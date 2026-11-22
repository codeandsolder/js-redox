//! Publish complete generated reports without truncating the previous snapshot.
use crate::content_dedup::{digest_stream, FileDigest};
use anyhow::{ensure, Context, Result};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fs::{self, File},
    io::{BufWriter, ErrorKind, Read, Write},
    path::{Path, PathBuf},
};
use work_budget::WorkBudget;

/// A completely encoded report whose final name is still untouched.
/// Dropping it abandons the staging file, including on a later render failure.
pub(crate) struct StagedReport {
    pending: tempfile::TempPath,
    destination: PathBuf,
}

impl StagedReport {
    pub(crate) fn publish(self) -> Result<()> {
        self.pending
            .persist(&self.destination)
            .with_context(|| format!("publishing {}", self.destination.display()))
    }
}

/// Open an existing regular file without following a final-component symlink.
fn open_regular(path: &Path) -> Result<File> {
    ensure!(
        fs::symlink_metadata(path)?.is_file(),
        "not a regular file: {}",
        path.display()
    );
    // Native nonblocking, no-follow open closes the gap between checking
    // the path and opening it on the supported Unix platforms.
    #[cfg(any(target_os = "linux", target_os = "android", target_vendor = "apple"))]
    let file = File::from(
        rustix::fs::open(
            path,
            rustix::fs::OFlags::RDONLY
                | rustix::fs::OFlags::CLOEXEC
                | rustix::fs::OFlags::NOFOLLOW
                | rustix::fs::OFlags::NONBLOCK,
            rustix::fs::Mode::empty(),
        )
        .map_err(std::io::Error::from)?,
    );
    #[cfg(not(any(target_os = "linux", target_os = "android", target_vendor = "apple")))]
    let file = File::open(path)?;
    ensure!(
        file.metadata()?.is_file(),
        "not a regular file: {}",
        path.display()
    );
    Ok(file)
}

/// Read a single regular-file snapshot without following final-component links.
pub(crate) fn read_bytes(path: &Path) -> Result<Vec<u8>> {
    let mut file = open_regular(path).with_context(|| format!("opening {}", path.display()))?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)
        .with_context(|| format!("reading {}", path.display()))?;
    Ok(data)
}

fn decode_json<T: DeserializeOwned>(mut reader: impl Read, path: &Path, label: &str) -> Result<T> {
    let mut text = String::new();
    reader
        .read_to_string(&mut text)
        .with_context(|| format!("failed to read {label} {}", path.display()))?;
    serde_json::from_str(&text)
        .with_context(|| format!("failed to parse {label} {}", path.display()))
}

/// Decode mandatory project-owned JSON.
pub(crate) fn read_json<T: DeserializeOwned>(path: &Path, label: &str) -> Result<T> {
    let file =
        open_regular(path).with_context(|| format!("failed to open {label} {}", path.display()))?;
    decode_json(file, path, label)
}

/// Only an absent file at open time is an optional result. An opened file
/// whose subsequent read or parse fails is never an absent artifact.
pub(crate) fn read_optional_json<T: DeserializeOwned>(
    path: &Path,
    label: &str,
) -> Result<Option<T>> {
    match open_regular(path) {
        Ok(file) => decode_json(file, path, label).map(Some),
        Err(error)
            if error
                .downcast_ref::<std::io::Error>()
                .is_some_and(|cause| cause.kind() == ErrorKind::NotFound) =>
        {
            Ok(None)
        }
        Err(error) => {
            Err(error).with_context(|| format!("failed to open {label} {}", path.display()))
        }
    }
}

/// Prepare a regular-file destination without removing or modifying it.
pub(crate) fn prepare_destination(path: &Path) -> Result<(&Path, Option<fs::Permissions>)> {
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    let permissions = match fs::symlink_metadata(path) {
        Ok(metadata) => {
            ensure!(
                metadata.is_file(),
                "publication destination is not a regular file: {}",
                path.display()
            );
            Some(metadata.permissions())
        }
        Err(error) if error.kind() == ErrorKind::NotFound => None,
        Err(error) => return Err(error).with_context(|| format!("checking {}", path.display())),
    };
    Ok((parent, permissions))
}

fn stage<T>(
    path: &Path,
    write: impl FnOnce(&mut BufWriter<&mut File>) -> Result<T>,
) -> Result<(StagedReport, T)> {
    let (parent, permissions) = prepare_destination(path)?;
    let mut builder = tempfile::Builder::new();
    builder.prefix(".report-");
    // Match the permissions of a newly created regular file (subject to umask).
    #[cfg(unix)]
    if permissions.is_none() {
        use std::os::unix::fs::PermissionsExt;
        builder.permissions(fs::Permissions::from_mode(0o666));
    }
    let mut pending = builder
        .tempfile_in(parent)
        .with_context(|| format!("staging {}", path.display()))?;
    let value = {
        let mut writer = BufWriter::new(pending.as_file_mut());
        let value = write(&mut writer).with_context(|| format!("encoding {}", path.display()))?;
        writer
            .flush()
            .with_context(|| format!("flushing {}", path.display()))?;
        value
    };
    if let Some(permissions) = permissions {
        pending.as_file().set_permissions(permissions)?;
    }
    Ok((
        StagedReport {
            pending: pending.into_temp_path(),
            destination: path.to_owned(),
        },
        value,
    ))
}

/// Serialize directly into a buffered staging file.
pub(crate) fn stage_json(path: &Path, value: &impl Serialize) -> Result<StagedReport> {
    let (report, ()) = stage(path, |writer| {
        serde_json::to_writer_pretty(&mut *writer, value)?;
        writer.write_all(b"\n")?;
        Ok(())
    })?;
    Ok(report)
}

pub(crate) fn write_json(path: &Path, value: &impl Serialize) -> Result<()> {
    stage_json(path, value)?.publish()
}

fn stage_bytes(path: &Path, value: &[u8]) -> Result<StagedReport> {
    let (report, ()) = stage(path, |writer| {
        writer.write_all(value)?;
        Ok(())
    })?;
    Ok(report)
}

/// Copy a regular input into a complete independent file while computing
/// the exact archived length and digest, with bounded streaming storage.
pub(crate) fn copy_snapshot(
    source: &Path,
    destination: &Path,
    budget: &WorkBudget,
) -> Result<FileDigest> {
    let reader = open_regular(source).with_context(|| format!("opening {}", source.display()))?;
    let mut charged = reader.metadata()?.len().div_ceil(1024);
    budget.consume(charged)?;
    let (report, identity) = stage(destination, |writer| {
        digest_stream(reader, |chunk, total| {
            // Account for growth without charging differently for short reads.
            let units = total.div_ceil(1024);
            budget.consume(units.saturating_sub(charged))?;
            charged = charged.max(units);
            writer.write_all(chunk)?;
            Ok(())
        })
    })?;
    budget.checkpoint()?;
    report.publish()?;
    Ok(identity)
}

pub(crate) fn write_bytes(path: &Path, value: &[u8]) -> Result<()> {
    stage_bytes(path, value)?.publish()
}

pub(crate) fn stage_text(path: &Path, value: &str) -> Result<StagedReport> {
    stage_bytes(path, value.as_bytes())
}

pub(crate) fn write_text(path: &Path, value: &str) -> Result<()> {
    stage_text(path, value)?.publish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::ser::{Error, SerializeSeq};

    struct FailingReport;

    impl Serialize for FailingReport {
        fn serialize<S: serde::Serializer>(
            &self,
            serializer: S,
        ) -> std::result::Result<S::Ok, S::Error> {
            let mut sequence = serializer.serialize_seq(Some(2))?;
            sequence.serialize_element(&"x".repeat(16_384))?;
            Err(S::Error::custom("fixture serialization failure"))
        }
    }

    #[test]
    fn streamed_snapshot_is_independent_and_budget_failure_preserves_previous_output() -> Result<()>
    {
        let root = tempfile::tempdir()?;
        let source = root.path().join("source.bin");
        let destination = root.path().join("snapshot.bin");
        let bytes = vec![0x5a; 2 * 1024 * 1024 + 37];
        fs::write(&source, &bytes)?;
        fs::write(&destination, "previous")?;
        let exhausted = WorkBudget::new("copy limit", work_budget::BudgetLimits::work(2048));
        assert!(copy_snapshot(&source, &destination, &exhausted).is_err());
        assert_eq!(fs::read(&destination)?, b"previous");
        let identity = copy_snapshot(
            &source,
            &destination,
            &WorkBudget::unlimited("copy fixture"),
        )?;
        assert_eq!(identity.bytes, u64::try_from(bytes.len())?);
        assert_eq!(identity.sha256, crate::sha256_hex(&bytes));
        fs::write(&source, "changed")?;
        assert_eq!(fs::read(&destination)?, bytes);
        assert_eq!(fs::read_dir(root.path())?.count(), 2);
        Ok(())
    }

    #[test]
    fn missing_during_read_is_an_error_not_optional_absence() -> Result<()> {
        struct MissingDuringRead;
        impl Read for MissingDuringRead {
            fn read(&mut self, _buffer: &mut [u8]) -> std::io::Result<usize> {
                Err(std::io::Error::new(
                    ErrorKind::NotFound,
                    "fixture read failure",
                ))
            }
        }
        let error = decode_json::<serde_json::Value>(
            MissingDuringRead,
            Path::new("fixture.json"),
            "fixture",
        )
        .err()
        .context("post-open read unexpectedly succeeded")?;
        assert_eq!(
            error
                .downcast_ref::<std::io::Error>()
                .map(std::io::Error::kind),
            Some(ErrorKind::NotFound)
        );
        assert!(error.to_string().contains("failed to read"));
        Ok(())
    }

    #[test]
    fn interrupted_serialization_retains_old_report_without_staging_files() -> Result<()> {
        let directory = tempfile::tempdir()?;
        let path = directory.path().join("report.json");
        let previous = serde_json::json!({"snapshot":"previous"});
        write_json(&path, &previous)?;
        let before = fs::read(&path)?;
        assert!(write_json(&path, &FailingReport).is_err());
        assert_eq!(fs::read(&path)?, before);
        assert_eq!(fs::read_dir(directory.path())?.count(), 1);
        let replacement = serde_json::json!({"source":"a\n💡","number":42});
        write_json(&path, &replacement)?;
        assert_eq!(
            fs::read_to_string(&path)?,
            format!("{}\n", serde_json::to_string_pretty(&replacement)?)
        );
        Ok(())
    }

    #[test]
    fn replacing_a_report_does_not_modify_other_hardlinks() -> Result<()> {
        let directory = tempfile::tempdir()?;
        let destination = directory.path().join("report.md");
        let snapshot = directory.path().join("snapshot.md");
        write_text(&destination, "previous")?;
        fs::hard_link(&destination, &snapshot)?;
        write_text(&destination, "next")?;
        assert_eq!(fs::read_to_string(snapshot)?, "previous");
        assert_eq!(fs::read_to_string(destination)?, "next");
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn existing_permissions_are_preserved_and_symlinks_are_not_followed() -> Result<()> {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let directory = tempfile::tempdir()?;
        let destination = directory.path().join("report.md");
        let alias = directory.path().join("alias.md");
        write_text(&destination, "previous")?;
        fs::set_permissions(&destination, fs::Permissions::from_mode(0o640))?;
        write_text(&destination, "next")?;
        assert_eq!(
            fs::metadata(&destination)?.permissions().mode() & 0o777,
            0o640
        );
        symlink(&destination, &alias)?;
        assert!(write_text(&alias, "unwanted").is_err());
        assert_eq!(fs::read_to_string(destination)?, "next");
        Ok(())
    }
}
