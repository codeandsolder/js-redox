//! Publish complete generated reports without truncating the previous snapshot.
use anyhow::{ensure, Context, Result};
use serde::{de::DeserializeOwned, Serialize};
use std::{
    fs::{self, File},
    io::{BufWriter, ErrorKind, Read, Write},
    path::{Path, PathBuf},
};

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

/// Decode project-owned JSON, retaining IO errors independently of parse failures.
pub(crate) fn read_json<T: DeserializeOwned>(path: &Path, label: &str) -> Result<T> {
    let mut file =
        open_regular(path).with_context(|| format!("failed to read {label} {}", path.display()))?;
    let mut text = String::new();
    file.read_to_string(&mut text)
        .with_context(|| format!("failed to read {label} {}", path.display()))?;
    serde_json::from_str(&text)
        .with_context(|| format!("failed to parse {label} {}", path.display()))
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

fn stage(
    path: &Path,
    write: impl FnOnce(&mut BufWriter<&mut File>) -> Result<()>,
) -> Result<StagedReport> {
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
    {
        let mut writer = BufWriter::new(pending.as_file_mut());
        write(&mut writer).with_context(|| format!("encoding {}", path.display()))?;
        writer
            .flush()
            .with_context(|| format!("flushing {}", path.display()))?;
    }
    if let Some(permissions) = permissions {
        pending.as_file().set_permissions(permissions)?;
    }
    Ok(StagedReport {
        pending: pending.into_temp_path(),
        destination: path.to_owned(),
    })
}

/// Serialize directly into a buffered staging file.
pub(crate) fn stage_json(path: &Path, value: &impl Serialize) -> Result<StagedReport> {
    stage(path, |writer| {
        serde_json::to_writer_pretty(&mut *writer, value)?;
        writer.write_all(b"\n")?;
        Ok(())
    })
}

pub(crate) fn write_json(path: &Path, value: &impl Serialize) -> Result<()> {
    stage_json(path, value)?.publish()
}

fn stage_bytes(path: &Path, value: &[u8]) -> Result<StagedReport> {
    stage(path, |writer| {
        writer.write_all(value)?;
        Ok(())
    })
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
