use anyhow::{Context, Result};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{BufRead, BufReader, ErrorKind, Read},
    path::Path,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Materialization {
    HardLink,
    Copy,
}

/// Return the SHA-256 digest of `bytes` as lowercase hexadecimal.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    encode_digest(&Sha256::digest(bytes))
}

fn encode_digest(digest: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(digest.len() * 2);
    for &byte in digest {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}

/// Content-addressed paths use exactly the spelling produced by the encoder.
pub(crate) fn is_canonical_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
}

/// Identity and length of precisely the bytes consumed by a stream operation.
pub(crate) struct FileDigest {
    pub(crate) sha256: String,
    pub(crate) bytes: u64,
}

pub(crate) fn digest_stream(
    reader: impl Read,
    mut visit: impl FnMut(&[u8], u64) -> Result<()>,
) -> Result<FileDigest> {
    // fill_buf lends the same storage to the digest and consumer and avoids
    // initializing a megabyte of array contents for every small file.
    let mut reader = BufReader::with_capacity(1024 * 1024, reader);
    let mut hasher = Sha256::new();
    let mut bytes = 0u64;
    loop {
        let chunk = match reader.fill_buf() {
            Ok(chunk) => chunk,
            Err(error) if error.kind() == ErrorKind::Interrupted => continue,
            Err(error) => return Err(error.into()),
        };
        if chunk.is_empty() {
            break;
        }
        let count = chunk.len();
        bytes = bytes
            .checked_add(u64::try_from(count)?)
            .context("file size overflow")?;
        visit(chunk, bytes)?;
        hasher.update(chunk);
        reader.consume(count);
    }
    Ok(FileDigest {
        sha256: encode_digest(&hasher.finalize()),
        bytes,
    })
}

/// Compute a lowercase hexadecimal SHA-256 digest of a file.
///
/// # Errors
/// Fails when the source file cannot be opened or read.
pub fn sha256_path(path: &Path) -> Result<String> {
    let file = fs::File::open(path).with_context(|| format!("opening {}", path.display()))?;
    Ok(digest_stream(file, |_, _| Ok(()))
        .with_context(|| format!("reading {}", path.display()))?
        .sha256)
}

#[must_use]
pub fn default_jobs(cap: usize) -> usize {
    std::thread::available_parallelism()
        .map_or(1, usize::from)
        .clamp(1, cap.max(1))
}

/// Materialize a regular source file by hardlink if possible, otherwise copy.
/// The old destination remains intact until its replacement is complete.
/// # Errors
/// Fails when either endpoint is invalid, staging fails, or the completed file
/// cannot be published.
pub fn link_or_copy(source: &Path, dest: &Path) -> Result<Materialization> {
    anyhow::ensure!(
        fs::symlink_metadata(source)
            .with_context(|| format!("inspecting {}", source.display()))?
            .is_file(),
        "materialization source is not a regular file: {}",
        source.display()
    );
    let (parent, _) = crate::report_file::prepare_destination(dest)?;
    // Private same-filesystem staging directory permits both hardlink and
    // copy without creating a window where dest is absent. Its RAII cleanup
    // also handles rename's same-inode no-op (including source == dest).
    let mut builder = tempfile::Builder::new();
    builder.prefix(".materialize-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        builder.permissions(fs::Permissions::from_mode(0o700));
    }
    let pending = builder
        .tempdir_in(parent)
        .with_context(|| format!("staging {}", dest.display()))?;
    let file = pending.path().join("content");
    let materialization = if fs::hard_link(source, &file).is_ok() {
        Materialization::HardLink
    } else {
        fs::copy(source, &file)
            .with_context(|| format!("copying {} to stage {}", source.display(), dest.display()))?;
        Materialization::Copy
    };
    fs::rename(&file, dest).with_context(|| format!("publishing {}", dest.display()))?;
    Ok(materialization)
}

#[cfg(test)]
mod tests {
    use super::{default_jobs, is_canonical_sha256, link_or_copy, sha256_hex, sha256_path};
    use anyhow::Result;
    use std::fs;

    #[test]
    fn sha256_path_streams_empty_and_multi_chunk_files() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("source.bin");
        for size in [0, 1, 1024 * 1024, 2 * 1024 * 1024 + 37] {
            let bytes = vec![0x5a_u8; size];
            fs::write(&path, &bytes)?;
            assert_eq!(sha256_path(&path)?, crate::sha256_hex(&bytes));
        }
        Ok(())
    }

    #[test]
    fn canonical_digest_matches_standard_vector_and_rejects_other_spellings() {
        let digest = sha256_hex(b"abc");
        assert_eq!(
            digest,
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert!(is_canonical_sha256(&digest));
        for invalid in [
            digest.to_uppercase(),
            digest[..63].to_owned(),
            format!("{digest}0"),
            format!("../{}", &digest[3..]),
            format!("{}g", &digest[..63]),
            "é".repeat(32),
        ] {
            assert!(!is_canonical_sha256(&invalid), "accepted {invalid:?}");
        }
    }

    #[test]
    fn materialization_preserves_destination_on_failure_and_same_inode() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let source = dir.path().join("source");
        let dest = dir.path().join("destination");
        let snapshot = dir.path().join("previous");
        fs::write(&source, "next")?;
        fs::write(&dest, "previous")?;
        fs::hard_link(&dest, &snapshot)?;
        assert!(link_or_copy(&dir.path().join("missing"), &dest).is_err());
        assert!(link_or_copy(dir.path(), &dest).is_err());
        assert_eq!(fs::read_to_string(&dest)?, "previous");
        link_or_copy(&source, &dest)?;
        assert_eq!(fs::read_to_string(&dest)?, "next");
        assert_eq!(fs::read_to_string(&snapshot)?, "previous");
        link_or_copy(&source, &dest)?;
        link_or_copy(&source, &source)?;
        assert_eq!(fs::read_to_string(&source)?, "next");
        assert_eq!(fs::read_dir(dir.path())?.count(), 3);
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn materialization_rejects_symlinks_without_mutating_targets() -> Result<()> {
        use std::os::unix::fs::symlink;
        let dir = tempfile::tempdir()?;
        let source = dir.path().join("source");
        let dest = dir.path().join("destination");
        let alias = dir.path().join("alias");
        fs::write(&source, "source")?;
        fs::write(&dest, "destination")?;
        symlink(&source, &alias)?;
        assert!(link_or_copy(&alias, &dest).is_err());
        assert!(link_or_copy(&dest, &alias).is_err());
        assert_eq!(fs::read_to_string(&dest)?, "destination");
        assert_eq!(fs::read_to_string(&source)?, "source");
        assert!(fs::symlink_metadata(alias)?.is_symlink());
        Ok(())
    }

    #[test]
    fn default_jobs_is_never_zero_and_respects_cap() {
        assert_eq!(default_jobs(0), 1);
        assert!((1..=3).contains(&default_jobs(3)));
    }
}
