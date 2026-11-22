use anyhow::{Context, Result};
use sha2::{Digest, Sha256};
use std::{fs, io::Read, path::Path};

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

/// Compute a lowercase hexadecimal SHA-256 digest of a file.
///
/// # Errors
///
/// Fails when the source file cannot be opened or read.
pub fn sha256_path(path: &Path) -> Result<String> {
    let mut file = fs::File::open(path).with_context(|| format!("opening {}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0_u8; 1024 * 1024];
    loop {
        let count = file
            .read(&mut buffer)
            .with_context(|| format!("reading {}", path.display()))?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(encode_digest(&hasher.finalize()))
}

#[must_use]
pub fn default_jobs(cap: usize) -> usize {
    std::thread::available_parallelism()
        .map_or(1, usize::from)
        .clamp(1, cap.max(1))
}

/// Materialize a source file using a hard link when possible, otherwise copy it.
///
/// # Errors
///
/// Fails when destination parent directories cannot be created, an existing destination cannot be inspected or removed, or the fallback file copy fails.
pub fn link_or_copy(source: &Path, dest: &Path) -> Result<Materialization> {
    if let Some(parent) = dest.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    match fs::symlink_metadata(dest) {
        Ok(_) => {
            fs::remove_file(dest).with_context(|| format!("removing {}", dest.display()))?;
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(error).with_context(|| format!("inspecting {}", dest.display()));
        }
    }
    match fs::hard_link(source, dest) {
        Ok(()) => Ok(Materialization::HardLink),
        Err(_) => {
            fs::copy(source, dest)
                .with_context(|| format!("copying {} to {}", source.display(), dest.display()))?;
            Ok(Materialization::Copy)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{default_jobs, is_canonical_sha256, sha256_hex, sha256_path};
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
    fn default_jobs_is_never_zero_and_respects_cap() {
        assert_eq!(default_jobs(0), 1);
        assert!((1..=3).contains(&default_jobs(3)));
    }
}
