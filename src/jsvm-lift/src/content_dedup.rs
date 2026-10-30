use anyhow::{Context, Result};
use sha2::{Digest, Sha256};
use std::{fs, io::Read, path::Path};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Materialization {
    HardLink,
    Copy,
}

pub fn sha256_path(path: &Path) -> Result<String> {
    let mut file = fs::File::open(path).with_context(|| format!("opening {}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 1024 * 1024];
    loop {
        let count = file
            .read(&mut buffer)
            .with_context(|| format!("reading {}", path.display()))?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

#[must_use]
pub fn default_jobs(cap: usize) -> usize {
    std::thread::available_parallelism()
        .map_or(1, usize::from)
        .clamp(1, cap.max(1))
}

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
    use super::default_jobs;

    #[test]
    fn default_jobs_is_never_zero_and_respects_cap() {
        assert_eq!(default_jobs(0), 1);
        assert!((1..=3).contains(&default_jobs(3)));
    }
}
