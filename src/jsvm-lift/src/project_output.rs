//! Prepare imported projects separately from the destination being replaced.
use crate::capture_project::{read_manifest, MANIFEST_NAME};
use anyhow::{bail, ensure, Context, Result};
use std::{
    fs,
    io::ErrorKind,
    path::{Path, PathBuf},
};

/// Resolve existing ancestor directories, keeping a not-yet-created suffix.
/// Never create directories until the destination has passed overlap checks.
fn resolve_destination(path: &Path) -> Result<PathBuf> {
    let absolute = std::path::absolute(path)?;
    let name = absolute
        .file_name()
        .context("output must name a project directory")?;
    let mut parent = absolute
        .parent()
        .context("output has no parent directory")?;
    let mut missing = Vec::new();
    let mut resolved = loop {
        match parent.canonicalize() {
            Ok(resolved) => {
                ensure!(
                    resolved.is_dir(),
                    "output ancestor is not a directory: {}",
                    parent.display()
                );
                break resolved;
            }
            Err(error) if error.kind() == ErrorKind::NotFound => {
                // A dangling link is not a new directory.
                match fs::symlink_metadata(parent) {
                    Ok(_) => bail!("cannot resolve output ancestor {}", parent.display()),
                    Err(error) if error.kind() == ErrorKind::NotFound => {}
                    Err(error) => {
                        return Err(error)
                            .with_context(|| format!("inspecting {}", parent.display()))
                    }
                }
                missing.push(parent.file_name().context("unresolvable output parent")?);
                parent = parent.parent().context("unresolvable output ancestor")?;
            }
            Err(error) => {
                return Err(error).with_context(|| format!("resolving {}", parent.display()))
            }
        }
    };
    resolved.extend(missing.into_iter().rev());
    resolved.push(name);
    Ok(resolved)
}

fn validate_project_directory(path: &Path) -> Result<()> {
    let manifest = path.join(MANIFEST_NAME);
    ensure!(
        fs::symlink_metadata(&manifest)?.is_file(),
        "capture manifest is not a regular file: {}",
        manifest.display()
    );
    read_manifest(&manifest)?;
    Ok(())
}

fn existing_destination(path: &Path, overwrite: bool) -> Result<bool> {
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(error).with_context(|| format!("inspecting {}", path.display())),
    };
    ensure!(
        metadata.is_dir(),
        "refusing non-directory or symlink output: {}",
        path.display()
    );
    ensure!(
        overwrite,
        "output directory already exists: {} (use --overwrite)",
        path.display()
    );
    if fs::read_dir(path)?.next().transpose()?.is_some() {
        validate_project_directory(path).with_context(|| {
            format!("refusing to replace non-project output: {}", path.display())
        })?;
    }
    Ok(true)
}

/// Single-writer directory publication. Keep existing projects intact during
/// import, and retain the backup if a failed rename cannot be rolled back.
pub(crate) struct ProjectOutput {
    directory: tempfile::TempDir,
    staged: PathBuf,
    destination: PathBuf,
    overwrite: bool,
    existed: bool,
}

impl ProjectOutput {
    /// Input paths must identify existing files or directory trees.
    pub(crate) fn new(destination: &Path, overwrite: bool, inputs: &[&Path]) -> Result<Self> {
        let destination = resolve_destination(destination)?;
        for input in inputs {
            let input = input
                .canonicalize()
                .with_context(|| format!("resolving capture input {}", input.display()))?;
            ensure!(
                !input.starts_with(&destination) && !destination.starts_with(&input),
                "project output {} overlaps capture input {}",
                destination.display(),
                input.display()
            );
        }
        let existed = existing_destination(&destination, overwrite)?;
        let parent = destination
            .parent()
            .context("output has no parent directory")?;
        fs::create_dir_all(parent)?;
        let mut builder = tempfile::Builder::new();
        builder.prefix(".capture-project-");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            builder.permissions(fs::Permissions::from_mode(0o700));
        }
        let directory = builder.tempdir_in(parent)?;
        let staged = directory.path().join("project");
        fs::create_dir(&staged)?;
        Ok(Self {
            directory,
            staged,
            destination,
            overwrite,
            existed,
        })
    }

    pub(crate) fn path(&self) -> &Path {
        &self.staged
    }

    /// Publish the validated import. Prefer an atomic exchange where the
    /// filesystem supports it; neither path promises crash durability.
    pub(crate) fn publish(self) -> Result<()> {
        validate_project_directory(&self.staged).context("validating staged capture project")?;
        ensure!(
            existing_destination(&self.destination, self.overwrite)? == self.existed,
            "project destination changed during import: {}",
            self.destination.display()
        );
        #[cfg(any(target_os = "linux", target_os = "android", target_vendor = "apple"))]
        if self.try_atomic_publish()? {
            return self.finish();
        }
        self.publish_portable()
    }

    /// Exchange directories atomically, or use an exclusive rename for new
    /// projects. Fall back only when the platform/filesystem lacks the flags.
    #[cfg(any(target_os = "linux", target_os = "android", target_vendor = "apple"))]
    fn try_atomic_publish(&self) -> Result<bool> {
        use rustix::{
            fs::{renameat_with, RenameFlags, CWD},
            io::Errno,
        };
        let flags = if self.existed {
            RenameFlags::EXCHANGE
        } else {
            RenameFlags::NOREPLACE
        };
        match renameat_with(CWD, &self.staged, CWD, &self.destination, flags) {
            Ok(()) => Ok(true),
            Err(Errno::NOSYS | Errno::NOTSUP | Errno::INVAL) => Ok(false),
            Err(error) => Err(std::io::Error::from(error))
                .with_context(|| format!("publishing {}", self.destination.display())),
        }
    }

    // A single-writer fallback for other filesystems: preserve the old
    // directory until staging succeeds and attempt rollback on rename failure.
    fn publish_portable(self) -> Result<()> {
        let previous = self.directory.path().join("previous");
        if self.existed {
            fs::rename(&self.destination, &previous).with_context(|| {
                format!("moving previous project {}", self.destination.display())
            })?;
        }
        if let Err(error) = fs::rename(&self.staged, &self.destination) {
            let rollback = if self.existed {
                fs::rename(&previous, &self.destination)
            } else {
                Ok(())
            };
            if let Err(rollback) = rollback {
                let retained = self.directory.keep();
                bail!("publishing {} failed ({error}); restoring old project failed ({rollback}); recover previous project at {}",self.destination.display(),retained.join("previous").display());
            }
            return Err(error)
                .with_context(|| format!("publishing {}", self.destination.display()));
        }
        self.finish()
    }

    fn finish(self) -> Result<()> {
        self.directory.close().with_context(|| {
            format!(
                "project {} published but staging cleanup failed",
                self.destination.display()
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::capture_project::{validate_manifest_value, write_manifest};
    use serde_json::json;

    fn manifest(path: &Path, input: &str) -> Result<()> {
        let document = json!({"schema":"capture-project/v1","source":{"kind":"test","input":input,"salvaged":false},"pages":[],"resources":[],"inline_scripts":[],"counts":{}});
        write_manifest(
            &path.join(MANIFEST_NAME),
            &validate_manifest_value(&document, "fixture")?,
        )
    }

    #[test]
    fn invalid_staging_and_abandoned_imports_leave_the_previous_project() -> Result<()> {
        let root = tempfile::tempdir()?;
        let output = root.path().join("output");
        manifest(&output, "old capture")?;
        let before = fs::read(output.join(MANIFEST_NAME))?;
        fs::write(output.join("old.txt"), "old data")?;
        {
            let pending = ProjectOutput::new(&output, true, &[])?;
            fs::write(pending.path().join("partial"), "incomplete")?;
        }
        assert_eq!(fs::read_dir(root.path())?.count(), 1);
        let pending = ProjectOutput::new(&output, true, &[])?;
        assert!(pending.publish().is_err());
        assert_eq!(fs::read(output.join(MANIFEST_NAME))?, before);
        assert_eq!(fs::read_to_string(output.join("old.txt"))?, "old data");
        let pending = ProjectOutput::new(&output, true, &[])?;
        manifest(pending.path(), "new capture")?;
        pending.publish()?;
        assert_eq!(
            read_manifest(&output.join(MANIFEST_NAME))?.source.input,
            "new capture"
        );
        assert!(!output.join("old.txt").exists());
        assert_eq!(fs::read_dir(root.path())?.count(), 1);
        Ok(())
    }

    #[test]
    fn portable_publication_replaces_only_completed_project() -> Result<()> {
        let root = tempfile::tempdir()?;
        let output = root.path().join("output");
        manifest(&output, "old")?;
        let pending = ProjectOutput::new(&output, true, &[])?;
        manifest(pending.path(), "new")?;
        pending.publish_portable()?;
        assert_eq!(
            read_manifest(&output.join(MANIFEST_NAME))?.source.input,
            "new"
        );
        assert_eq!(fs::read_dir(root.path())?.count(), 1);
        Ok(())
    }

    #[cfg(any(target_os = "linux", target_os = "android", target_vendor = "apple"))]
    #[test]
    fn native_exchange_retains_old_project_in_staging_until_cleanup() -> Result<()> {
        let root = tempfile::tempdir()?;
        let output = root.path().join("output");
        manifest(&output, "old")?;
        let pending = ProjectOutput::new(&output, true, &[])?;
        manifest(pending.path(), "new")?;
        if pending.try_atomic_publish()? {
            assert_eq!(
                read_manifest(&output.join(MANIFEST_NAME))?.source.input,
                "new"
            );
            assert_eq!(
                read_manifest(&pending.path().join(MANIFEST_NAME))?
                    .source
                    .input,
                "old"
            );
            pending.finish()?;
            assert_eq!(fs::read_dir(root.path())?.count(), 1);
        } else {
            assert_eq!(
                read_manifest(&output.join(MANIFEST_NAME))?.source.input,
                "old"
            );
            pending.publish_portable()?;
            assert_eq!(
                read_manifest(&output.join(MANIFEST_NAME))?.source.input,
                "new"
            );
        }
        Ok(())
    }

    #[test]
    fn rejects_unowned_destinations_and_input_overlap_without_mutating_inputs() -> Result<()> {
        let root = tempfile::tempdir()?;
        let output = root.path().join("output");
        fs::create_dir(&output)?;
        fs::write(output.join(MANIFEST_NAME), "not a project")?;
        assert!(ProjectOutput::new(&output, true, &[]).is_err());
        assert_eq!(
            fs::read_to_string(output.join(MANIFEST_NAME))?,
            "not a project"
        );
        manifest(&output, "old")?;
        assert!(ProjectOutput::new(&output, false, &[]).is_err());
        let input = output.join("input.har");
        fs::write(&input, "capture")?;
        assert!(ProjectOutput::new(&output, true, &[&input]).is_err());
        assert_eq!(fs::read_to_string(input)?, "capture");
        let assets = root.path().join("assets");
        fs::create_dir(&assets)?;
        assert!(ProjectOutput::new(&assets.join("new/project"), true, &[&assets]).is_err());
        assert!(!assets.join("new").exists());
        let nested = root.path().join("nested/new/project");
        let pending = ProjectOutput::new(&nested, false, &[])?;
        manifest(pending.path(), "new")?;
        pending.publish()?;
        assert!(nested.join(MANIFEST_NAME).is_file());
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn output_and_manifest_symlinks_are_not_project_ownership() -> Result<()> {
        use std::os::unix::fs::symlink;
        let root = tempfile::tempdir()?;
        let original = root.path().join("original");
        manifest(&original, "old")?;
        let alias = root.path().join("alias");
        symlink(&original, &alias)?;
        assert!(ProjectOutput::new(&alias, true, &[]).is_err());
        let unrelated = root.path().join("unrelated");
        fs::create_dir(&unrelated)?;
        symlink(original.join(MANIFEST_NAME), unrelated.join(MANIFEST_NAME))?;
        assert!(ProjectOutput::new(&unrelated, true, &[]).is_err());
        // Normalize a symlinked parent before comparing input directory trees.
        assert!(ProjectOutput::new(&alias.join("missing/child"), true, &[&original]).is_err());
        assert!(!original.join("missing").exists());
        Ok(())
    }
}
