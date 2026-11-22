//! Allocate distinct archive paths without clobbering previously staged bodies.
use super::resource::insert_suffix;
use crate::{capture_project::validate_project_relative_path, sha256_hex};
use anyhow::{Context, Result};
use std::{
    collections::HashMap,
    fs::{self, File},
    io::{ErrorKind, Write},
    path::Path,
};
use work_budget::WorkBudget;

#[derive(Default)]
struct FileVersions {
    by_digest: HashMap<String, String>,
    // Number of the next candidate; zero denotes the original filename.
    next: usize,
}

pub(super) struct StoredResource {
    pub(super) path: String,
    pub(super) sha256: String,
    pub(super) reused: bool,
}

/// Owns the filesystem namespace of a single private import staging directory.
pub(super) struct ResourceStore<'a> {
    root: &'a Path,
    budget: &'a WorkBudget,
    directories: HashMap<String, String>,
    files: HashMap<String, FileVersions>,
}

impl<'a> ResourceStore<'a> {
    pub(super) fn new(root: &'a Path, budget: &'a WorkBudget) -> Self {
        Self {
            root,
            budget,
            directories: HashMap::new(),
            files: HashMap::new(),
        }
    }

    fn directory(&mut self, logical_path: &str) -> Result<String> {
        let mut logical = String::new();
        let mut physical = String::new();
        for component in logical_path.split('/') {
            self.budget.consume(1)?;
            if !logical.is_empty() {
                logical.push('/');
            }
            logical.push_str(component);
            if let Some(previous) = self.directories.get(&logical) {
                physical.clone_from(previous);
                continue;
            }
            if !physical.is_empty() {
                physical.push('/');
            }
            let base = format!("{physical}{component}");
            // create_dir provides the real filesystem's collision semantics,
            // including case-insensitive names and an existing file ancestor.
            let mut version = 1usize;
            loop {
                self.budget.consume(1)?;
                let candidate = if version == 1 {
                    base.clone()
                } else {
                    format!("{base}~d{version}")
                };
                match fs::create_dir(self.root.join(&candidate)) {
                    Ok(()) => {
                        self.directories.insert(logical.clone(), candidate.clone());
                        physical = candidate;
                        break;
                    }
                    Err(error) if error.kind() == ErrorKind::AlreadyExists => {
                        version = version
                            .checked_add(1)
                            .context("archive directory suffix overflow")?;
                    }
                    Err(error) => {
                        return Err(error)
                            .with_context(|| format!("creating archive directory {candidate}"))
                    }
                }
            }
        }
        Ok(physical)
    }

    pub(super) fn write(&mut self, desired: &str, bytes: &[u8]) -> Result<StoredResource> {
        self.budget.consume(1)?;
        validate_project_relative_path(desired, "archive resource path")?;
        let (parent, name) = desired
            .rsplit_once('/')
            .context("archive resource has no parent")?;
        let digest = sha256_hex(bytes);
        if let Some(path) = self
            .files
            .get(desired)
            .and_then(|versions| versions.by_digest.get(&digest))
        {
            return Ok(StoredResource {
                path: path.clone(),
                sha256: digest,
                reused: true,
            });
        }
        let parent = self.directory(parent)?;
        let base = format!("{parent}/{name}");
        let versions = self.files.entry(desired.to_owned()).or_default();
        loop {
            self.budget.consume(1)?;
            let candidate = if versions.next == 0 {
                versions.next = 2;
                base.clone()
            } else {
                let version = versions.next;
                versions.next = version
                    .checked_add(1)
                    .context("archive file suffix overflow")?;
                insert_suffix(&base, &format!("~v{version}"))
            };
            // Never truncate an existing path, even if it was allocated by a
            // different logical name or aliases it on this filesystem.
            match File::create_new(self.root.join(&candidate)) {
                Ok(mut file) => {
                    file.write_all(bytes)
                        .with_context(|| format!("writing archive resource {candidate}"))?;
                    versions.by_digest.insert(digest.clone(), candidate.clone());
                    return Ok(StoredResource {
                        path: candidate,
                        sha256: digest,
                        reused: false,
                    });
                }
                Err(error)
                    if error.kind() == ErrorKind::AlreadyExists
                        || error.kind() == ErrorKind::IsADirectory => {}
                Err(error) => {
                    return Err(error)
                        .with_context(|| format!("creating archive resource {candidate}"))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn file_and_directory_collisions_preserve_both_bodies_in_either_order() -> Result<()> {
        for child_first in [false, true] {
            let root = tempfile::tempdir()?;
            let budget = WorkBudget::unlimited("archive fixture");
            let mut store = ResourceStore::new(root.path(), &budget);
            let mut resources = [
                ("resources/assets.js", b"parent".as_slice()),
                ("resources/assets.js/child.txt", b"child".as_slice()),
            ];
            if child_first {
                resources.reverse();
            }
            for (name, bytes) in resources {
                let stored = store.write(name, bytes)?;
                assert_eq!(fs::read(root.path().join(&stored.path))?, bytes);
                assert_eq!(stored.sha256, sha256_hex(bytes));
                assert!(!stored.reused);
            }
            for (name, bytes) in resources {
                let stored = store.write(name, bytes)?;
                assert!(stored.reused);
                assert_eq!(fs::read(root.path().join(stored.path))?, bytes);
            }
        }
        Ok(())
    }

    #[test]
    fn distinct_versions_use_monotonic_candidates_and_reuse_first_exact_body() -> Result<()> {
        let root = tempfile::tempdir()?;
        let budget = WorkBudget::new("linear allocation", work_budget::BudgetLimits::work(400));
        let mut store = ResourceStore::new(root.path(), &budget);
        // Also occupy a real filename that looks like a generated version.
        let existing = store.write("resources/data~v2.json", b"independent")?;
        for index in 0..100 {
            let stored = store.write("resources/data.json", index.to_string().as_bytes())?;
            assert_eq!(
                fs::read_to_string(root.path().join(stored.path))?,
                index.to_string()
            );
        }
        let first = store.write("resources/data.json", b"0")?;
        assert!(first.reused);
        assert_eq!(first.path, "resources/data.json");
        assert_eq!(fs::read(root.path().join(existing.path))?, b"independent");
        Ok(())
    }

    #[test]
    fn logical_directory_alias_cannot_claim_an_allocated_directory() -> Result<()> {
        let root = tempfile::tempdir()?;
        let budget = WorkBudget::unlimited("directory fixture");
        let mut store = ResourceStore::new(root.path(), &budget);
        let first = store.write("resources/a", b"file")?;
        let child = store.write("resources/a/b.txt", b"nested")?;
        let literal = store.write("resources/a~d2/b.txt", b"literal")?;
        assert_ne!(child.path, literal.path);
        for (stored, bytes) in [
            (first, b"file".as_slice()),
            (child, b"nested"),
            (literal, b"literal"),
        ] {
            assert_eq!(fs::read(root.path().join(stored.path))?, bytes);
        }
        assert!(store.write("resources/../outside", b"bad").is_err());
        Ok(())
    }
}
