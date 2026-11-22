//! A bounded, operation-local cache of exact captured source snapshots.
use crate::{sha256_hex, source_text::SourceLineIndex};
use anyhow::{ensure, Context, Result};
use std::{
    collections::{HashMap, VecDeque},
    fs,
    io::Read,
    mem::size_of,
    path::Path,
    rc::Rc,
};
use work_budget::WorkBudget;

/// A browsing operation may reference thousands of locations across many
/// bodies. Retain at most this amount of source/index storage, independent of
/// corpus size. A larger individual source is still supported, but not cached.
pub(super) const SOURCE_CACHE_BYTES: usize = 64 * 1024 * 1024;

pub(super) struct VerifiedSource {
    pub(super) text: String,
    pub(super) lines: SourceLineIndex,
}

impl VerifiedSource {
    pub(super) fn from_text(text: String) -> Self {
        Self {
            lines: SourceLineIndex::new(&text),
            text,
        }
    }

    fn retained_bytes(&self, sha: &str) -> usize {
        self.text
            .capacity()
            .saturating_add(self.lines.retained_bytes())
            .saturating_add(
                size_of::<Self>() + 2 * size_of::<String>() + size_of::<Rc<Self>>() + 2 * sha.len(),
            )
    }
}

/// Content-addressed files are immutable within a report operation. Cache the
/// already verified bytes, not the session/script claim which selected them.
/// FIFO eviction bounds retained payloads without changing report semantics.
pub(super) struct VerifiedSources<'a> {
    pub(super) project: &'a Path,
    pub(super) budget: &'a WorkBudget,
    entries: HashMap<String, Rc<VerifiedSource>>,
    arrival_order: VecDeque<String>,
    retained_bytes: usize,
    capacity: usize,
}

impl<'a> VerifiedSources<'a> {
    pub(super) fn new(project: &'a Path, budget: &'a WorkBudget, capacity: usize) -> Self {
        Self {
            project,
            budget,
            entries: HashMap::new(),
            arrival_order: VecDeque::new(),
            retained_bytes: 0,
            capacity,
        }
    }

    pub(super) fn load(&mut self, sha: &str) -> Result<Rc<VerifiedSource>> {
        self.budget.consume(1)?;
        ensure!(
            crate::content_dedup::is_canonical_sha256(sha),
            "invalid original runtime source digest"
        );
        if let Some(source) = self.entries.get(sha) {
            return Ok(Rc::clone(source));
        }
        let path = self
            .project
            .join(format!("resources/runtime-scripts/{sha}.js"));
        let mut file = fs::File::open(&path)
            .with_context(|| format!("opening original runtime source {}", path.display()))?;
        let metadata = file.metadata()?;
        ensure!(
            metadata.is_file(),
            "original runtime source is not a regular file: {}",
            path.display()
        );
        // Reserve the known byte-reading work before allocating the source.
        // If an external writer grew the file, account for the extra bytes too.
        let reserved = metadata.len().div_ceil(1024);
        self.budget.consume(reserved)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)
            .with_context(|| format!("reading original runtime source {}", path.display()))?;
        self.budget
            .consume(u64::try_from(bytes.len().div_ceil(1024))?.saturating_sub(reserved))?;
        ensure!(
            sha256_hex(&bytes) == sha,
            "captured runtime source hash mismatch: {sha}"
        );
        let text = String::from_utf8(bytes)
            .with_context(|| format!("original runtime source is not UTF-8: {sha}"))?;
        let source = Rc::new(VerifiedSource::from_text(text));
        self.budget.checkpoint()?;
        let weight = source.retained_bytes(sha);
        if weight > self.capacity {
            return Ok(source);
        }
        while self.retained_bytes > self.capacity - weight {
            let evicted = self
                .arrival_order
                .pop_front()
                .context("source cache queue accounting")?;
            let entry = self
                .entries
                .remove(&evicted)
                .context("source cache entry accounting")?;
            self.retained_bytes -= entry.retained_bytes(&evicted);
        }
        self.retained_bytes += weight;
        self.arrival_order.push_back(sha.to_owned());
        self.entries.insert(sha.to_owned(), Rc::clone(&source));
        Ok(source)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use work_budget::BudgetLimits;

    #[test]
    fn verified_source_cache_reuses_content_and_respects_work_limits() -> Result<()> {
        let directory = tempfile::tempdir()?;
        let root = directory.path();
        fs::create_dir_all(root.join("resources/runtime-scripts"))?;
        let text = "x".repeat(2048);
        let sha = sha256_hex(text.as_bytes());
        let path = root.join(format!("resources/runtime-scripts/{sha}.js"));
        fs::write(&path, &text)?;
        let budget = WorkBudget::new("verified-source-cache", BudgetLimits::work(4));
        let mut cache = VerifiedSources::new(root, &budget, SOURCE_CACHE_BYTES);
        let first = cache.load(&sha)?;
        let second = cache.load(&sha)?;
        assert!(Rc::ptr_eq(&first, &second));
        assert_eq!(budget.remaining_work(), Some(0));
        assert_eq!(first.text, text);
        assert!(cache.load(&sha).is_err());
        fs::write(&path, "not the captured source")?;
        let budget = WorkBudget::unlimited("verify-corrupt-source");
        let mut fresh = VerifiedSources::new(root, &budget, SOURCE_CACHE_BYTES);
        assert!(fresh.load(&sha).is_err());
        assert!(fresh.load("../invalid").is_err());
        let error = fresh
            .load(&sha.to_uppercase())
            .err()
            .context("uppercase digest accepted")?;
        assert_eq!(error.to_string(), "invalid original runtime source digest");
        Ok(())
    }

    #[test]
    fn eviction_and_oversized_sources_do_not_change_verification() -> Result<()> {
        let directory = tempfile::tempdir()?;
        let root = directory.path();
        fs::create_dir_all(root.join("resources/runtime-scripts"))?;
        let texts = ["x".repeat(2048), "y".repeat(2048), "z".repeat(16384)];
        let mut digests = Vec::new();
        for text in &texts {
            let sha = sha256_hex(text.as_bytes());
            fs::write(
                root.join(format!("resources/runtime-scripts/{sha}.js")),
                text,
            )?;
            digests.push(sha);
        }
        let budget = WorkBudget::unlimited("cache-eviction");
        let capacity = VerifiedSource::from_text(texts[0].clone()).retained_bytes(&digests[0]);
        let mut cache = VerifiedSources::new(root, &budget, capacity);
        let first = cache.load(&digests[0])?;
        let second = cache.load(&digests[1])?;
        assert!(!cache.entries.contains_key(&digests[0]));
        assert!(cache.retained_bytes <= capacity);
        let oversized = cache.load(&digests[2])?;
        assert_eq!(oversized.text, texts[2]);
        assert!(!cache.entries.contains_key(&digests[2]));
        assert!(Rc::ptr_eq(&second, &cache.load(&digests[1])?));
        let again = cache.load(&digests[0])?;
        assert!(!Rc::ptr_eq(&first, &again));
        assert_eq!(first.text, again.text);
        Ok(())
    }
}
