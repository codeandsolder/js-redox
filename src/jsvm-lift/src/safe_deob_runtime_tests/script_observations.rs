//! Shared isolated runtime observations of synthetic script fixtures.
//!
//! Completion expressions and event traces must use the same typed encoding;
//! coercion to a string is not a faithful comparison of arrays or primitives.
use super::node;
use anyhow::{bail, Result};
use std::fs;
use tempfile::TempDir;

#[derive(serde::Serialize)]
pub(super) struct Comparison {
    pub(super) label: String,
    pub(super) original: String,
    pub(super) rewritten: String,
}

const RUNNER: &str = include_str!("script_observations.cjs");

/// Run original and rewritten scripts in independent VM contexts. The
/// explicitly selected browser builtins are shared only for fixtures that
/// require them. A bounded batch avoids starting Node for every script.
pub(super) fn compare_pairs(
    suite: &str,
    comparisons: &[Comparison],
    browser_globals: bool,
) -> Result<()> {
    let scratch = TempDir::new()?;
    let path = scratch.path().join("observations.cjs");
    let runner = format!(
        "const comparisons = {};\nconst browserGlobals = {browser_globals};\n{RUNNER}",
        serde_json::to_string(comparisons)?
    );
    fs::write(&path, runner)?;
    let count = node(&path, false)?;
    if count != format!("{}\n", comparisons.len()).as_bytes() {
        bail!("{suite}: unexpected comparison runner output");
    }
    Ok(())
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_observation_runner_detects_mismatches() -> Result<()> {
    let cases = [
        ("signed-zero", "0", "-0"),
        ("nested-signed-zero", "[[0]]", "[[-0]]"),
        ("undefined-vs-hole", "[void 0]", "[,]"),
        ("undefined-vs-null", "[void 0]", "[null]"),
        ("nested-shape", "[[1,2]]", "[1,2]"),
        ("event-signed-zero", "events.push(0);0", "events.push(-0);0"),
        ("exception-message", "throw Error('a')", "throw Error('b')"),
        ("syntax-failure", "function (", "function ("),
    ];
    for (label, original, rewritten) in cases {
        let result = compare_pairs(
            label,
            &[Comparison {
                label: label.into(),
                original: original.into(),
                rewritten: rewritten.into(),
            }],
            false,
        );
        assert!(result.is_err(), "{label} must not compare equal");
    }
    compare_pairs(
        "matching-typed-values",
        &[Comparison {
            label: "matching-typed-values".into(),
            original: "events.push(-0,void 0,0n);[NaN,-0,void 0,,0n]".into(),
            rewritten: "events.push(-0,void 0,0n);[0/0,-0,void 0,,0n]".into(),
        }],
        false,
    )
}
