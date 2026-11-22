//! Shared isolated runtime observations of synthetic script fixtures.
//!
//! Completion expressions and event traces share a typed graph encoding.
//! Descriptors and reference identity are observable; coercion to a string
//! is not a faithful comparison of records, arrays, or primitives.
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

fn assert_mismatch(label: &str, original: &str, rewritten: &str) -> Result<()> {
    let result = compare_pairs(
        label,
        &[Comparison {
            label: label.into(),
            original: original.into(),
            rewritten: rewritten.into(),
        }],
        false,
    );
    let Err(error) = result else {
        bail!("{label} must not compare equal");
    };
    assert!(
        error
            .to_string()
            .contains(&format!("{label}: mismatch at encoded offset")),
        "{label}: unexpected harness error: {error}"
    );
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
        ("exception-value-type", "throw 0", "throw '0'"),
        ("exception-signed-zero", "throw 0", "throw -0"),
        ("exception-bigint", "throw 0n", "throw 0"),
        ("exception-array-shape", "throw [void 0]", "throw [,]"),
        (
            "exception-native-error-type",
            "throw Error('a')",
            "throw 'Error: a'",
        ),
        ("abrupt-vs-normal", "throw 0", "0"),
        ("record-data", "({'x':0})", "({'x':-0})"),
        ("record-order", "({a:1,b:2})", "({b:2,a:1})"),
        ("record-prototype", "({})", "Object.create(null)"),
        (
            "record-extensibility",
            "({})",
            "Object.preventExtensions({})",
        ),
        (
            "record-descriptor",
            "({'x':1})",
            "Object.defineProperty({},'x',{'value':1})",
        ),
        ("array-extra-property", "const a=[];a.x=1;a", "[]"),
        ("array-cycle", "const a=[];a[0]=a;a", "const a=[];a[0]=[];a"),
        ("record-alias", "const a={};[a,a]", "[{},{}]"),
        (
            "event-result-alias",
            "const a=[];events.push(a);a",
            "events.push([]);[]",
        ),
        ("thrown-record", "throw {'x':1}", "throw {'x':2}"),
        (
            "symbol-alias",
            "const s=Symbol('x');[s,s]",
            "[Symbol('x'),Symbol('x')]",
        ),
        ("symbol-kind", "Symbol.for('x')", "Symbol('x')"),
        ("function-alias", "const f=()=>1;[f,f]", "[()=>1,()=>1]"),
    ];
    for (label, original, rewritten) in cases {
        assert_mismatch(label, original, rewritten)?;
    }

    Ok(())
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_observation_runner_rejects_invalid_observations() -> Result<()> {
    for (label, source, marker) in [
        ("syntax-failure", "function (", "SyntaxError"),
        (
            "proxy",
            "new Proxy({}, {})",
            "unsupported observation: proxy",
        ),
        (
            "exotic-object",
            "new Map()",
            "unsupported observation: exotic object",
        ),
        (
            "reparented-exotic",
            "Object.setPrototypeOf(new Map(),null)",
            "unsupported observation: exotic object",
        ),
        (
            "custom-record-prototype",
            "Object.create({})",
            "unsupported observation: object prototype",
        ),
        (
            "custom-error-prototype",
            "new (class extends Error {})('x')",
            "unsupported observation: object prototype",
        ),
        (
            "error-accessor",
            "throw Object.defineProperty(Error('x'),'message',{get(){throw 1}})",
            "unsupported observation: accessor error property",
        ),
    ] {
        let result = compare_pairs(
            label,
            &[Comparison {
                label: label.into(),
                original: source.into(),
                rewritten: source.into(),
            }],
            false,
        );
        let Err(error) = result else {
            bail!("{label}: invalid observation must fail");
        };
        assert!(error.to_string().contains(marker), "{label}: {error}");
    }
    Ok(())
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_observation_runner_compares_matching_graphs() -> Result<()> {
    compare_pairs(
        "matching-data-graphs",
        &[
            Comparison {
                label: "matching-cycle".into(),
                original: "const a={};a.self=a;events.push(a);a".into(),
                rewritten: "const b={};b.self=b;events.push(b);b".into(),
            },
            Comparison {
                label: "matching-accessor-definition".into(),
                original: "({get x(){throw Error('getter called')}})".into(),
                rewritten: "({get x(){throw Error('getter called')}})".into(),
            },
            Comparison {
                label: "matching-symbol-graph".into(),
                original: "const s=Symbol('x');const a={[s]:s};[a,s]".into(),
                rewritten: "const t=Symbol('x');const b={[t]:t};[b,t]".into(),
            },
            Comparison {
                label: "matching-large-sparse-array".into(),
                original: "const a=[];a.length=4294967295;a[7]=1;a".into(),
                rewritten: "const b=Array(4294967295);b[7]=1;b".into(),
            },
        ],
        false,
    )?;
    compare_pairs(
        "matching-abrupt-values",
        &[
            Comparison {
                label: "matching-zero".into(),
                original: "throw -0".into(),
                rewritten: "throw -(0)".into(),
            },
            Comparison {
                label: "matching-error".into(),
                original: "throw TypeError('a')".into(),
                rewritten: "throw new TypeError('a')".into(),
            },
            Comparison {
                label: "matching-thrown-array".into(),
                original: "throw [NaN,,-0]".into(),
                rewritten: "throw [0/0,,-0]".into(),
            },
        ],
        false,
    )?;
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

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_observation_runner_preserves_error_properties() -> Result<()> {
    for (label, original, rewritten) in [
        (
            "error-prototype",
            "throw Object.assign(Error('x'),{'name':'Same'})",
            "throw Object.assign(TypeError('x'),{'name':'Same'})",
        ),
        ("error-message-presence", "throw Error()", "throw Error('')"),
        (
            "error-cause",
            "throw Error('x',{'cause':-0})",
            "throw Error('x',{'cause':0})",
        ),
        (
            "error-aggregate",
            "throw AggregateError([Error('a')],'x')",
            "throw AggregateError([Error('b')],'x')",
        ),
        (
            "error-own-data",
            "throw Object.assign(Error('x'),{'extra':1})",
            "throw Error('x')",
        ),
        (
            "error-extensibility",
            "throw Object.freeze(Error('x'))",
            "throw Error('x')",
        ),
        (
            "error-cause-alias",
            "const a={};events.push(a);throw Error('x',{'cause':a})",
            "events.push({});throw Error('x',{'cause':{}})",
        ),
    ] {
        assert_mismatch(label, original, rewritten)?;
    }
    compare_pairs(
        "matching-error-graphs",
        &[
            Comparison {
                label: "error-cycle".into(),
                original: "const e=Error('x');e.cause=e;events.push(e);throw e".into(),
                rewritten: "const f=new Error('x');f.cause=f;events.push(f);throw f".into(),
            },
            Comparison {
                label: "aggregate-alias".into(),
                original: "const e=Error('member');throw AggregateError([e,e],'x',{'cause':e})"
                    .into(),
                rewritten:
                    "const f=new Error('member');throw new AggregateError([f,f],'x',{'cause':f})"
                        .into(),
            },
            Comparison {
                label: "stack-excluded".into(),
                original: "throw Object.defineProperty(Error('x'),'stack',{get(){throw 1}})".into(),
                rewritten: "throw Error('x')".into(),
            },
        ],
        false,
    )
}
