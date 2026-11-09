use super::*;
use anyhow::{anyhow, Context, Result};
use std::{collections::BTreeMap, fs, path::Path, process::Command};
use tempfile::TempDir;
use work_budget::{run_command, BudgetLimits, WorkBudget};

const FIXTURE_DIR: &str = "corpus/generated/reversible-obfuscation";
const MAIN_FIXTURES: [&str; 30] = [
    "obscura-split-strings.js",
    "obscura-number-expressions.js",
    "obscura-unicode-escape.js",
    "obscura-string-array.js",
    "rotated-base64-string-array.js",
    "direct-rotated-string-array.js",
    "formatted-base64-string-array.js",
    "token-boundaries.js",
    "proxy-literals-unary.js",
    "proxy-members.js",
    "safe-mix.js",
    "proven-helper-prune.js",
    "const-aliases.js",
    "from-char-code-alias.js",
    "obscura-control-flow-storage.js",
    "proxy-calls.js",
    "selector-trailing-params.js",
    "reference-identity-table.js",
    "reference-identity-table-sync.js",
    "ordered-switch.js",
    "ordered-switch-for.js",
    "arithmetic-state.js",
    "arithmetic-state-external.js",
    "arithmetic-state-registers.js",
    "arithmetic-state-try.js",
    "arithmetic-state-conditional.js",
    "multi-exit-reducible-state.js",
    "early-abrupt-state-dispatch.js",
    "static-alias-installer-calls.js",
    "static-alias-live-forwarding.js",
];

fn budget(label: &str) -> WorkBudget {
    WorkBudget::unlimited(format!("semantic-test:{label}"))
}

fn repo_root() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn fixture(file: &str) -> Result<String> {
    let path = repo_root().join(FIXTURE_DIR).join(file);
    fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))
}

fn compact(text: &str) -> String {
    text.chars().filter(|ch| !ch.is_whitespace()).collect()
}

fn node(path: &Path, check_only: bool) -> Result<Vec<u8>> {
    let mut command = Command::new("node");
    if check_only {
        command.arg("--check");
    }
    command.arg(path).current_dir(repo_root());
    let node_budget = WorkBudget::new(
        format!("node:{}", path.display()),
        BudgetLimits::wall_time(std::time::Duration::from_secs(60)),
    );
    let output = run_command(&mut command, &node_budget)
        .with_context(|| format!("running Node for {}", path.display()))?;
    if !output.status.success() {
        return Err(anyhow!(
            "Node failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(output.stdout)
}

fn runtime_equivalent(scratch: &Path, label: &str, before: &str, after: &str) -> Result<()> {
    let before_path = scratch.join(format!("{label}.before.js"));
    let after_path = scratch.join(format!("{label}.after.js"));
    fs::write(&before_path, before)?;
    fs::write(&after_path, after)?;
    assert_eq!(
        node(&before_path, false)?,
        node(&after_path, false)?,
        "{label}"
    );
    Ok(())
}

fn count(report: &SafeDeobReport, kind: &str) -> usize {
    report.transforms.get(kind).copied().unwrap_or_default()
}

fn assert_invariants(label: &str, outcome: &SafeDeobOutcome) {
    assert_eq!(outcome.report.schema, "js-safe-deobfuscate/v1", "{label}");
    assert!(outcome.report.safe_static_only, "{label}");
    assert!(!outcome.report.presentation_formatted, "{label}");
    assert!(
        outcome.report.runtime_semantics_preserved_by_design,
        "{label}"
    );
    assert_eq!(
        outcome.report.analysis_source_sha256, outcome.report.output_sha256,
        "{label}"
    );
}

fn deob_fixture(scratch: &Path, file: &str) -> Result<SafeDeobOutcome> {
    let source = fixture(file)?;
    let work_budget = budget(file);
    let outcome = deobfuscate_source(&source, file, SourceMode::Auto, 16, false, &work_budget)
        .with_context(|| format!("deobfuscating {file}"))?;
    runtime_equivalent(scratch, file, &source, &outcome.source)?;
    assert_invariants(file, &outcome);
    Ok(outcome)
}

fn assert_main_contract(file: &str, outcome: &SafeDeobOutcome) {
    let report = &outcome.report;
    match file {
        "rotated-base64-string-array.js"
        | "direct-rotated-string-array.js"
        | "formatted-base64-string-array.js" => {
            assert!(count(report, "string_array_decode") >= 2, "{file}");
            assert!(count(report, "materialize_decoder_rotation") >= 1, "{file}");
            assert!(count(report, "remove_decoder_rotation_iife") >= 1, "{file}");
        }
        "token-boundaries.js" => {
            for merged in ["returnfalse", "returntrue", "throwtrue"] {
                assert!(!outcome.source.contains(merged), "{merged}");
            }
        }
        "proxy-literals-unary.js" => {
            assert!(count(report, "proxy_literal") >= 4);
            assert!(count(report, "proxy_unary") >= 4);
        }
        "proxy-members.js" => {
            assert!(count(report, "proxy_static_member") >= 2);
            assert!(count(report, "proxy_computed_member") >= 2);
        }
        "proxy-calls.js" => assert!(count(report, "proxy_call") >= 3),
        "multi-exit-reducible-state.js" => {
            assert!(count(report, "if_ladder_structured") >= 2);
        }
        "early-abrupt-state-dispatch.js" => {
            assert!(count(report, "if_ladder_structured") >= 2);
        }
        "proven-helper-prune.js" => {
            assert!(!outcome.source.contains("function pruneMe"));
            assert!(outcome.source.contains("function keepMe"));
            assert!(count(report, "remove_unused_proven_helper") >= 1);
        }
        "from-char-code-alias.js" => {
            assert!(count(report, "from_char_code_alias") >= 4);
            assert!(!outcome.source.contains("c(68)"));
            assert!(outcome.source.contains("c(0xd800)"));
            assert!(outcome.source.contains("mutable(65)"));
        }
        "selector-trailing-params.js" => {
            assert!(count(report, "selector_dispatch_specialize") >= 2);
            assert!(!compact(&outcome.source).contains(&compact(
                "function(selector,left,p2,p3,p4,p5,p6,p7,p8,p9){return(left|0);}",
            )));
        }
        "reference-identity-table.js" | "reference-identity-table-sync.js" => {
            assert!(count(report, "reference_identity_compare") >= 2);
            assert!(count(report, "reference_state_unflatten") >= 1);
        }
        "ordered-switch.js" | "ordered-switch-for.js" => {
            assert!(count(report, "ordered_switch_unflatten") >= 1);
        }
        "arithmetic-state.js"
        | "arithmetic-state-external.js"
        | "arithmetic-state-registers.js"
        | "arithmetic-state-conditional.js" => {
            assert!(count(report, "arithmetic_state_unflatten") >= 1, "{file}");
            assert!(!report.arithmetic_state_proofs.is_empty(), "{file}");
        }
        "static-alias-installer-calls.js" => {
            assert_eq!(report.static_alias_installer_calls.len(), 2);
            assert!(!report.static_alias_installer_calls[0].forwarding_installer_proven);
        }
        "static-alias-live-forwarding.js" => {
            assert_eq!(report.static_alias_installer_calls.len(), 1);
            assert!(report.static_alias_installer_calls[0].forwarding_installer_proven);
        }
        _ => {}
    }
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_generated_runtime_equivalence() -> Result<()> {
    let scratch = TempDir::new()?;
    let mut totals = BTreeMap::<String, usize>::new();
    for file in MAIN_FIXTURES {
        let outcome = deob_fixture(scratch.path(), file)?;
        let expected_changed = !matches!(
            file,
            "static-alias-installer-calls.js" | "static-alias-live-forwarding.js"
        );
        assert_eq!(outcome.report.changed, expected_changed, "{file}");
        assert_main_contract(file, &outcome);
        for (kind, value) in &outcome.report.transforms {
            *totals.entry(kind.clone()).or_default() += value;
        }
    }
    for (kind, minimum) in [
        ("constant_fold", 5),
        ("computed_property", 3),
        ("string_array_decode", 2),
        ("static_array_lookup", 1),
        ("dead_branch", 1),
        ("split_sequence", 1),
        ("const_propagate", 4),
        ("proxy_binary", 5),
        ("proxy_string", 5),
        ("proxy_literal", 4),
        ("proxy_unary", 4),
        ("proxy_static_member", 2),
        ("proxy_computed_member", 2),
        ("proxy_call", 3),
        ("pure_function_eval", 1),
        ("remove_unused_proven_helper", 1),
        ("selector_dispatch_specialize", 2),
        ("reference_identity_compare", 4),
        ("reference_state_unflatten", 1),
        ("ordered_switch_unflatten", 1),
        ("arithmetic_state_unflatten", 1),
    ] {
        assert!(
            totals.get(kind).copied().unwrap_or_default() >= minimum,
            "{kind}"
        );
    }

    let source = fixture("static-alias-installer-calls.js")?;
    let work_budget = budget("formatted-alias");
    let formatted = deobfuscate_source(
        &source,
        "formatted-alias",
        SourceMode::Auto,
        16,
        true,
        &work_budget,
    )?;
    assert!(formatted.report.presentation_formatted);
    assert_ne!(
        formatted.report.analysis_source_sha256,
        formatted.report.output_sha256
    );
    Ok(())
}

fn zero_transform_fixture(scratch: &Path, file: &str, kinds: &[&str]) -> Result<SafeDeobOutcome> {
    let outcome = deob_fixture(scratch, file)?;
    for kind in kinds {
        assert_eq!(count(&outcome.report, kind), 0, "{file}: {kind}");
    }
    Ok(outcome)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_safety_runtime_equivalence() -> Result<()> {
    let scratch = TempDir::new()?;
    assert!(
        count(
            &deob_fixture(scratch.path(), "classic-script-redeclaration.js")?.report,
            "constant_fold"
        ) >= 1
    );
    assert!(deobfuscate_source(
        "const scope={x:1}; with(scope){console.log(x,1+2);}\n",
        "with-statement-negative",
        SourceMode::Auto,
        16,
        false,
        &budget("with-statement-negative"),
    )
    .is_err());

    let fixed_source = "const table=['SEED','cookie=','array'];(function(a,n){const rotate=function(k){while(--k){a['push'](a['shift']());}};rotate(++n);}(table,4));const decode=function(i,_unused){i=i-0x0;let value=table[i];return value;};console.log(decode('0x2'),decode('0x1'),decode('0x0'));\n";
    let fixed = deobfuscate_source(
        fixed_source,
        "fixed-rotated-direct-decoder",
        SourceMode::Auto,
        16,
        false,
        &budget("fixed-rotated-direct-decoder"),
    )?;
    runtime_equivalent(
        scratch.path(),
        "fixed-rotated-direct-decoder",
        fixed_source,
        &fixed.source,
    )?;
    for (kind, minimum) in [
        ("materialize_fixed_decoder_rotation", 1),
        ("remove_fixed_decoder_rotation_iife", 1),
        ("string_array_decode", 3),
    ] {
        assert!(count(&fixed.report, kind) >= minimum, "{kind}");
    }

    for (file, kinds) in [
        (
            "duplicate-scope-decoder-negative.js",
            &["string_array_decode"][..],
        ),
        (
            "mutable-decoder-alias-safety.js",
            &["string_array_decode"][..],
        ),
        (
            "source-sensitive-base64-negative.js",
            &["string_array_decode"][..],
        ),
        (
            "proxy-safety.js",
            &["proxy_binary", "proxy_string", "proxy_call"][..],
        ),
        (
            "ordered-switch-safety.js",
            &["ordered_switch_unflatten"][..],
        ),
        (
            "ordered-switch-for-safety.js",
            &["ordered_switch_unflatten"][..],
        ),
        (
            "arithmetic-state-external-safety.js",
            &["arithmetic_state_unflatten"][..],
        ),
        (
            "arithmetic-state-try-safety.js",
            &["arithmetic_state_unflatten"][..],
        ),
        (
            "arithmetic-state-conditional-safety.js",
            &["arithmetic_state_unflatten"][..],
        ),
        (
            "arithmetic-state-iife-safety.js",
            &["arithmetic_state_unflatten"][..],
        ),
    ] {
        let outcome = zero_transform_fixture(scratch.path(), file, kinds)?;
        if file.starts_with("arithmetic-state-") {
            assert!(outcome.report.arithmetic_state_proofs.is_empty(), "{file}");
        }
    }

    let eval = zero_transform_fixture(
        scratch.path(),
        "proven-helper-prune-eval-safety.js",
        &["remove_unused_proven_helper"],
    )?;
    assert!(eval.source.contains("function hiddenHelper"));

    let arithmetic = deob_fixture(scratch.path(), "arithmetic-state-safety.js")?;
    assert_eq!(count(&arithmetic.report, "arithmetic_state_unflatten"), 1);
    assert_eq!(arithmetic.report.arithmetic_state_proofs.len(), 1);
    assert_eq!(
        arithmetic.report.arithmetic_state_proofs[0].termination,
        "conditional"
    );

    let register = deob_fixture(scratch.path(), "arithmetic-state-registers-safety.js")?;
    assert!(count(&register.report, "arithmetic_state_unflatten") >= 1);
    assert!(register.source.contains("regs[1]"));
    assert!(!register.source.contains("out = \"A\""));
    assert_eq!(
        register.report.arithmetic_state_proofs[0].register_reads_rewritten,
        0
    );
    Ok(())
}

#[test]
#[ignore = "optional external Taobao corpus; semantic CI invokes explicitly"]
fn depythonify_safe_deob_real_et_external_corpus() -> Result<()> {
    let root = repo_root();
    let positive_path = root.join("corpus/taobao/normal_et_f(1).js");
    let negative_path = root.join("corpus/taobao/captcha_et_f(1).js");
    if !positive_path.is_file() || !negative_path.is_file() {
        eprintln!("SKIP real-et: external Taobao corpus is not present in this worktree");
        return Ok(());
    }
    let scratch = TempDir::new()?;
    for (path, expected) in [(&positive_path, 1_usize), (&negative_path, 0_usize)] {
        let source = fs::read_to_string(path)?;
        let outcome = deobfuscate_source(
            &source,
            path.display().to_string(),
            SourceMode::Auto,
            16,
            false,
            &budget(&path.display().to_string()),
        )?;
        let output = scratch
            .path()
            .join(path.file_name().context("real ET filename missing")?);
        fs::write(&output, &outcome.source)?;
        node(&output, true)?;
        assert_eq!(
            count(&outcome.report, "arithmetic_state_unflatten"),
            expected
        );
        assert_eq!(outcome.report.arithmetic_state_proofs.len(), expected);
        if expected == 1 {
            assert!(matches!(
                outcome.report.arithmetic_state_proofs[0]
                    .termination
                    .as_str(),
                "undefined" | "return" | "throw"
            ));
        }
    }
    Ok(())
}
