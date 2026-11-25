#[path = "safe_deob_runtime_tests/literal_proofs.rs"]
mod literal_proofs;
#[path = "safe_deob_runtime_tests/matrices.rs"]
mod matrices;
#[path = "safe_deob_runtime_tests/script_observations.rs"]
mod script_observations;

use super::*;
use anyhow::{anyhow, Context, Result};
use std::{collections::BTreeMap, fs, path::Path, process::Command};
use tempfile::TempDir;
use work_budget::{run_command, BudgetLimits, WorkBudget};

const FIXTURE_DIR: &str = "corpus/generated/reversible-obfuscation";
const MAIN_FIXTURES: &[&str] = &[
    "obscura-split-strings.js",
    "obscura-number-expressions.js",
    "obscura-unicode-escape.js",
    "obscura-string-array.js",
    "rotated-base64-string-array.js",
    "direct-rotated-string-array.js",
    "duplicate-scope-decoder.js",
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
    "reference-identity-table-lexical.js",
    "reference-identity-table-callable.js",
    "ordered-switch.js",
    "ordered-switch-for.js",
    "ordered-switch-bounded.js",
    "arithmetic-state.js",
    "arithmetic-state-lexical.js",
    "arithmetic-state-iife-shadow-safety.js",
    "arithmetic-state-external.js",
    "arithmetic-state-registers.js",
    "arithmetic-state-register-key-safety.js",
    "arithmetic-state-try.js",
    "arithmetic-state-conditional.js",
    "arithmetic-state-primitive-branches.js",
    "multi-exit-reducible-state.js",
    "early-abrupt-state-dispatch.js",
    "exception-resume-state.js",
    "exception-state-multi-entry-cycle.js",
    "exception-state-multi-entry-branching.js",
    "exception-state-write-liveness.js",
    "exception-state-structured-liveness.js",
    "numeric-state-sibling-guard-fold.js",
    "boolean-switch.js",
    "inert-array-truthiness.js",
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
    let before_output = node(&before_path, false)?;
    let after_output = node(&after_path, false)?;
    assert_eq!(
        String::from_utf8_lossy(&before_output),
        String::from_utf8_lossy(&after_output),
        "{label}"
    );
    Ok(())
}

fn count(report: &SafeDeobReport, kind: &str) -> usize {
    report.transforms.get(kind).copied().unwrap_or_default()
}

fn assert_invariants(label: &str, outcome: &SafeDeobOutcome) {
    assert_eq!(outcome.report.schema, "js-safe-deobfuscate/v3", "{label}");
    assert!(outcome.report.guarantees.safe_static_only, "{label}");
    assert!(!outcome.report.guarantees.presentation_formatted, "{label}");
    assert!(
        outcome
            .report
            .guarantees
            .runtime_semantics_preserved_by_design,
        "{label}"
    );
    assert_eq!(
        outcome.report.analysis_source_sha256, outcome.report.output_sha256,
        "{label}"
    );
}

fn deob_fixture(scratch: &Path, file: &str) -> Result<SafeDeobOutcome> {
    let source = fixture(file)?;
    deob_fixture_source(scratch, file, &source)
}

fn deob_fixture_source(scratch: &Path, file: &str, source: &str) -> Result<SafeDeobOutcome> {
    let work_budget = budget(file);
    let outcome = deobfuscate_source(source, file, SourceMode::Auto, 16, false, &work_budget)
        .with_context(|| format!("deobfuscating {file}"))?;
    runtime_equivalent(scratch, file, source, &outcome.source)?;
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
        "duplicate-scope-decoder.js" => {
            assert_eq!(count(report, "string_array_decode"), 2, "{file}");
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
        "multi-exit-reducible-state.js" | "early-abrupt-state-dispatch.js" => {
            assert!(count(report, "if_ladder_structured") >= 2);
        }
        "exception-resume-state.js" => {
            assert!(count(report, "exception_state_pruned") >= 1);
        }
        "boolean-switch.js" => {
            assert!(count(report, "boolean_switch_structured") >= 2);
        }
        "inert-array-truthiness.js" => {
            // One actual constant fold; runtime equivalence checks the guarded effects.
            assert!(count(report, "constant_fold") >= 1);
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
        _ => assert_state_and_alias_contract(file, outcome),
    }
}

fn assert_state_and_alias_contract(file: &str, outcome: &SafeDeobOutcome) {
    let report = &outcome.report;
    match file {
        "reference-identity-table.js" | "reference-identity-table-sync.js" => {
            assert!(count(report, "dispatch_switch_structured") >= 1);
            assert_eq!(count(report, "reaching_heap_dispatch"), 0);
        }
        "reference-identity-table-lexical.js" | "reference-identity-table-callable.js" => {
            assert!(count(report, "reaching_heap_compare") >= 2);
            assert!(count(report, "reaching_heap_dispatch") >= 1);
        }
        "ordered-switch.js" | "ordered-switch-for.js" => {
            assert!(count(report, "dispatch_switch_structured") >= 1);
            assert_eq!(count(report, "ordered_switch_unflatten"), 0);
        }
        "ordered-switch-bounded.js" => {
            assert_eq!(count(report, "ordered_switch_unflatten"), 1);
            assert!(!outcome.source.contains("switch ("));
        }
        "arithmetic-state.js" => assert_eq!(
            count(report, "arithmetic_state_unflatten"),
            0,
            "ambient state may be accessor-backed"
        ),
        "arithmetic-state-lexical.js"
        | "arithmetic-state-iife-shadow-safety.js"
        | "arithmetic-state-external.js"
        | "arithmetic-state-registers.js"
        | "arithmetic-state-register-key-safety.js"
        | "arithmetic-state-conditional.js" => {
            assert!(count(report, "arithmetic_state_unflatten") >= 1, "{file}");
            assert!(!report.arithmetic_state_proofs.is_empty(), "{file}");
        }
        "numeric-state-sibling-guard-fold.js" => {
            assert!(
                count(report, "numeric_state_guard_fold") >= 4,
                "{file}: {:#?}",
                report.transforms
            );
            assert_eq!(outcome.source.matches("log.push('guard')").count(), 1);
            assert_eq!(outcome.source.matches("get value()").count(), 1);
        }
        "arithmetic-state-primitive-branches.js" => {
            assert_eq!(count(report, "arithmetic_state_unflatten"), 5);
            assert_eq!(report.arithmetic_state_proofs.len(), 5);
            assert!(
                report.arithmetic_state_proofs.iter().any(|proof| {
                    proof.branch_paths.is_empty()
                        && proof.state_path.iter().any(|state| state == "void 0")
                }),
                "direct undefined state must dispatch through its next switch"
            );
            for value in ["\"3\"", "true", "null", "void 0"] {
                assert!(
                    report.arithmetic_state_proofs.iter().any(|proof| {
                        proof
                            .branch_paths
                            .first()
                            .and_then(|path| path.first())
                            .is_some_and(|state| state == value)
                    }),
                    "missing typed state {value}"
                );
            }
        }
        "static-alias-installer-calls.js" => {
            assert_eq!(report.static_alias_installer_calls.len(), 2);
            assert!(!report.static_alias_installer_calls[0].forwarding_installer_proven);
        }
        "static-alias-live-forwarding.js" => {
            assert_eq!(report.static_alias_installer_calls.len(), 1);
            assert!(report.static_alias_installer_calls[0].forwarding_installer_proven);
        }
        _ => assert_exception_state_contract(file, outcome),
    }
}

fn assert_exception_state_contract(file: &str, outcome: &SafeDeobOutcome) {
    let report = &outcome.report;
    match file {
        "exception-state-structured-liveness.js" => {
            assert!(
                count(report, "dead_intermediate_state_write") >= 3,
                "{file}: {:#?}",
                report.transforms
            );
            assert!(
                !outcome.source.contains("state = 73;"),
                "{file}: {}",
                outcome.source
            );
            assert!(
                !outcome.source.contains("state = 94;"),
                "{file}: {}",
                outcome.source
            );
            // The immediate state-69 guard has been moved into the arm
            // that sets it. Later liveness removes the now-unused value,
            // but the effect must still execute exactly once.
            assert!(count(report, "numeric_state_guard_fold") >= 1, "{file}");
            assert_eq!(outcome.source.matches("trace.push('left')").count(), 1);
            assert!(
                outcome.source.contains("state = 25;"),
                "{file}: {}",
                outcome.source
            );
            assert!(
                outcome.source.contains("for (;;) {"),
                "{file}: {}",
                outcome.source
            );
        }
        "exception-state-write-liveness.js" => {
            assert!(
                count(report, "exception_state_pruned") >= 2,
                "{file}: {:#?}",
                report.transforms
            );
            // Two assignments are proven dead; five observable writes
            // survive catch reads, implicit retry, closure capture,
            // the normal state guard and mapped-arguments alias.
            assert_eq!(outcome.source.matches("state = 73;").count(), 5);
        }
        "exception-state-multi-entry-cycle.js" | "exception-state-multi-entry-branching.js" => {
            assert_eq!(count(report, "exception_state_pruned"), 1, "{file}");
            assert!(
                outcome.source.contains("for (;;) {"),
                "{file}: {}",
                outcome.source
            );
            assert!(
                outcome.source.contains("else break;"),
                "{file}: {}",
                outcome.source
            );
            if file == "exception-state-multi-entry-cycle.js" {
                assert_eq!(
                    outcome
                        .source
                        .matches("log.push(\"body:\" + count)")
                        .count(),
                    1
                );
            } else {
                // A shared join executes only once even if both branches
                // and the independent catch retry can enter the same SCC.
                assert_eq!(
                    outcome.source.matches("log.push('join:' + count)").count(),
                    1
                );
                for label in [1, 2, 3, 4] {
                    assert!(
                        outcome.source.contains(&format!("state === {label}")),
                        "{file}: {}",
                        outcome.source
                    );
                }
            }
        }
        _ => {}
    }
}

const SCRIPT_COMPLETION_SOURCES: &[&str] = &[
        "let x=0;function f(){x=(eval('var x=1'),2);return x;}[f(),x];",
        "let x=0;function f(){x=eval('var x=1;true')?2:3;return x;}[f(),x];",
        "let x=0;function f(){'use strict';x=(eval('var x=1'),2);return x;}[f(),x];",
        "let x=0;function f(){eval('var x=1');return function(){x=(events.push('pre'),2);return x;};}[f()(),x];",
        "function f(x){x=(eval('var x=1'),2);return x;}f(0);",
        "function f(){try{x=(events.push('rhs'),2);}catch(e){events.push(e.name)}let x=1;return x;}f();",
        "function f(){const x=1;try{x=(events.push('rhs'),2);}catch(e){events.push(e.name)}return x;}f();",
        "function f(){let x=1;x=(events.push('test'),false)?(events.push('yes'),2):(events.push('no'),3);return x;}f();",
        "var x=1;function f(){x=(events.push('rhs'),2);return x;}[f(),x];",
        "let x=0;function f(){x=((0,eval)('1'),2);return x;}[f(),x];",
        "function f(x){return x+1}eval('f=function(x){return x+9}');f(2)",
        "function f(x){return x+1}function g(a=eval('f=x=>x+8')){function f(x){return x+2}}g();f(2)",
        "function f(x){return x+1}function g(a=()=>eval('f=x=>x+8')){function f(x){return x+2}a()}g();f(2)",
        "function f(x){return x+1}const g=()=>{eval('var f=function(x){return x+9}');return f(2)};g()",
        "function f(x){return x+1}function g(){'use strict';eval('f=function(x){return x+9}')}g();f(2)",
        "function g(){function f(x){return x+1}return f(2)}function h(){eval('1')}h();g()",
        "const x=7;const f=()=>{eval('var x=9');return x};f();",
        "const x=7;const f=()=>{(eval)('var x=9');return x};f();",
        "const x=7;const f=()=>{if(true){eval('var x=9');}return x};f();",
        "const x=7;const f=()=>{eval('var x=9');const g=()=>x;return g()};f();",
        "const x=7;const f=function(a=eval('var x=9')){return x};f();",
        "const x=7;const f=()=>{eval('var x=9');return (()=>{'use strict';return x})()};f();",
        "const x=7;const f=()=>{'use strict';eval('var x=9');return x};f();",
        "const x=7;const f=()=>{const g=()=>eval('var x=9');g();return x};f();",
        "const x=7;const f=()=>{(0,eval)('1');return x};f();",
        "function f(){const x=7;eval('1');return x;}f();",
        "const f=()=>{eval('var x=9');{const x=7;return x}};f();",
        "function f(){const a=['outer'];return (()=>{eval('var a=[\"inner\"]');return a[0]})()}f();",
        "function f(){const o={m(){return this===o}};return (true?o.m:null)();}f();",
        "function f(){let x=7;return (true?eval:null)('typeof x');}f();",
        "function f(){const o={x:7};return [delete (true?o.x:null),o.x];}f();",
        "typeof (true?missing:null);",
        "const f=true?function(){}:null;f.name;",
        "const f=true?()=>1:null;f.name;",
        "const f=true?class{}:null;f.name;",
        "function f(v){return 2*(true?v+4:0);}f(3);",
        "function f(){const o={m(){return this===o}};return (true?o?.m:null)();}f();",
        "function f(){const o={tag(){return this===o}};return (true?o.tag:null)`a`;}f();",
        "function f(){const p={get:x=>x.m};const o={m(){return this===o}};return p.get(o)();}f();",
        "function f(){const p={get:(x,k)=>x[k]};const o={m(){return this===o}};return p.get(o,'m')();}f();",
        "function f(){const p={get:x=>x.m};const o={m:7};return [delete p.get(o),o.m];}f();",
        "function f(){const p={get:x=>x.m};const o={m(){return this===o}};return p.get(o)?.();}f();",
        "function f(){const p={get:x=>x.tag};const o={tag(){return this===o}};return p.get(o)`a`;}f();",
        "function f(){const x=-1;return x.toString();}f();",
        "function f(){const x=-0;return 1/x;}f();",
        "function f(){const x=-2;return x**2;}f();",
        "function f(){const x=void 0;try{return typeof x.toString;}catch(e){return e.name;}}f();",
        "function f(){const x=7;return delete x;}f();",
        "function f(){const x=7;return delete ((x));}f();",
        "function f(){const x=void 0;try{return x();}catch(e){return e.name;}}f();",
        "function f(){const x=void 0;return x?.(events.push('bad'));}f();",
        "function f(){const p={x:-1};return p.x.toString();}f();",
        "function f(){const a=[-1];return a[0].toString();}f();",
        "function f(){const p={x:void 0};return p.x?.(events.push('bad'));}f();",
        "function f(){const p={op:(x=events.push('default'))=>-x};return p.op(void 0);}f();",
        "function f(){const p={op:(a,b=events.push('default'))=>a+b};return p.op(7,void 0);}f();",
        "function f(){function g(){return -1;}return g().toString();}f();",
        "function f(){return (2-3).toString();}f();",
        "function f(){const c=void 0;return c?.x;}f();",
        "function f(){const a=[void 0];return a[0]?.(events.push('bad'));}f();",
        "function f(){return a[0];const a=[7];}f();",
        "function f(){return g();const a=[7];function g(){return a[0];}}f();",
        "function f(){const a=[7];(eval)('a[0]=9');return a[0];}f();",
        "function f(){const a=[7];const g=()=>eval('a[0]=9');g();return a[0];}f();",
        "function f(){const a=[7];function g(a){eval('a[0]=9')}g([0]);return a[0];}f();",
        "function f(){const a=[7];(0,eval)('1');return a[0];}f();",
        "Object.defineProperty(Array.prototype,'9',{get(){this[0]=9;return 1}});function f(){const a=[7];events.push(a[9]);return a[0];}f();",
        "const a=[7];(0,eval)('a[0]=9');a[0];",
        "const a=[7];Object.defineProperty(globalThis,'read',{get(){a[0]=9;return x=>x}});read(a[0]);",
        "function f(){const p={x:1,get x(){return 2;}};return p.x;}f();",
        "function f(){const p={x:1,...{x:2}};return p.x;}f();",
        "function f(){const p={x:1,['x']:events.push('key')};return p.x;}f();",
        "function f(){const p={x:1,mutate(){this.x=2;}};p.mutate();return p.x;}f();",
        "function f(){const p={x:1};eval('p.x=9');return p.x;}f();",
        "function f(){return g();var p={x:1};function g(){return p.x;}}f();",
        "function f(){var p={x:1};var p={x:2};return p.x;}f();",
        "function f(){const p={__proto__:1};return p.__proto__===Object.prototype;}f();",
        "function f(){const p={['__proto__']:1};return p.__proto__;}f();",
        "function f(){const p={invoke:function(eval,s){var hidden=7;return eval(s);}};return p.invoke(eval,'hidden');}f();",
        "function f(){const p={op:function(a,a){return a+a;}};return p.op(1,2);}f();",
        "function f(){const p={x:1,...{x:2},x:3};return p.x;}f();",
        "function f(){const p={x:1,[(events.push('key'),'x')]:2,x:3};return p.x;}f();",
        "function f(){let p={op(a,b){return a+b;}};return p.op(1,2);}f();",
        "function f(){var p={x:1};const g=()=>p.x;return g();}f();",
        r"['😀'<'\uE000','😀'<='\uE000','😀'>'\uE000','😀'>='\uE000'];",
        r"['\u{10000}'<'\uFFFF','\uFFFF'<'\u{10000}','a'<'ab','😀'==='😀'];",
        "''+(1**(0/0));",
        "''+((-1)**(1/0));",
        "''+(1**(-1/0));",
        "''+((0/0)**0);",
        "''+(1/((-0)**3));",
        "''+((-0)**(-3));",
        "''+((-2)**0.5);",
        "''+((-2)**3);",
        "function f(){const a=1**(0/0);return a===a;}f();",
        "f();const x=7;function f(){return x;}",
        "function g(){return f();const x=7;function f(){return x;}}g();",
        "switch(1){case 0:const x=7;break;case 1:x;}",
        "f();const x=7;function f(){const y=x+1;return y;}",
        "f();const x=7;function f(){class C{static y=x;}return C.y;}",
        "{f();const x=7;function f(){return x;}}",
        "const f=()=>x;f();const x=7;",
        "const x=7;const f=()=>x;f();",
        "const x=7;const f=function(){return x;};f();",
        "const x=7;{function f(){return x;}f();}",
        "const x=7;const f=()=>{function g(){return x;}return g();};f();",
        "const x=7;class C{static get value(){return x;}}C.value;",
        "for(const x=7;;){x;break;}",
        "const x=7,y=x+1,z=y+1;z;",
        "switch(0){case 0:const x=7;x;break;case 1:break;}",
        "switch(1){case 0:const x=7;function f(){return x;}break;case 1:f();}",
        "function f(){let x;x=7;return (eval)('x');} f();",
        "function f(){let x;x=7;return ((eval))('x');} f();",
        "function f(){let x;x=7;return (()=>(eval)('x'))();} f();",
        "function f(){function hidden(){return 'ok';}return (eval)('hidden()');} f();",
        "function f(){let x;x=7;return (0,eval)('typeof x');} f();",
        "function f(){let x;x=7;return eval?.('typeof x');} f();",
        "1;",
        "1;2;",
        "1;var x;",
        "1;{let x;}",
        "1;{2;}",
        "1;if (true) {}",
        "1;if (false) 2;",
        "1;if (true) {let x;}",
        "1;if (true) {2; ;}",
        "{let x;x=7;}",
        "{let x;x=7;3;}",
        "outer:{1;break outer;2;}",
        "outer:{1;{break outer;}2;}",
        "outer:{1;if (true) break outer;2;}",
        "var i=0; while(i++<2){i;}",
        "1;while(false){2;}",
        "1;for(0;true;true){break;}",
        "1;for(0;true;true){2;break;}",
        "1;switch(1){case 2:2;break;}",
        "1;switch(0){case 0:2;case 1:3;break;}",
        "1;switch(1){case 1:break;}",
        "var flag=false;switch(!flag){case (events.push('test'),true):break;case false:2;}",
        "var flag=false;switch(!flag){case (events.push('test'),true):7;break;case false:2;}",
        "try {1;} finally {2;}",
        "try {throw 3;} catch(e){e;} finally{2;}",
        "outer:try{3;}finally{2;break outer;}",
        "outer:try{3;}finally{break outer;}",
        "outer:{1;try{break outer;}finally{}}",
        "function f(){if(false){var x=2;}return x;} f();",
        "let x=0; x++; if(x){}",
        "var i=0; while(i++<2){ if(i===2)continue; 7;}",
        "1; try { throw 7; } finally { 2; }",
        "1; switch(0){case 0:events.push('a');case 1:(events.push)('b');break;}",
        "{x=7;let x;}",
        "{let x=(function(){x=7;})()}",
        "function f(){const inner=()=>{x=7;};inner();let x;} f();",
        "switch(1){case 0:let x;case 1:x=7;break;}",
        "function f(){if(true){x=7;}let x;} f();",
        "function f(a=class{static{b=7;}},b){} f();",
        "for(let x of [class{static{x=7;}}]){}",
        "{let x;{x=7;}}",
        "function f(){x=7;var x;} f();",
        "function f(x){x=7;} f();",
        "function f(){let x,y=class{static{x=7;}};} f();",
        "for(let x of [0]){x=7;}",
        "for(let x in {a:1}){x=7;}",
        "switch(1){case 1:let x;x=7;break;}",
        "1;while(true){4;break;}",
        "1;while(2-2){events.push('bad');}",
        "1;while(!0)break;",
        "1;do {4;} while(false);",
        "1;do {break;} while(events.push('bad'));",
        "1;do {events.push('once');break;} while(events.push('bad'));",
        "1;do {events.push('once');continue;events.push('bad');} while(false);",
        "1;for(;;){4;break;}",
        "1;for(events.push('init');1;events.push('bad')){4;break;}",
        "1;for(events.push('init');1;events.push('bad'))break;",
        "1;for(var x=events.push('init');1;events.push('bad')){x;break;}",
        "1;for(let i=0,f=()=>i;true;events.push('bad')){i++;events.push(f(),i);break;}",
        "outer:for(var i=0;true;events.push('update')){if(i++<1)continue outer;events.push(i);break;}",
        "1;for(;;){if(events.push('early'))break;events.push('bad');break;}",
        "1;while(true){switch(events.push('case')){case 1:events.push('hit');break;}4;break;}",
        "1;while(true){for(var i=0;i<2;i++){if(i===0)continue;events.push(i);}5;break;}",
        "1;for(;;){inner:for(var i=0;i<2;i++){if(i===0)continue inner;events.push(i);}6;break;}",
        "outer:while(true){1;{break outer;}7;break;}",
        "outer:while(true){if(events.push('out'))break outer;7;break;}",
        "outer:for(var i=0;i<2;i++){while(true){events.push(i);continue outer;break;}}",
        "1;while(true){try{events.push('try');if(events.length)break;}finally{events.push('finally');}6;break;}",
        "1;for(events.push('init');true;events.push('bad')){throw 17;break;}",
        "function f(){for(var x=7;true;events.push('bad')){return x;break;}} f();",
        "1;do 'use strict';while(false);",
        "1;for(;;){let secret=7;events.push(()=>secret);break;} events[0]();",
        "for(var i=0;;){switch(i++){case 0:continue;}break;}",
        "first:second:for(var i=0;true;events.push('update')){if(i++<1)continue first;events.push(i);break;}",
        "again:do {if(events.push('once'))continue again;break;}while(false);",
        "outer:for(var i=0;i<2;i++){while(true){events.push(i);if(i===0)continue outer;break;}events.push('tail');}",
        r#"const order=["0","1"];let index=0;while(true){switch(order[index++]){case 0:events.push("zero");continue;case 1:events.push("one");continue;}break;}events.join(',');"#,
        r#"const order=["0","1"];const index=0;while(true){switch(order[index++]){case "0":events.push("zero");continue;case "1":events.push("one");continue;}break;}events.join(',');"#,
        r#"if(false){var order=["0","1"];};let index=0;while(true){switch(order[index++]){case "0":events.push("zero");continue;case "1":events.push("one");continue;}break;}events.join(',');"#,
        r#"Array.prototype[2]="0";const order=["0","1"];let index=0;while(true){switch(order[index++]){case "0":events.push("zero");continue;case "1":events.push("one");continue;}break;}events.join(',');"#,
        r#"String.prototype.split=function(){return ["1","0"]};const order="0|1".split("|");let index=0;while(true){switch(order[index++]){case "0":events.push("zero");continue;case "1":events.push("one");continue;}break;}events.join(',');"#,
        "for(let a=[1,'1',true,0],i=0;;){switch(a[i++]){case '1':events.push('string');continue;case 1:events.push('number');continue;case true:events.push('bool');continue;case 0:7;break;}break;}",
        "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:7;continue;case 2:break;}break;}",
        "9;for(let a=[1,2],i=0;;){switch(a[i++]){case 1:7;continue;case 3:8;continue;}break;}",
        "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:events.push('a');continue;case 2:events.push('b');continue;}break;}",
        "for(let a=[1,1,2],i=0;;){switch(a[i++]){case 1:events.push('a');continue;case 2:8;break;}break;}",
        "for(let a=[-0,1],i=0;;){switch(a[i++]){case 0:events.push('zero');continue;case 1:7;break;}break;}",
        "for(let a=[0/0,1],i=0;;){switch(a[i++]){case 0/0:events.push('bad');continue;case 1:8;break;}break;}",
        "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:events.push('a');continue;case 1:events.push('bad');continue;case 2:8;break;}break;}",
        "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:events.push('a');continue;case 2:throw 7;case 3:var unused=9;break;}break;}",
        "var i=0;while(true){switch(i++){case (events.push('test0'),0):events.push('hit0');continue;default:events.push('default');break;case (events.push('test1'),1):7;continue;}break;}",
        "var i=0;while(true){switch(i++){case 0:7;continue;case 1:try{8;break;}finally{events.push('finally');}}break;}",
        "var i=0;while(true){switch(i++){case 0:if(events.push('break'))break;continue;case 1:9;continue;}break;}",
        "var i=0;outer:while(true){switch(i++){case 0:events.push('zero');continue outer;case 1:events.push('one');break outer;}break;}",
        "const a=new Proxy([0,1],{get(t,k){events.push(String(k));return t[k]}});let i=0;while(true){switch(a[i++]){case 0:7;continue;case 1:8;continue;}break;}i;",
        "for(var i=0,extra=events.push('init');i<3;events.push('update')){switch(i++){case 0:7;continue;case 1:8;break;}break;}extra;",
        "var i=0;do{switch(i++){case 0:7;continue;case 1:8;break;}break;}while(events.push('test'));",
        "var i=0;while(true){switch(i++){case 0:let a=5;continue;case 1:a;break;}break;}",
        "var i=0;while(true){switch(i++){case 0:(eval)('events.push(1)');continue;case 1:8;break;}break;}",
        "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:events.push(i);continue;case 2:8;break;}break;}",
        "var i=0;while(true){switch(i++){case 0:events.push('a');case 1:events.push('b');continue;case 2:break;}break;}",
        "var i=0;while(true){switch(i++){case 0:var x=events.push('var');continue;case 1:8;break;}break;}x;",
        "for(let a=[1,2],i=0;;){switch(a[i++]){case 1:inner:for(let j=0;j<2;j++){if(j===0)continue inner;events.push(j);}continue;case 2:9;break;}break;}",
        "outer:for(let a=[1,2],i=0;;){switch(a[i++]){case 1:if(events.push('break'))break outer;continue;case 2:9;break;}break;}",
        "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:7;continue;case 2:8;continue;}break;}",
        "9;for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:7;continue;case 2:continue;}break;}",
        "for(let a=[0,1,2],i=1;i<a['length']&&a[i]!==2;){switch(a[i++]){case 1:events.push('one');continue;case 2:events.push('bad');continue;}break;}",
        "for(let a=[1,3],i=0;i<a.length;a.length){switch(a[i++]){case i:events.push('first');continue;case i+1:events.push('second');continue;}break;}",
        "for(let a=[1,2],i=-0;1/i<0;){switch(a[i++]){case 1:events.push('zero');continue;case 2:events.push('bad');continue;}break;}",
        "9;for(let a=[1,2],i=-1;i>=0;){switch(a[i++]){case 1:events.push('bad');continue;case 2:8;continue;}break;}",
        "for(let a=[1,2],i=0;i<1;){switch(a[i++]){case i:events.push('hit');continue;case events.push('bad'):8;continue;}break;}",
        "for(let a=[1,2],i=0,unused=void 0;i<a.length;){switch(a[i++]){case 1:if(events.push('break'))break;7;continue;case 2:events.push('bad');}break;}",
        "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:if(events.length)break;events.push('one');continue;case 2:8;}break;}",
        "again:for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:events.push('one');continue again;case 2:events.push('two');continue again;}break;}",
        "for(let a=[1,2],i=0;i<a.length;events.push('update')){switch(a[i++]){case 1:7;continue;case 2:8;continue;}break;}",
        "Object.defineProperty(Array.prototype,'2',{get(){events.push('inherited');return 0}});for(let a=[1,2],i=0;i<a.length;a[i]){switch(a[i++]){case 1:7;continue;case 2:8;continue;}break;}",
        "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case (events.push('label'),1):7;continue;case 2:8;continue;}break;}",
        "for(let a=[1+1,3],i=0;i<a.length;){switch(a[i++]){case a[0]:events.push('own0');continue;case a[1]:events.push('own1');continue;}break;}",
        "for(let a=[1,2],i=0;i<a.length;){switch(a[i++]){case 1:if(!events.length){events.push('continue');continue;}8;continue;case 2:9;continue;}break;}",
        "for(let a=[1],i=0;i<a.length;){switch(a[i++]){case 1:7;continue;}break;}",
        "for(let a=[1],i=0;i<a.length;){switch(a[i++]){default:7;continue;}break;}",
        "var i=0;for(;i<2;){switch((events.push('selector'),i++)){default:{events.push(i);continue;}}break;}",



        "const a=[7];const v=a[0];(0,eval)('a[0]=9');[v,a[0]];",
        "function f(fn){const a=[7];return fn(a[0],(a[0]=9),a[0]);}f((...args)=>args);",
        "function f(){const a=[7];return a[(a[0]=9,0)];}f();",
        "let a=[7];const prior=a[0];a[0]=9;[prior,a[0]];",
        "const a=[7];const b=a;const x=b[0];(0,eval)('a[0]=9');[x,b[0]];",
        "function f(flag){let a=[7];if(flag){a[0]=9;return 1;}return a[0];}[f(true),f(false)];",
        "const a=[,9];[a.length,a[1]];",
        "let a={x:7,...{x: 9},x:11};a.x;",
        "function f(flag){let a={x:7,y:8};if(flag)a={x:7,z:9};return a.x;}[f(false),f(true)];",
        "function f(flag){let a=flag?{x:7,y:8}:{x:7,y:9};return [a.y,a.x];}[f(false),f(true)];",
        "function f(flag){let a=flag?{x:7}:{get x(){events.push('getter');return 9}};return a.x;}[f(false),f(true)];",
        "function f(){const a={'1e+21':7,1e21:9};return a[1e21];}f();",
        "function f(){const a={'0.0000001':7,1e-7:9};return [a['0.0000001'],a[1e-7]];}f();",
        "let a={'1e+21':7,1e21:9};a['1e+21'];",
        "function f(){const a={x:7,y:events.push('init')};return a.x;}f();",
        "({x:7,y:events.push('init')}).x;",
        "let a=[7];let i=0;const v=a[i];a=[9];[v,a[i]];",
        "function f(flag){let a={x:7};let b=a;if(flag)b={x: 9};return [a.x,b.x];}[f(false),f(true)];",
        "function f(flag){let a=[-0];if(flag)a=[0];return 1/a[0];}[f(true),f(false)];",
        "let a=[7];let i=0;while(i++<2){a[0]++;}a[0];",
        "let a=[7];try{a[0]=9;throw 1;}catch(e){}a[0];",
        "let a={get x(){a.y=9;return 0;},y:7};const x=a.x;[x,a.y];",
        "let a=[7];let b=0;b=(a[0]=9);a[0];",
        "const a=[7,...[8,9]];[a[0],a[1],a.length];",
        "const a=[7];const b={x:7,...{get y(){a[0]=9;return 1;}}};[a[0],b.x];",
        "const a=[7];const x=a[0];Object.defineProperty(Array.prototype,'9',{get(){a[0]=9;return 0}});a[9];[x,a[0]];",
        "function f(flag){const a=[7];flag&&eval('a[0]=9');return a[0];}[f(false),f(true)];",
        "let a=[7];const b=()=>a[0];a=[9];b();",
        "let a=[7];let b=a;const x=b[0];b=[9];[x,a[0],b[0]];",
        "let a=[7];{let a=[9];a[0];}a[0];",
        "const a=[7];let i=0;const o={[(i=1,'x')]:a[i-1]};[o.x,i];",
        "let a={x:7,y:8};let b=a;b.x=9;[a.x,a.y];",
        "let a={x:{y:7}};let b=a.x;b.y=9;a.x.y;",
        "let a={x:7};let b={a};b.a.x+=2;a.x;",
        "let a={x:7};let b={a};const p=b.a.x++;const q=++b.a.x;[p,q,a.x];",
        "let a={x:0,y:8};a.x ||= 9;a.x &&= 7;a.x ??= events.push('bad');[a.x,a.y];",
        "let a={x:null};a.x ??= {y:7};a.x.y;",
        "let a={x:7};let b=a;a.x=(a={x:8},9);[a.x,b.x];",
        "let a={x:7};let b=a;a[(a={x:8},'x')]=9;[a.x,b.x];",
        "let a=[7,8,9];let b=a;b.length=2;[a.length,a[1],a[2]];",
        "let a=[7,8,9];a.length='1';[a[0],a.length,a[2]];",
        "let a=[7,8,9];delete a[1];[a[0],a[2],a.length];",
        "let a={x:null,y:7};a.x=a;a.x.x.x.y;",
        "let a={x:7};let b={x: 9};let c=true?a:b;c.x=8;[a.x,b.x];",
        "function f(flag){let a={x:7};let b={x:8};let c=flag?a:b;c.x=9;return [a.x,b.x];}[f(true),f(false)];",
        "function f(flag){let a={x:7,y:8};let b={x:7,y:9};let c=flag?a:b;c.x=9;return [c.y,a.y,b.y];}[f(true),f(false)];",
        "function f(flag){let a={x:7};if(flag)a.x=9;else a.x=9;return a.x;}[f(true),f(false)];",
        "function f(flag){let a={x:7};if(flag)a.x=9;return a.x;}[f(true),f(false)];",
        "function f(v){let a={x:v,y:7};a.x ||= 9;return [a.x,a.y];}[f(0),f(1)];",
        "function f(v){let a={x:7,y:8};a.x=v;return [a.x,a.y];}f(9);",
        "let a={x:7};let b={p:a};let c={q:b};c.q.p.x=9;c.q.p.x;",
        "let a={x:7};function mutate(){a.x=9;return 1;}let b={p:a,y:mutate()};b.p.x;",
        "let a={x:7};let b={p:a,y:(a.x=9)};b.p.x;",
        "let a={x:7};const x=a[(a.x=9,'x')];[x,a.x];",
        "function f(flag){let a={x:7};let b=flag?{p:a}:{p:a};return b.p.x;}[f(true),f(false)];",
        "const a=[7,...[8,9]];a.length=1;[a[0],a.length];",
        "const a={16:7};a[0x10n]=9;a[16n];",
        "let a={x:7};let b=a;if(a===b)a.x=9;a.x;",
        "let a={x:7};let b={x:8};if(a!==b)a.x=9;a.x;",
        "let a={x:7};if(typeof a==='object')a.x=9;a.x;",
        "function f(flag){let a={x:7};let b={x:8};let c=flag?a:b;if(c===a)a.x=9;return a.x;}[f(true),f(false)];",
        "let a={x:7};Object.defineProperty(a,'x',{set(v){events.push(v)}});a.x=9;a.x;",
        "Object.defineProperty(Object.prototype,'missing',{set(v){events.push(v);this.x=9}});let a={x:7};a.missing=4;a.x;",
        "Object.defineProperty(Array.prototype,'1',{get(){return 9}});let a=[7,8];a.length=1;a[1];",
        "let a={x:7};let b=a;Object.freeze(a);b.x=9;a.x;",
        "let a={x:7};let b={p:a};(0,eval)('a.x=9');b.p.x;",
        "let a=[7,8];try{a.length=1.5;}catch(e){events.push(e.name)}a.length;",
        "let a={x:7};let b=a;b.x=(delete a.x,9);b.x;",
        "let a={x:7};let b=a;b.x+=(a.x=10);a.x;",
        "let a={x:7};let b=a;let c=(a.x=9,a);[c.x,b.x];",
        "let a={__proto__:null};const m=a.missing;a.x=7;const x=a.x;delete a.x;[m,x,a.x];",
        "let p={x:7};let a={__proto__:p};const x=a.x;p.x=9;[x,a.x];",
        "let p={x:7};let a={__proto__:p};a.x=9;const x=a.x;delete a.x;[x,a.x,p.x];",
        "let p={__proto__:null,x:7};let a={__proto__:p};a.y=9;const y=a.y;delete a.y;[y,p.y,a.y];",
        "let p={__proto__:null,x:{y:7}};let a={__proto__:p};a.x.y=9;[p.x.y,a.x.y];",
        "let p={x:7};let a={__proto__:{__proto__:p}};const x=a.x;p.x=9;[x,a.x];",
        "let a={__proto__:{x:7},x:8};delete a.x;a.x;",
        "let a={__proto__:null};a.__proto__=9;a.__proto__;",
        "let a={['__proto__']:7};a.__proto__;",
        "let a={__proto__:null};a.x??=7;a.x;",
        "let p={x:7};let a={__proto__:p};a.x+=2;[a.x,p.x];",
        "let p={x:7};let a={__proto__:p};let y=a.x++;[a.x,p.x,y];",
        "function f(flag){let a={__proto__:null};if(flag)a.x=7;a.x=9;return a.x;}[f(true),f(false)];",
        "function f(flag){let a={__proto__:null,x:7};if(flag)delete a.x;a.x=9;return a.x;}[f(true),f(false)];",
        "function f(flag){let p={x:7};let a={__proto__:p};if(flag)a.x=7;return a.x;}[f(true),f(false)];",
        "function f(flag){let p={x:7};let a={__proto__:p,x:7};if(flag)delete a.x;return a.x;}[f(true),f(false)];",
        "function f(flag){let p=flag?{x:7}:{x:7};let a={__proto__:p};return a.x;}[f(true),f(false)];",
        "function f(flag){let p=flag?{x:7}:{x: 9};let a={__proto__:p};return a.x;}[f(true),f(false)];",
        "function f(k){let a={x:7,[k]:9};a.x=8;return a.x;}[f('x'),f('z')];",
        "function f(k){let a={__proto__:null,[k]:9};a.x=8;return a.x;}[f('x'),f('z')];",
        "let a={__proto__:null,x:7,...{get x(){events.push('get');return 8;}}};a.x=9;a.x;",
        "let a={__proto__:null,get x(){return 7;}};delete a.x;a.x=9;a.x;",
        "let p=[7,8];let a={__proto__:p};const len=a.length;p.length=1;[len,a.length,a[0]];",
        "let p=[7];let a={__proto__:p};a.length=9;[a.length,p.length];",
        "Object.defineProperty(Object.prototype,'missing',{get(){events.push('get');return 9}});let a={__proto__:3};a.missing;",
        "Object.defineProperty(Object.prototype,'x',{set(v){events.push(v);this.y=9}});let a={};a.x=8;a.y;",
        "let p={get x(){events.push('get');return 7;}};let a={__proto__:p};a.x;",
        "let p={set x(v){events.push(v);this.y=9}};let a={__proto__:p};a.x=9;a.y;",
        "function f(k){let a={__proto__:null,x:7,get [k](){return 9;}};return a.x;}[f('x'),f('y')];",
        "let p={x:7};let a={__proto__:p};function mutate(){p.x=9}mutate();a.x;",
        "let p={x:7};function mutate(){p.x=9;return 1;}let a={__proto__:p,y:mutate()};a.x;",
        "let a={__proto__:null};Object.setPrototypeOf(a,{x: 9});a.x;",
        "let a={__proto__:null};Object.defineProperty(a,'x',{value:7});a.x=9;a.x;",
        "let a=[1,2];let b={__proto__:a};b[1]=9;[a[1],b[1],a.length,b.length];",
        "let a={x:7};let b={...a};b.x;",
        "let a={x:7};let b={...a};a.x=9;b.x;",
        "let a={x:{y:7}};let b={...a};b.x.y=9;[a.x.y,b.x.y];",
        "let a={__proto__:{x:7}};let b={__proto__:null,...a};b.x;",
        "let a=[7,,9];let b={__proto__:null,...a};[b[0],b[1],b[2],b.length];",
        "let a=[7,8];a.length=1;let b={__proto__:null,...a};[b[0],b[1],b.length];",
        "let b={x:2,...{x:7},x:9};b.x;",
        "let b={x:2,...{x:7}};b.x;",
        "let a={__proto__:null,x:7};let b={__proto__:null,...a};[b.x,b.y];",
        "let a={__proto__:null,...null,...void 0,...7,...true};a.x;",
        "let a={__proto__:null,...'ab'};[a[0],a[1],a[2],a.length];",
        "let a={__proto__:null,...'é中'};[a[0],a[1],a[2]];",
        "let a={__proto__:null,...'😀z'};[a[0].charCodeAt(0),a[1].charCodeAt(0),a[2],a[3]];",
        "let a={['__proto__']:7};let b={__proto__:null,...a};[b.__proto__,b.x];",
        "let a={x:7};let b={get x(){events.push('wrong');return 9},...a};b.x;",
        "function f(flag){let a=flag?{x:7}:{y:8};let b={__proto__:null,x:7,...a};return b.x;}[f(true),f(false)];",
        "function f(flag){let a=flag?{x:7}:{y:8};let b={__proto__:null,...a};return [b.x,b.z];}[f(true),f(false)];",
        "function f(k){const a={__proto__:null,[k]:7};const b={__proto__:null,x:7,...a};return b.x;}[f('x'),f(Symbol('x')),f('y')];",
        "let a={x:7,...{get x(){events.push('get');return 8}}};let b={...a};b.x=9;b.x;",
        "let p={x:7};let b={...{get x(){p.x=9;events.push('get');return 7}}};p.x;",
        "let a={get x(){events.push('get');return 7}};let b={...a};b.x;",
        "function f(k){let a={get [k](){events.push('get');return 7}};let b={__proto__:null,...a};return b.x;}[f('x'),f(Symbol('x'))];",
        "let a={x:7};function side(){a.x=9;return 0;}let b={...a,y:side()};[a.x,b.x];",
        "let a={x:7};let b={...a,y:(a.x=9)};[a.x,b.x];",
        "let a={x:7};let b={...a,...(a.x=9,a)};[a.x,b.x];",
        "let a={x:7};function unknown(){a.x=9;}let b={...a,...(unknown(),a)};b.x;",
        "Array.prototype[Symbol.iterator]=function*(){yield 99;};let a=[7,8];let b={...a};b[0];",
        "let a=[7,8];let b={...a};[b[0],b[1],b.length];",
        "let a={__proto__:null,[Symbol('a')]:7};let b={...a};Reflect.ownKeys(b).length;",
];

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_reaching_heap_dispatch_runtime_equivalence() -> Result<()> {
    let sources = [
        "let a=[[],[]];for(let state=a[0];true;){switch(state){case a[0]:state=a[1];continue;case a[1]:-0;break;}break;}",
        "let a=[[],[]],x=0;for(let state=a[0];true;){x++;switch(state){case a[0]:x+=2;case a[1]:x+=3;break;}break;}x;",
        "let a=[[],[]];for(let state=[];true;){42;switch(state){case a[0]:9;break;}break;}",
        "let a=[[],[]],f=[null,null];for(let state=a[0],i=0;i<2;i++){switch(state){case a[0]:f[0]=()=>i;state=a[1];continue;case a[1]:f[1]=()=>i;continue;}break;}[f[0](),f[1]()];",
        "let a=[[],[]],f=[null,null,null];for(let state=a[0],i=0;i<2;f[i]=()=>i,i++){switch(state){case a[0]:state=a[1];continue;case a[1]:19;continue;}break;}[f[0](),f[1]()];",
        "let a=[[],[]];for(let state=a[0];true;){switch(state){case a[1]:var hidden=42;break;case a[0]:7;break;}break;}typeof hidden;",
        "let a=[[],[]];for(let state=a[1];true;){switch(state){default:23;case a[0]:31;break;case a[1]:44;break;}break;}",
        "let a=[[],[]],f=[null];for(let state=a[0],i=0;i<1;f[0]=()=>i,i++){switch(state){case a[0]:-0;continue;}break;}f[0]();",
    ];
    script_runtime_equivalence(&sources, "reaching-heap-dispatch", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_observation_coverage_runtime_equivalence() -> Result<()> {
    let sources = [
        "function f(target){for(let i=0;i<2;){let a=i===0?[0]:target;let b=[i];i=i+(a[0]=b[0],1);}}let t=[0];f(t);t[0];",
        "function f(target){for(let i=0;i<2;){let a=i===0?[0]:target;let b=[i];i=i+(a[0]+=b[0],1);}}let t=[7];f(t);t[0];",
        "function f(target){for(let i=0;i<2;){let a=i===0?[0]:target;let b=[i];i=i+(a[0]=(()=>{let c=[i];return c[0];})(),1);}}let t=[0];f(t);t[0];",
        "function f(target){for(let i=0;i<2;){let a=i===0?[0]:target;let b=[i];i=i+(a[0]=b[0],1);}}let t={set 0(v){events.push(v);}};f(t);events;",
    ];
    script_runtime_equivalence(&sources, "observation-coverage", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_reference_construction_runtime_equivalence() -> Result<()> {
    let source = fixture("reference-identity-table-sync.js")?;
    let (builder, _) = source
        .split_once("var trace")
        .context("reference fixture builder")?;
    let preinit = format!(
        "try{{console.log(S[0][0]===S[4][0]);}}catch(e){{console.log(e.name);}}\n{builder}"
    );
    let constructor = format!("var replacement=[];var Array=function(){{return replacement;}};\n{builder}\nconsole.log(S[0][0]===S[0][1]);");
    script_runtime_equivalence(&[&preinit, &constructor], "reference-construction", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_script_completion_runtime_equivalence() -> Result<()> {
    script_runtime_equivalence(SCRIPT_COMPLETION_SOURCES, "script-completion", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_selector_projection_runtime_equivalence() -> Result<()> {
    let sources = [
        "function outer(){let x=7;function f(s){if(s===0)return x;return 0;}function inner(){let x=9;return f(0);}return inner();}outer();",
        "function outer(){let n=0;function f(s){if(++n&&s===1)return 1;if(s===0)return 2;return 3;}return [f(0),n];}outer();",
        "function outer(){function f(s,s){if(s===0)return 1;if(s===1)return 2;return 3;}return f(0,1);}outer();",
        "function f(s){if(s===0)return 1;return 2;}globalThis.f=()=>9;f(0);",
        "function outer(){var a=42;function f(s){if(s===a)return 1;if(s===0)return 2;return 3;}eval('a=0');return f(0);}outer();",
        "function outer(){function f(s,x,y){if(s===0)return (arguments[2]=9,y);return 0;}return f(0,1,2);}outer();",
        "function outer(){function f(s,x){if(s===0)return x+1;return 0;}let obj={valueOf(){events.push('coercion');return 7}};return f(0,obj);}outer();",
        "function outer(){function f(s,x,y){if(s===0)return x+1;return 0;}return f(0,7,events.push('arg'));}outer();",
        "function outer(){function f(s,x){if(s===0)return (x=7,x);return 0;}return f(0,events.push('arg'));}outer();",
        "function outer(){function f(s){if(s===0)return 1;return 2;function s(){}}return f(0);}outer();",
        "var a=42;function outer(){function f(s){if(s===a)return 1;if(s===0)return 2;return 3;}globalThis.a=0;return f(0);}outer();",
        "function outer(){let n=0;function f(s){if(s===0||++n)return 1;return 2;}return [f(0),n];}outer();",
        "function outer(){function f(s,x,y,z){if(s===0)return x;return 0;}return f(0,7,events.push(1),events.push(2));}outer();",
        "function outer(){function f(s,x){if(s===0)return x;return 0;}return f(0);}outer();",
        "function outer(){function f(s,x){if(s===0)return x;return 0;}return f(0,void events.push(1));}outer();",
        "function outer(a){var a=42;function f(s){if(s===a)return 1;if(s===0)return 2;return 3;}arguments[0]=0;return f(0);}outer(9);",
        "function outer(){function f(s,x){if(s===0)return x===0;return 0;}return f(0,(events.push('arg'),-0));}outer();",
    ];
    script_runtime_equivalence(&sources, "selector-projection", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_scalar_helper_cells_runtime_equivalence() -> Result<()> {
    let sources = [
        "function outer(){function f(x){var y=x+1;return (x=9)+y;}return f(2);}outer();",
        "function outer(){function f(x){var y=x;var x=9;return y+x;}return f(2);}outer();",
        "function outer(){function f(x){var y;var y=x+1;y++;return y;}return f(2);}outer();",
        "function outer(){function f(x){var y=x+1;var y;return y;}return f(2);}outer();",
        "function outer(){function f(x){let y=x+1;const z=y;y+=4;return z+y;}return f(2);}outer();",
        "function outer(){function f(x){let y=x;return (y+=3,y++ + y);}return f(2);}outer();",
        "function outer(){function f(x){let y=0;y ||= x;y &&= 7;return y;}return f(2);}outer();",
        "function outer(){function f(x,x){return x;}return [f(2),f(2,7)];}outer();",
        "function outer(){function f(){return typeof y;var y=1;}return f();}outer();",
        "function outer(){function f(x){return x;function x(){}}return typeof f(2);}outer();",
        "function outer(){function f(){return y;let y=7;}return f();}try{outer()}catch(e){e.name;}",
        "function outer(){function f(){const x=7;x=9;return x;}return f();}try{outer()}catch(e){e.name;}",
        "function f(x){return x+1}globalThis.f=x=>x+9;f(2);",
        "function outer(flag){if(flag){function f(x){return x+1}}try{return f(2)}catch(e){return e.name;}}[outer(false),outer(true)];",
        "function outer(flag){if(flag)function f(x){return x+1}try{return f(2)}catch(e){return e.name;}}[outer(false),outer(true)];",
        "function outer(){function f(x){return x+1}function f(x){return x+9}return f(2);}outer();",
        "function outer(){'use strict';{function f(x){return x+1}return f(2)}}outer();",
        "function outer(){let a;{function f(x){return x+1}a=f(2)}return a;}outer();",
        "function f(x){return x+9}function outer(a=f(2)){function f(x){return x+1}return a;}outer();",
        "function f(x){return x+9}function outer(a=()=>f(2)){function f(x){return x+1}return a();}outer();",
        "function outer(){function f(x){var arguments;return x;}return f(2);}outer();",
        "function outer(){function f(x){var arguments=7;return arguments;}return f(2);}outer();",
        "function outer(){function f(x){var y=x+1;return (x=9)+y;}return [f(2),f(7)];}outer();",
        "function outer(){function f(x){let y=x;return y &&= 7;}return [f(0),f(2)];}outer();",
        "function outer(){function f(x,y,z){return x+1;}return f(7,events.push(1),events.push(2));}outer();",
        "function outer(){function f(x){return (x=7,x);}return f(events.push('arg'));}outer();",
        "function outer(){function f(x){return x+1;}return f({valueOf(){events.push('coercion');return 7;}});}outer();",
    ];
    script_runtime_equivalence(&sources, "scalar-helper-cells", false)?;
    let heap_sources = [
        "function outer(){function index(x){let y=x;return (x=9,y);}let a=[0,0];for(let i=0;i<2;i++){a[index(i)]=7;}return a[0]+a[1];}outer();",
        "function outer(){function index(x,y){return x+y;}let a=[0,7];let i=0;index(i++,i++);return a[i-1];}outer();",
        "function outer(){function index(x){return x;}let a=[7];index(a[0]=9);return a[0];}outer();",
        "function outer(){function index(x){return x;}let a=[7];index(a);return a[0];}outer();",
        "function index(x){return x;}let a=[7];globalThis.index=()=>{a[0]=9;};index(0);a[0];",
        "function outer(flag){if(flag){function index(x){return x;}}let a=[7];index(0);return a[0];}try{outer(false)}catch(e){e.name;}",
        "function outer(){function index(x){return x%2;}let a=[[],[]];for(let i=0;i<2;i++){a[index(i)]=a[0];}return a[0]===a[1];}outer();",
        "function outer(){function index(x,y){return x;}let a=[7];index(0,a);return a[0];}outer();",
        "function outer(){function index(x){return (x=0,x);}let a=[7];index(a);return a[0];}outer();",
        "function outer(){function index(x){return x;}let a=[7];index(a[0]=9,a);return a[0];}outer();",
    ];
    script_runtime_equivalence(&heap_sources, "scalar-helper-heap", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_declarative_var_runtime_equivalence() -> Result<()> {
    let sources = [
        "function f(){var a=[7];var b=a;b[0]=9;return a[0];}f();",
        "function f(){var a=[7];var a;return a[0];}f();",
        "function f(){var a=[7];{var b=a;}b[0]++;return a[0];}f();",
        "function f(){var a=[1];for(var i=0;i<2;i++){a[0]++;}return a[0];}f();",
        "function f(p){'use strict';var p=[7];arguments[0]=[9];return p[0];}f([]);",
        "function f(p){var p=[7];arguments[0]=[9];return p[0];}f([]);",
        "function f(p){p=[7];arguments[0]=[9];return p[0];}f([]);",
        "function f(p){var p=[7];var args=arguments;args[0]=[9];return p[0];}f([]);",
        "function f(){var a=[9];try{throw [];}catch(a){var a=[7];events.push(a[0]);}return a[0];}f();",
        "function f(){var a=[7];function mutate(){a[0]=9;}mutate();return a[0];}f();",
        "function f(){var a=[7];eval('a=[9]');return a[0];}f();",
        "Object.defineProperty(globalThis,'a',{get(){return [9]},set(value){events.push(value[0])},configurable:true});var a=[7];a[0];",
    ];
    // The public safe-deob entry point rejects dynamic with scopes.
    // The lower-level heap tests separately verify target-resolution facts.
    for source in [
        "function f(){var a=[7];with({a:[2]}){var a=[9];events.push(a[0]);}return a[0];}f();",
        "function f(){var a=[7];with(new Proxy({},{has(t,k){if(k==='b')a[0]=9;return false;}})){var b=a[0];return b;}}f();",
    ] {
        let result = deobfuscate_source(
            source,
            "declarative-var-with",
            SourceMode::Auto,
            16,
            false,
            &budget("declarative-var-with"),
        );
        let Err(error) = result else {
            return Err(anyhow!("dynamic with scope was unexpectedly accepted"));
        };
        assert!(error.to_string().contains("dynamic-with-scope"), "{error}");
    }
    script_runtime_equivalence(&sources, "declarative-var", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_callable_capture_runtime_equivalence() -> Result<()> {
    let sources = [
        "let f=x=>[x];let a=f(7);a[0];",
        "let f=function(x){return [x];};let alias=f;let a=alias(7);a[0];",
        "let f=function inner(x){return [x];};let a=f(7);a[0];",
        "let a=[7];let f=()=>{a[0]=9;return a;};let b=f();[a[0],b[0],a===b];",
        "let a=[7];let f=()=>a;a=[9];let b=f();b[0];",
        "let fs=[x=>[x]];let a=fs[0](7);a[0];",
        "let f=x=>[x];let a=f((f=x=>[9],7));a[0];",
        "let f=x=>[x];let a=f(7);let b=f(9);[a[0],b[0]];",
        "let a=[7];let f=()=>[a[0]];let b=f();a[0]=9;let c=f();[b[0],c[0]];",
        "let f;{let x=7;f=()=>[x];}let a=f();a[0];",
        "let f;for(let i=0;i<2;i++){if(i===0)f=()=>[i];else{let a=f();events.push(a[0]);}}",
        "let a;for(let i=0;i<2;i++){let f=()=>[i];a=f();}a[0];",
        "let f;for(let i=0;i<2;i++)if(i===0)f=()=>[i];else{let a=f();events.push(a[0]);}",
        "let a;for(let i=0,f=()=>[i];i<1;i++){a=f();}a[0];",
        "let f;let a;for(let i=0;i<2;f=()=>[i],i++){if(i===1)a=f();}a[0];",
        "let a;for(let i=0;i<2;i++){let x=i;let f=()=>[x];a=f();}a[0];",
        "let f=(()=>{let x=7;return ()=>[x];})();let a=f();a[0];",
        "let a=[7];let f=()=>{events.push('effect');return [9];};let b=f();[b[0],a[0]];",
        "let f=()=>[7];let a=f;f=()=>[9];let b=a();b[0];",
        "let f=()=>[7];let a=[typeof f,typeof {}];[a[0],a[1]];",
        "let f=function(){};let a=[7];events.push(delete f.prototype);a[0];",
        "let f=()=>[7];let a={...f,x:7};a.x;",
        "let f=()=>[7];let a={f};let b=a.f();b[0];",
        "let a=[7];let f=()=>[a[0]];let b=f((a[0]=9,0));b[0];",
        "let f=()=>7;let g=f;let h=()=>7;[f===g,f===h,[f][0]===f];",
        "let f=function(){return [this.x];};let o={x:9,f};let a=o.f();a[0];",
        "let make=()=>{let a=[7];return ()=>a[0]++;};let f=make();let g=make();[f(),g(),f()];",
        "let f=()=>[7];let a=f((events.push('arg'),f=()=>[9]));a[0];",
        "let f=(x=>{return [x];});let a=f(7);let b=f(9);[a[0],b[0],a===b];",
        "let f=function self(n){return n?self(n-1):[7];};let a=f(2);a[0];",
        "let a=[7];let f=()=>[7];let o={get f(){a[0]=9;return f;}};let b=o.f();[a[0],b[0]];",
        "let f=null;let a=[7];f?.(a[0]=9);a[0];",
    ];
    script_runtime_equivalence(&sources, "callable-capture", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_completion_paths_runtime_equivalence() -> Result<()> {
    let sources = [
        "7; outer:{break outer;}",
        "outer:{7;break outer;}",
        "7; while(false){}",
        "let i=0;while(i++<2){i;}",
        "let i=0;while(i++<2){if(i===1){3;}else{}}",
        "do{3;break;}while(false);",
        "for(let i=0;i<2;i++){3;continue;}",
        "for(let i=0;i<2;i++){3;if(i===1)continue;}",
        "switch(1){case 1:3;case 2:break;}",
        "7;switch(3){case 1:3;case 2:break;}",
        "7;switch(1){case 1:break;}",
        "outer:for(;;){7;break outer;}",
        "let i=0;outer:inner:while(i++<2){5;continue outer;}",
        "let i=0;while(i++<2){switch(i){case 1:3;break;case 2:break;}}",
        "for(let i=0;i<2;i++){if(i===0){3;}else{;}}",
        "for(let i=0;i<2;i++){{let x;}}",
        "let i=0;for(;i<2;99){i++;i;}",
        "let i=0;do{i++;i;}while(i<3);",
        "outer:{switch(1){case 1:9;break outer;}}",
        "let a=[0],i=0;while(i<3){a[0]+=2;i++;}a[0];",
        "let a=[0],i=0;do{a[0]+=2;i++;}while(i<3);a[0];",
        "let a=[0];for(;;){a[0]=7;break;}a[0];",
        "let a=[0];for(let i=0;i<4;i++){if(i===1)continue;a[0]+=i;}a[0];",
        "let a=[0];do{a[0]=7;break;}while((a[0]=9,true));a[0];",
        "let a=[0],i=0;outer:while(i<3){i++;for(let j=0;j<3;j++){if(j===1)continue outer;a[0]++;}a[0]=99;}a[0];",
        "let a=[0];outer:{a[0]=7;break outer;a[0]=9;}a[0];",
        "let a=[0];outer:inner:for(let i=0;i<3;i++){a[0]++;continue outer;}a[0];",
        "let a=[0];outer:for(let i=0;i<3;i++){for(;;){a[0]=7;break outer;}a[0]=9;}a[0];",
        "function f(flag){let a=[0];for(let i=0;i<1;i++){a[0]=7;if(flag)break;}return a[0];}[f(true),f(false)];",
        "function f(flag){let a=[0];for(let i=0;i<1;i++){if(flag){a[0]=7;break;}a[0]=9;}return a[0];}[f(true),f(false)];",
        "function f(flag){let a=[0];for(let i=0;i<2;i++){a[0]=7;if(flag)continue;a[0]=7;}return a[0];}[f(true),f(false)];",
        "let a=[0];switch(2){case (a[0]=1,1):a[0]=99;break;default:a[0]=99;break;case (a[0]=2,2):a[0]=7;break;}a[0];",
        "let a=[0];switch(1){case 1:a[0]=7;case 2:a[0]+=2;break;default:a[0]=99;}a[0];",
        "let a=[0];for(let i=0;i<3;i++){switch(i){case 0:continue;case 1:a[0]+=7;break;default:a[0]+=9;}a[0]++;}a[0];",
        "let a=[0];switch(3){case 1:a[0]=9;break;}a[0];",
        "let f=()=>{let a=[0];while(true){a[0]=7;return a;}};let r=f();r[0];",
        "function outer(flag){function f(){let a=[0];for(let i=0;i<1;i++){if(flag)return [7];a[0]=7;}return a;}let r=f();return r[0];}[outer(true),outer(false)];",
        "function outer(flag){function f(){let a=[0];for(let i=0;i<1;i++){if(flag)return [9];a[0]=7;}return a;}let r=f();return r[0];}[outer(true),outer(false)];",
        "let g;for(let i=0;i<3;i++){if(i===1){g=()=>[i];continue;}}let r=g();r[0];",
        "let a=[7];while(true){try{break;}finally{a[0]=9;}}a[0];",
        "function f(flag){let a=[7];switch(flag){case 1:a[0]=9;}return a[0];}[f(1),f(2)];",
        "let a=[0];try{outer:while(true){try{a[0]=7;break outer;}finally{a[0]=9;throw 1}}}catch(e){events.push(e)}a[0];",
        "let a=[0];let i=0;do{events.push(i);i++;if(i===1)continue;a[0]++;}while(i<3);a[0];",
        "let a=[0];outer:{switch(1){case 1:a[0]=7;break outer;}a[0]=9;}a[0];",
        "let a=[0];function f(flag){while(true){if(flag){a[0]=9;throw 1;}a[0]=7;return a;}}try{f(true)}catch(e){events.push(e)}f(false)[0];",
        "let a=[0];for(let i=0;i<2;i++){switch(i){case 0:let x=7;continue;case 1:let y=9;a[0]=y;}}a[0];",
    ];
    let mut comparisons = Vec::with_capacity(sources.len() * 2);
    for (index, source) in sources.iter().enumerate() {
        let label = format!("completion-paths-{index}");
        let result =
            deobfuscate_source(source, &label, SourceMode::Auto, 48, false, &budget(&label))?;
        comparisons.push(script_observations::Comparison {
            label: format!("{label}-eval"),
            original: format!("eval({})", serde_json::to_string(source)?),
            rewritten: format!("eval({})", serde_json::to_string(&result.source)?),
        });
        comparisons.push(script_observations::Comparison {
            label,
            original: (*source).to_owned(),
            rewritten: result.source,
        });
    }
    script_observations::compare_pairs("completion-paths", &comparisons, false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_string_own_runtime_equivalence() -> Result<()> {
    let sources = [
        "let s='abc';[s.length,s[0],s[2]];",
        "let s='é😀z';[s.length,s[0],s[1],s[2],s[3]];",
        "let s='😀',a=[7];[s[0],s[1],a[0]];",
        "let s='abc';[s[-0],s[1n],s['01'],s['-0'],s[3]];",
        "let s='abc',a=[7];let r=[s?.length,s?.[1]];[r[0],r[1],a[0]];",
        "let {length:l,0:x,...rest}='abc';[l,x,rest[1],rest[2]];",
        "let s='abc',a=[7];[s[(a[0]=9,0)],a[0]];",
        "let s='abc',old=s;let r=s[(s='xyz',0)];[r,s,old];",
        "Object.defineProperty(String.prototype,'01',{get(){events.push('get');return 9},configurable:true});let s='abc';[s.length,s[0],s['01']];",
        "Object.defineProperty(String.prototype,'3',{get(){events.push('get');return 9},configurable:true});let s='abc';[s[2],s[3]];",
        "Object.defineProperty(String.prototype,'0',{get(){events.push('get');return 9},configurable:true});let s='abc';[s.length,s[0]];",
        "let s='abc',a=[7];let k={toString(){a[0]=9;return '0'}};[s[k],a[0]];",
    ];
    script_runtime_equivalence(&sources, "string-own-properties", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_optional_chain_runtime_equivalence() -> Result<()> {
    let sources = [
        "let a=null,b=[7];let r=[a?.[b[0]=9].x];[r[0],b[0]];",
        "let a={x: 7},b=[0];let r=[a?.[(b[0]=9,'x')]];[r[0],b[0]];",
        "let a={x: null},b=[7];let r=[a?.x?.[b[0]=9].y];[r[0],b[0]];",
        "let a={x: {y: 7}};let r=[a?.x.y];r[0];",
        "let a={x: 7,f(){return [this.x]}};let r=a?.f();r[0];",
        "let a={x: 7,f(){return [this.x]}};let r=a.f?.();r[0];",
        "let a={x: 7,f(){return [this.x]}};let r=a?.f?.();r[0];",
        "let a={x: 7,f(){return [this.x]}};let r=(a?.f)();r[0];",
        "let a={x: 7,f(){return [this.x]}};let r=(a?.f)?.();r[0];",
        "let a=null,b=[7];let r=[a?.f(b[0]=9).x];[r[0],b[0]];",
        "let a={f: null},b=[7];let r=[a.f?.(b[0]=9).x];[r[0],b[0]];",
        "let a={x: 7,f(){events.push('call');return null}},b=[7];let r=[a?.f()?.[b[0]=9]];[r[0],b[0]];",
        "let f=(x)=>[x];let a=[7];let r=f?.(a[0]=9);[r[0],a[0]];",
        "let a={x: 7,f(x){return [this.x,x]}};let old=a;let r=a?.f((a={x: 9},11));[r[0],r[1],old.x];",
        "let a=null,b=[7];let r=[delete a?.[b[0]=9]];[r[0],b[0]];",
        "let a={__proto__: null,x:7};let r=[delete a?.x];[r[0],a.x];",
        "let a={__proto__: null,get x(){throw 1}};let r=[delete a?.x];[r[0],a.x];",
        "let a={f(){events.push('call');return [7]}};let r=[delete a?.f()];r[0];",
        "let a=[7];let f=x=>{x?.[a[0]=9]};f(null);a[0];",
        "let a=[7];let f=x=>{x?.[a[0]=9]};f({});a[0];",
        "let a=null,b=[7];try{(a?.x)[b[0]=9]}catch(e){events.push(e.name)}b[0];",
        "let a=null,b=[7];try{(a?.f)(b[0]=9)}catch(e){events.push(e.name)}b[0];",
        "let a={x: 7,f(){return [this.x]}};let g=(0,a?.f);try{g()}catch(e){events.push(e.name)}",
        "let a=[7],o={get f(){a[0]=9;return null}};let r=[o.f?.(a[0]=11)];[r[0],a[0]];",
        "let a=[7];for(let i=0;i<2;i++){let o=i===0?null:{x: 9};o?.[(a[0]=i,'x')]}a[0];",
        "let a={x: 7,f(){return [this.x]}};let r=(a?.f)(...(events.push('spread'),[]));r[0];",
    ];
    script_runtime_equivalence(&sources, "optional-chains", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_destructuring_assignment_runtime_equivalence() -> Result<()> {
    let sources = [
        "let a,b;({x: a,y:b}={x: 7,y:9});let r=[a,b];[r[0],r[1]];",
        "let x;({x}={x: 7});let r=[x];r[0];",
        "let x;({x=7}={x: void 0});let r=[x];r[0];",
        "let x;({x=7}={x: null});let r=[x];r[0];",
        "let x;({x: {y:x=7}}={x: {y:void 0}});let r=[x];r[0];",
        "let a=[1],s={x: 7};({x: a[(s.x=9,0)]}=s);a[0];",
        "let s={x: 7},a=[1],old=a;({x: a[(a=[9],0)]}=s);[old[0],a[0]];",
        "let a=[0],old=a,s={x: void 0};({x: a[0]=(a=[9],7)}=s);[old[0],a[0]];",
        "let a=[0,null],s={x: 7,y:8};({x: a[0],...a[(s.y=9,1)]}=s);[a[0],a[1].y];",
        "let s={x: 7,y:8},a,r;({x: a,...r}=s);let q=[a,r.y];[q[0],q[1]];",
        "let s={x: 7},a;let r=({x: a}=s);[r===s,r.x];",
        "let s={x: 7,y:8},a=[0];({x: a[0],y:a[0]}=s);a[0];",
        "let s={x: 7},a=[0];({[(s.x=9,'x')]:a[0]}=s);a[0];",
        "let a=[[7]],s={x: 9};let k={toString(){a[0]=[11];return 'x'}};({[k]:a[0][0]}=s);a[0][0];",
        "let a=[7],s={get x(){a[0]=9;return 8}};let x;({x}=s);a[0];",
        "let a=[7];a[Symbol.iterator]=function*(){a[0]=9;yield 11};let x;[x]=a;[x,a[0]];",
        "let f=function(x){({a: arguments[0]}={a: 9});return [x]};let r=f(7);r[0];",
        "let a=[0],s={get x(){events.push('get');return 7}};({[(events.push('key'),'x')]:a[(events.push('target'),0)]}=s);a[0];",
        "let a=[0],s={get y(){events.push('get');return 9}};({...a[(events.push('target'),0)]}=s);a[0].y;",
        "let a=[0],s={x: void 0};({x: a[(events.push('target'),0)]=(events.push('default'),7)}=s);a[0];",
        "let a=[0];try{({x: a[(events.push('target'),0)]}=null)}catch(e){events.push(e.name)}a[0];",
        "let a=[0],s={x: 7};const x=0;try{({x,y:a[0]}=s)}catch(e){events.push(e.name)}a[0];",
        "let a=[0],s={x: 7,y:8};({x: a[0],...s}=s);[a[0],s.x,s.y];",
        "let s={x: 7};let r;({x: r}=(s={x: 9}));r;",
    ];
    script_runtime_equivalence(&sources, "object-assignment-patterns", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_arguments_objects_runtime_equivalence() -> Result<()> {
    let sources = [
        "let f=function(a){arguments[0]=9;return [a]};let r=f(7);r[0];",
        "let f=function(a){a=9;return arguments};let r=f(7);r[0];",
        "let f=function(a,a){a=9;return arguments};let r=f(7,8);[r[0],r[1]];",
        "let f=function(a,a){a=9;return arguments};let r=f(7);[r[0],r[1]];",
        "let f=function(a){delete arguments[0];a=9;return [a,arguments[0]]};let r=f(7);[r[0],r[1]];",
        "let f=function(a){delete arguments[0];Object.defineProperty(arguments,'0',{value:8,writable:true});a=9;return [a,arguments[0]]};let r=f(7);[r[0],r[1]];",
        "let f=function(a){'use strict';arguments[0]=9;return [a,arguments[0]]};let r=f(7);[r[0],r[1]];",
        "let f=function(a=1){a=9;return arguments};let r=f(7);r[0];",
        "let f=function(a,...rest){a=9;return arguments};let r=f(7,8);[r[0],r[1],r.length];",
        "let f=function(a){return [arguments,()=>[a]]};let p=f(7);p[0][0]=9;let r=p[1]();r[0];",
        "let f=function(a){return [arguments,()=>[a]]};let p=f(7);for(let i=0;i<256;i++){let x=[i];}p[0][0]=9;let r=p[1]();r[0];",
        "let f=function(a){let b={__proto__: arguments};b[0]=9;return [a,b[0]]};let r=f(7);[r[0],r[1]];",
        "let f=function(a){a=9;return {__proto__:null,...arguments}};let r=f(7);[r[0],r.length,r.callee];",
        "let f=function(a){let b={...arguments};a=9;return b};let r=f(7);r[0];",
        "let f=function(a){let {0:x,...r}=arguments;return {__proto__:null,...r}};let r=f(7,8);[r[0],r[1],r.length];",
        "let f=function(a){var arguments;return arguments};let r=f(7);r[0];",
        "let f=function(a){let b=arguments;arguments=[9];b[0]=8;return [a,arguments[0]]};let r=f(7);[r[0],r[1]];",
        "let f=function(a){return ()=>arguments};let g=f(7);let r=g();r[0];",
        "let f=function(a,g=()=>arguments){var arguments=[9];return g};let g=f(7);let r=g();r[0];",
        "let f=function(arguments){return arguments};let r=f([7]);r[0];",
        "let f=function(a){return arguments.callee};let g=f(7);let r=[g===f];r[0];",
        "let f=function(a){'use strict';return arguments.callee};try{f(7)}catch(e){events.push(e.name)}",
        "let f=function(a){'use strict';return {__proto__:null,...arguments}};let r=f(7);[r[0],r.length,r.callee];",
        "let f=function(a){function a(){return 9}return arguments};let r=f(7);r[0]();",
        "let f=function(a){return [arguments,()=>[a]]};let p=f(7),q=f(8);let o=flag=>flag?p[0]:q[0];let g=flag=>{o(flag)[0]=9;return [p[1]()[0],q[1]()[0]]};g(true);g(false);",
        "let f=function(a){return [arguments,()=>[a]]};let p=f(7);Object.defineProperty(p[0],'0',{value:8,writable:false});p[0][0]=9;let r=p[1]();r[0];",
        "let f=function(a=arguments[0]){return [a,arguments.length]};let r=f(7);[r[0],r[1]];",
        "let f=function(a){arguments.length=99;return arguments};let r=f(7);[r.length,r[0]];",
        "let f=function(a){delete arguments.length;arguments.length=99;return {...arguments}};let r=f(7);[r.length,r[0]];",
        "let outer=[7];let escaped=(function(){var arguments;return [arguments,outer[0]];})();outer[0]=9;escaped[0].callee()[1];",
        "let outer=[7];let escaped=(function(){var arguments;return [arguments,outer[0]];})();outer[0]=9;let result=escaped[0].callee();result[1];",
    ];
    script_runtime_equivalence(&sources, "arguments-objects", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_parameter_environments_runtime_equivalence() -> Result<()> {
    let sources = [
        "let f=(a=7,b=a+2)=>[a,b];let r=f();[r[0],r[1]];",
        "let f=(a=7)=>[a];let r=f(void 0);r[0];",
        "let f=(a=7)=>[a];let r=f(null);r[0];",
        "let n=0;let f=(a=(n+=1),b=(n+=2))=>[a,b,n];let r=f();[r[0],r[1],r[2]];",
        "let n=0;let f=(a=(n+=1),b=(n+=2))=>[a,b,n];let r=f(7,9);[r[0],r[1],r[2]];",
        "function outer(x){let a=[7];let f=(v=(a[0]=9))=>[v];f(x);return a[0];}[outer(void 0),outer(1)];",
        "function outer(x){let a=[7];let f=(v=(a[0]=7))=>[v];f(x);return a[0];}[outer(void 0),outer(1)];",
        "let f=(...a)=>a;let b=f(7,9);[b[0],b[1],b.length];",
        "let f=(a,...rest)=>[a,rest.length,rest[0]];let r=f(7,9);[r[0],r[1],r[2]];",
        "let f=(...a)=>a;let b=f();b.length;",
        "let f=(a=7,...rest)=>[a,rest.length];let r=f(void 0,9);[r[0],r[1]];",
        "let o={x:7,f:function(a=this.x){return [a]}};let r=o.f();r[0];",
        "let f=(a=7)=>{var x;return [x,a]};let r=f();[r[0],r[1]];",
        "let f=(a=7,g=()=>[a])=>{var a=9;return g};let r=f()();r[0];",
        "let f=(a=7,g=()=>[a])=>{a=9;return g};let r=f()();r[0];",
        "let f=(g=()=>[a],a=7)=>{var a=9;return g};let r=f()();r[0];",
        "let f=(a=7,g=()=>[a])=>{var a;return [a,g]};let p=f();let r=p[1]();[p[0],r[0]];",
        "let f=(a=7,g=()=>[a])=>{var a;let h=()=>[a];a=9;return [g,h]};let p=f();let r=p[0](),s=p[1]();[r[0],s[0]];",
        "let f=(a=7,g=()=>[a])=>{if(false){try{}catch(a){var a=11}}a=9;return g;};let r=f()();r[0];",
        "let f=function(a=7,g=()=>[a]){function a(){return 9}return g;};let r=f()();r[0];",
        "let f=function(a=7,g=()=>[a]){function a(){return [9]}let p=a();return [g,p];};let p=f();let r=p[0](),s=p[1];[r[0],s[0]];",
        "let a=7;let f=(g=()=>[a])=>{var a=9;return g};let r=f()();r[0];",
        "let f=(a=7,g=()=>[a])=>{var a=9;return g};let g=f(),h=f(11);let r=g(),s=h();[r[0],s[0]];",
        "let f=(a=7,g=()=>[a])=>{var a=9;return g};let g=f();for(let i=0;i<256;i++){let a=[i];}let r=g();r[0];",
        "let o={x:7,f:function(g=()=>[this.x]){return g}};let r=o.f()();r[0];",
        "let f=({x,y:z=9})=>[x,z];let r=f({x:7,y:void 0});[r[0],r[1]];",
        "let f=({x:{y=7}})=>[y];let r=f({x:{y:void 0}});r[0];",
        "let f=({x,...rest})=>[x,rest.y];let r=f({x:7,y:9});[r[0],r[1]];",
        "let f=({x,...rest})=>rest;let r=f({x:7,y:9});r.y;",
        "let f=({x})=>{var x;return [x]};let r=f({x:7});r[0];",
        "let f=({['x']:a,b=a})=>[a,b];let r=f({x:7,b:void 0});[r[0],r[1]];",
        "let a=[7];let f=({x})=>[x];f({get x(){a[0]=9;return 7}});a[0];",
        "let f=([x])=>[x];let a=[7];a[Symbol.iterator]=function*(){yield 9};let r=f(a);r[0];",
        "let {x,y:z=9}={x:7,y:void 0};let a=[x,z];[a[0],a[1]];",
        "const {x,...r}={x:7,y:9};r.y;",
        "function outer(){var {x,...r}={x:7,y:9};return r.y;}outer();",
        "var {x}={x: 7};let r=[x];r[0];",
        "let a={x:7,y:9};let {x:v,...r}=a;let b=[v,r.y];[b[0],b[1]];",
        "function outer(){let g=f;function f(){return [7]}function f(){return [9]}let r=g();return r[0];}outer();",
        "let f=(a=b,b=7)=>[a];try{f()}catch(e){events.push(e.name)}f(9)[0];",
        "let f=(a=7,g=()=>a)=>{eval('var a=9');return [a,g()]};let r=f();[r[0],r[1]];",
        "let f=(a=7,g=()=>a)=>{var a;return [a,g()]};let r=f();[r[0],r[1]];",
        "let f=function self(a=self){return [a]};let r=f();r[0]===f;",
        "let f=function(a=7){return [arguments[0],a]};let r=f();[r[0],r[1]];",
        "let f=({x=()=>y},y=7)=>x;let r=f({x:void 0})();r;",
        "let a=[7];let f=({x=(a[0]=9),...r})=>r;let r=f({x:void 0,y:a});[r.y[0],a[0]];",
        "let o={x:7,y:9,get z(){events.push('get');return 11}};let {z,...r}=o;[z,r.x,r.y];",
        "let f=({x},y=()=>x)=>y;let g=f({x: 7});g();",
        "let f=(...{length})=>[length];let r=f(1,2,3);r[0];",
    ];
    script_runtime_equivalence(&sources, "parameter-environments", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_alternative_call_targets_runtime_equivalence() -> Result<()> {
    let sources = [
        "function outer(flag){let f=flag?()=>[7]:()=>[7];let a=f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let f=flag?()=>[7]:()=>[9];let a=f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let a=[0];let f=flag?()=>{a[0]=7}:()=>{a[0]=7};f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let a=[0];let f=flag?()=>{a[0]=7}:()=>{a[0]=9};f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let a=[0];let f=flag?()=>{a[0]=7}:()=>{};f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let f=flag?x=>[x]:x=>[x];let n=0;let a=f(++n);return [a[0],n];}[outer(true),outer(false)];",
        "function outer(flag){let a=[7];let f=flag?()=>a:()=>a;let b=f();b[0]=9;return [a[0],a===b];}[outer(true),outer(false)];",
        "function outer(flag){let make=x=>()=>[x];let f=flag?make(7):make(7);let a=f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let make=x=>()=>[x];let f=flag?make(7):make(9);let a=f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let f=flag?()=>[7]:()=>{events.push('effect');return [7]};let a=f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let a=[7];let f=flag?()=>{}:()=>{events.push(a);a[0]=9};f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let a=[7];let f=flag?()=>a:{};let b=f();return b[0];}try{outer(false)}catch(e){events.push(e.name)}outer(true);",
        "function outer(flag){let o={x:7,f:flag?function(){return [this.x]}:function(){return [this.x]}};let a=o.f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let f=flag?()=>[7]:()=>[7];let a=f((f=()=>[9],0));return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let make=()=>{let a=[7];return ()=>a;};let f=flag?make():make();let a=f();return a[0];}[outer(true),outer(false)];",
        "function outer(flag){let a=[7];let f=flag?()=>{a[0]=9;return a}:()=>{a[0]=9;return a};let b=f();return [a[0],b[0]];}[outer(true),outer(false)];",
        "function outer(flag){let f=flag?()=>[7]:()=>[7];let a=f(),b=f();return a===b;}[outer(true),outer(false)];",
        "function outer(flag){let a=[7],b=[9];let o=flag?{x:a,f(){return this.x}}:{x:b,f(){return this.x}};let r=o.f();return r[0];}[outer(true),outer(false)];",
        "function outer(flag){let make=x=>function self(){return [x,self]};let f=flag?make(7):make(9);let a=f();return [a[0],a[1]===f];}[outer(true),outer(false)];",
        "function outer(flag){let a=[7];let f=flag?()=>{throw 1}:()=>a;let b=f();return b[0];}try{outer(true)}catch(e){events.push(e)}outer(false);",
        "function outer(flag){let a=[7];let f=flag?()=>a:async()=>a;let b=f();return b[0];}[outer(true),outer(false)];",
        "function outer(flag){let a=[7];let f=flag?()=>a:()=>a;let r=f((events.push('arg'),a[0]=9));return r[0];}[outer(true),outer(false)];",
    ];
    script_runtime_equivalence(&sources, "alternative-call-targets", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_receiver_cell_runtime_equivalence() -> Result<()> {
    let sources = [
        "let o={x:7,f:function(){return [this.x]}};let a=o.f();a[0];",
        "let o={x:7,f(){return [this.x]}};let a=o.f();a[0];",
        "let o={x:7,f(){this.x++;return this;}};let a=o.f();[a.x,o.x,a===o];",
        "let o={x:7,f(){return [this.x]}};let a=o.f((o={x: 9},0));a[0];",
        "let o={x:7,f(){return [this.x]}};let a=o[(o={x: 9},'f')]();a[0];",
        "let o={x:7,f(){return [this.x]}};let a=(o.f)();a[0];",
        "let f=function(){'use strict';return [this===void 0]};let a=f();a[0];",
        "let o={x:7,f(){'use strict';return [this===void 0]}};let a=(0,o.f)();a[0];",
        "globalThis.x=11;let o={x:7,f(){return [this.x]}};let a=(0,o.f)();a[0];",
        "let o={x:7,f(){return [this.x]}};let p={x:9,f:o.f};let a=o.f(),b=p.f();[a[0],b[0]];",
        "let o={x:7,f(){return [this.x]}};let a=o.f((o.x=9,0));a[0];",
        "let o={x:7,f(){return [this.x]}};let a=o.f((events.push('arg'),o.x=9));a[0];",
        "let o={x:7,f(){'use strict';let g=function(){return [this===void 0]};return g();}};let a=o.f();a[0];",
        "let o={x:7,f(){return ()=>[this.x]}};let g=o.f();o.x=9;let a=g();a[0];",
        "let o={x:7,f(){return {x:9,g:()=>[this.x]}}};let p=o.f();let a=p.g();a[0];",
        "let o={x:7,f(){return ()=>[this.x]}};let p={x:9,f:o.f};let g=o.f(),h=p.f();let a=g(),b=h();[a[0],b[0]];",
        "let o={x:7,f(){return ()=>[this.x]}};let g=o.f();o={x: 9};for(let i=0;i<256;i++){let a=[i];}let a=g();a[0];",
        "let o={x:7,f(){return [()=>this.x,()=>{this.x=9}]}};let p=o.f();p[1]();let a=[p[0]()];a[0];",
        "let o={x:7,f(){return ()=>[this.x]}};let g=o.f();events.push(g);let a=g();a[0];",
        "globalThis.x=11;let o={x:7,f:()=>[this.x]};let a=o.f();a[0];",
        "let o={x:7,f(){return class{ x=9; g=()=>[this.x];};}};let C=o.f();let a=new C().g();a[0];",
        "let o={x:7,f(){return class{static x=9;static g=()=>[this.x];};}};let C=o.f();let a=C.g();a[0];",
        "let o={x:7,f(){return [this.x]}};let p={x:9,f:o.f};let a=(true?p.f:o.f)();a[0];",
        "let o={x:7,f(){return [this.x]}};let a=(o.f=o.f)();a[0];",
        "let o={x:7,f(){return [this.x]}};let a=o.f((o.f=()=>[9],0));a[0];",
    ];
    script_runtime_equivalence(&sources, "receiver-cell", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_hoisted_callable_cells_runtime_equivalence() -> Result<()> {
    let sources = [
        "function outer(){let f=make;function make(x){return [x];}let a=f(7);return a[0];}outer();",
        "function outer(){function make(){let x=7;function f(){return [x++];}return f;}let f=make();let a=f(),b=f();return [a[0],b[0]];}outer();",
        "function outer(){function f(){return [7]}let old=f;f=()=>[9];let a=old(),b=f();return [a[0],b[0]];}outer();",
        "function outer(){let a=f();function f(){return [7];}return a[0];}outer();",
        "function outer(){'use strict';let f;{let x=7;f=inner;function inner(){return [x];}}let a=f();return a[0];}outer();",
        "function outer(){'use strict';let fs=[null,null];for(let i=0;i<2;i++){fs[i]=f;function f(){return [i];}}let a=fs[0](),b=fs[1]();return [a[0],b[0]];}outer();",
        "function outer(){function f(){return [7];}let g=f;let a=g((f=()=>[9],0));return a[0];}outer();",
        "function outer(){function f(){return [7];}let g=f;events.push(g);let a=g();return a[0];}outer();",
        "function outer(n){'use strict';switch(n){case 0:f=()=>[9];case 1:let a=f();return a[0];function f(){return [7];}}}[outer(0),outer(1)];",
        "function outer(){function f(){return [7];}f=()=>[9];function g(){return f();}let a=g();return a[0];}outer();",
        "function outer(){function f(){return [7];}let a=f((f=()=>[9],0));let b=f();return [a[0],b[0]];}outer();",
        "function outer(){function f(){}let g=f;return [f===g,f===(events.push('x'),f)];}outer();",
        "function outer(){function make(){function f(){}return f;}let a=make(),b=make();return a===b;}outer();",
        "function outer(){function f(){return [7]}function f(){return [9]}let a=f();return a[0];}outer();",
        "function outer(f){function f(){return [7]}let a=f();return a[0];}outer(()=>[9]);",
        "function outer(){function f(){return [7];}eval('f=()=>[9]');let a=f();return a[0];}outer();",
        "function outer(){if(false){function f(){return [7]}}return typeof f;}outer();",
        "let f=function self(self){return [self];};let a=f(7);a[0];",
        "let f=function self(){var self=7;return [self];};let a=f();a[0];",
    ];
    script_runtime_equivalence(&sources, "hoisted-callable-cells", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_instance_cell_runtime_equivalence() -> Result<()> {
    let sources = [
        "let make=x=>()=>[x];let f=make(7),g=make(9);let a=f(),b=g();[a[0],b[0]];",
        "let make=()=>{let x=0;return [()=>[x++],()=>[x]]};let pair=make();let a=pair[0](),b=pair[1]();[a[0],b[0]];",
        "let fs=[null,null,null];for(let i=0;i<3;i++)fs[i]=()=>[i];let a=fs[0](),b=fs[1](),c=fs[2]();[a[0],b[0],c[0]];",
        "function outer(){let fs=[null,null,null];for(var i=0;i<3;i++)fs[i]=()=>[i];let a=fs[0](),b=fs[1](),c=fs[2]();return [a[0],b[0],c[0]];}outer();",
        "let make=()=>{let a=[7];return ()=>[a[0]++];};let f=make();let g=make();let a=f(),b=g(),c=f();[a[0],b[0],c[0]];",
        "let f=()=>{let x=[7];return ()=>x;};let g=f();for(let i=0;i<256;i++){let garbage=[i];}let a=g();a[0];",
        "let f=()=>{let x=[7];return [()=>x,()=>{x[0]=9}];};let pair=f();let a=pair[0]();pair[1]();a[0];",
        "let f=()=>{let x=[7];return ()=>x;};let g=f();events.push(g);let a=g();a[0];",
        "let f=()=>{let x=7;return ()=>[x];};let g=f();let a=g();let b=f()();[a[0],b[0]];",
        "function outer(){function f(n){let a=[n];if(n){let b=f(n-1);return [a[0]+b[0]];}return a;}let r=f(3);return r[0];}outer();",
        "let f=function self(n){return n?self(n-1):[7];};let a=f(2);a[0];",
        "let f=n=>n?f(n-1):[7];let a=f(2);a[0];",
        "function outer(){let a=[0];function f(n){if(n)g(n-1);a[0]++;}function g(n){if(n)f(n-1);a[0]++;}f(4);return a[0];}outer();",
        "let make=x=>{let f=()=>[x];return [f,()=>{let a=make(x+1);return a[0]();}]};let a=make(7);let b=a[1]();let c=a[0]();[b[0],c[0]];",
        "let f=n=>{let x=[n];if(n)f(n-1);return x;};let a=f(3);a[0];",
        "let f=()=>{let x=7;return [()=>[x],v=>{x=v}];};let pair=f();let a=pair[0]();pair[1](9);let b=pair[0]();[a[0],b[0]];",
        "function outer(flag){let f=(()=>{let x=[7];return ()=>x;})();if(flag){events.push(f);}let a=f();return a[0];}[outer(true),outer(false)];",
        "let f=()=>{let x=[7];return ()=>x;};let a=f(),b=f();let c=a();c[0]=9;let d=b();[c[0],d[0]];",
    ];
    script_runtime_equivalence(&sources, "instance-cells", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_named_activation_runtime_equivalence() -> Result<()> {
    let sources = [
        "function outer(){function build(v){let a=[v];return a;}let r=build(7);return r[0];}outer();",
        "function outer(){let a=[7];function mutate(x){x[0]=9;return x;}let b=mutate(a);return [a[0],b[0],a===b];}outer();",
        "function outer(){let a=[7];function mutate(){a[0]=9;}mutate();return a[0];}outer();",
        "function outer(){let a=[0,0];function write(i){a[i]=i+7;}for(let i=0;i<2;i++){write(i);}return a;}outer();",
        "function outer(){function pick(v){let a=[v];return a[0];}let b=[pick(7),pick(9)];return b[0]+b[1];}outer();",
        "function outer(){function pick(v){let a=[v];return a[0];}let b=[pick(7)];let c=b[0];let alias=pick;return alias(9)+c;}outer();",
        "function outer(flag){function build(){if(flag)return [7];return [7];}let b=build();return b[0];}[outer(true),outer(false)];",
        "function outer(flag){function build(){if(flag)return [7];return [9];}let b=build();return b[0];}[outer(true),outer(false)];",
        "function outer(){let a=[7];function g(){a[0]=9;return a;}function f(){return g();}let b=f();return [b[0],a[0],a===b];}outer();",
        "function outer(){let a=build(7);function build(x){return [x];}return a[0];}outer();",
        "function outer(){function f(a,n){if(n)f(a,n-1);a[0]++;return a;}let a=[0];f(a,2);return a[0];}outer();",
        "function outer(){function build(){events.push('effect');return [7];}let a=build();return a[0];}outer();",
        "function outer(){function f(x,x){return [x];}let a=f(1,7);return a[0];}outer();",
        "function outer(){function f(x){arguments[0]=9;return [x];}let a=f(7);return a[0];}outer();",
        "function outer(){function f(p){function p(){return 9}return [p];}let a=f(7);return a[0]();}outer();",
        "function outer(){function f(){let x=[7];using r={[Symbol.dispose](){x[0]=9;}};return x;}let a=f();return a[0];}outer();",
        "function outer(){'use strict';{let a=build(7);function build(x){return [x];}return a[0];}}outer();",
        "function outer(flag){function build(){if(flag)throw 0;return [7];}let a=build();return a[0];}try{outer(true)}catch(e){events.push(e)}outer(false);",
        "function outer(){function f(){return [7];}eval('f=()=>[9]');let a=f();return a[0];}outer();",
        "function f(){return [7];}globalThis.f=()=>[9];let a=f();a[0];",
        "function outer(){let a=[7];function f(){events.push('effect');return [9];}let b=f();return a[0]+b[0];}outer();",
        "function outer(){function f(v){if(v)return [7];return [9];}let a=f(1);let b=f(0);return a[0]+b[0];}outer();",
        "function outer(){function f(x){return x;}let a=[7];let b=f(a);return a===b;}outer();",
        "function outer(){let a=[0];function f(n){if(n)g(n-1);a[0]++;}function g(n){if(n)f(n-1);a[0]++;}f(4);return a[0];}outer();",
        "function outer(){function f(x){return [x];}let a=f(7);return [a[0],f(9)[0]];}outer();",
        "function outer(){function f(){return [7];}let a=f();const alias=f;return [a[0],alias()[0]];}outer();",
        "function outer(){let a=[0];function f(x,y){x[0]=y;return x;}let b=f(a,(a[0]++,7));return [b[0],a[0]];}outer();",
        "function outer(){function f(){return [7];}let a=f();function g(){return outer();}return a[0];}outer();",
    ];
    script_runtime_equivalence(&sources, "named-activation", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_immediate_activation_runtime_equivalence() -> Result<()> {
    let sources = [
        "let a=(()=>[7])();a[0];",
        "let a=(()=>{let x=[7];return x;})();a[0];",
        "let a=(function(){var a=[1,2];for(var i=0;i<2;i++)a[i]+=2;return a;})();[a[0],a[1]];",
        "let a=[1];let b=(x=>{x[0]=7;return x;})(a);[a[0],b[0],a===b];",
        "let a=(()=>{let a=[7];for(let i=0;i<2;i++){if(i===1)return a;}return [9];})();a[0];",
        "function f(flag){let a=[7];let b=(()=>{if(flag)return a;return a;})();return b[0];}[f(false),f(true)];",
        "function f(flag){let a=[7];let b=(()=>{if(flag)throw 0;return a;})();return b[0];}try{f(true)}catch(e){events.push(e);}f(false);",
        "let a=(()=>{events.push('effect');return [7];})();a[0];",
        "let a=(function(){events.push('effect');return [7];})();a[0];",
        "let a=(()=>{try{return [7];}finally{}return [9];})();a[0];",
        "let a=(()=>{try{return [7];}finally{return [9];}})();a[0];",
        "let a=[7];let old=a;a[(()=>{a=[9];return 0;})()]=11;[old[0],a[0]];",
        "let a=[[7],(()=>{let b=[8];return b;})()];[a[0][0],a[1][0]];",
        "let result=[0,0];for(let i=0;i<2;i++){result[i]=(x=>{let a=[x];return a[0];})(i);}[result[0],result[1]];",
        "let result=[0,0];for(let i=0;i<2;i++){result[i]=(x=>{let a=[x];if(x===1){try{return a[0]}finally{}}return a[0];})(i);}result;",
        "let outer=[7];let escaped=(function(){var arguments;return [arguments,outer[0]];})();outer[0]=9;escaped[0].callee()[1];",
        "function expose(){return expose.caller;}let a=[7];let f=(function(){return [expose(),a[0]];})();a[0]=9;f[0]()[1];",
        "let a=(function(x,x){return [x];})(1,7);a[0];",
        "let a=(function(x,x){return [x];})(7);a[0];",
        "let a=(function(p){function p(){return 9}return p;})([7]);a();",
        "let a=(function(x){'use strict';var x;return x;})([7]);a[0];",
        "let a=(()=>{var x;return [x];})();a[0];",
        "let a;{using r={[Symbol.dispose](){a[0]=9;}};a=[7];events.push(a[0]);}a[0];",
        "let a=(()=>{let x;using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x;})();a[0];",
        "let a=(()=>{let x;{using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x;}})();a[0];",
        "let a=(()=>{let x;using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x[0];})();let b=[a];b[0];",
        "let a;{using r={[Symbol.dispose](){a[0]=9;}};a=[7];let v=(()=>a[0])();events.push(v);}a[0];",
        "let a;(()=>{using r={[Symbol.dispose](){a[0]=9;}};a=[7];})();a[0];",
        "let a=(()=>{let x;using r={[Symbol.dispose](){x[0]=9;}};x=[7];for(let i=0;i<1;i++){return x;}})();a[0];",
        "let a=(()=>{let x;using r={[Symbol.dispose](){throw new Error('dispose');}};x=[7];return x;})();a[0];",
        "function f(flag){let a=(()=>{if(flag)return [7];return [7];})();return a[0];}[f(true),f(false)];",
        "function f(flag){let a=(()=>{if(flag)return [[7]];return [[7]];})();return a[0][0];}[f(true),f(false)];",
        "function f(flag){let a=(()=>{if(flag)return [7];return [9];})();return a[0];}[f(true),f(false)];",
        "function f(flag){let a=(()=>{if(flag)return (()=>[7])();return [7];})();return a[0];}[f(true),f(false)];",
        "function f(flag){let a=(()=>{if(flag)return {__proto__:{'x':7}};return {'x':7};})();return a.x;}[f(true),f(false)];",
        "function f(flag){let a=(()=>{if(flag)return [7];for(let i=0;i<2;i++){if(i===1)return [7];}return [9];})();return a[0];}[f(true),f(false)];",
        "function f(flag){let a=(()=>{let x=[7];if(flag){using r={[Symbol.dispose](){x[0]=9;}};x=[7];return x;}return x;})();return a[0];}[f(true),f(false)];",
        "function f(flag){let a=(()=>{let x=[7];if(flag)return x;return [7];})();a[0]=8;return a[0];}[f(true),f(false)];",
        "function f(flag){let a=(()=>{if(flag)return [7];return [7];})();a[0]=7;return a[0];}[f(true),f(false)];",
        "function f(flag){let a=[7];let b=(()=>{if(flag)return [7];return [7];})();return a===b;}[f(true),f(false)];",
    ];
    script_runtime_equivalence(&sources, "immediate-activation", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_direct_decoder_runtime_equivalence() -> Result<()> {
    let sources = [
        "const t=['YQ==','Yg=='];function d(i){return atob(t[i])}Array.prototype['00']='Yw==';Array.prototype['0x0']='ZA==';[d(0),d('1'),d(-0),d(1n),d('00'),d('0x0')];",
        "const t=['YQ==',,'Yg=='];function d(i){return atob(t[i])}Array.prototype[1]='Yw==';[d(0),d(1),d(2)];",
        "const t=['YQ==',(()=>{events.push('init');return 'Yg=='})()];function d(i){return atob(t[i])}[d(0),d(1)];",
        "function f(){try{d(0)}catch(e){events.push(e.name)}const t=['YQ=='];function d(i){return atob(t[i])}return d(0)}f();",
        "function f(){const t=['YQ=='];function d(i){return atob(t[i])}function g(){return d(0)}return g()}f();",
        "function f(){try{g()}catch(e){events.push(e.name)}const t=['YQ=='];function d(i){return atob(t[i])}function g(){return d(0)}return g()}f();",
        "function f(){const t=['YQ=='];function d(i){return atob(t[i])}function g(){return h()}function h(){return d(0)}return g()}f();",
        "function f(){const t=['YQ=='];function d(i){return atob(t[i])}function g(){return d(0)}return g}f()();",
        "const t=['YQ=='];function d(i){return atob(t[i])}function f(){eval('var d=()=>7');return d(0)}f();",
        "const t=['YQ=='];function d(i){return atob(t[i])}eval('d=()=>7');d(0);",
        "const t=['YQ=='];function d(i){return atob(t[i])}eval(\"t[0]='Yg=='\");d(0);",
        "function f(){const t=['YQ=='];function d(i){return atob(t[i])}function sibling(t,d){eval('1')}return d(0)}f();",
        "const t=['YQ=='];function d(i,i){return atob(t[i])}try{d(0)}catch(e){e.name;}",
        "const t=['YQ=='];function d(i){return d=t[i],atob(d)}[d(0),typeof d];",
        "var t=['YQ=='];function d(i){return atob(t[i])}globalThis.t[0]='Yg==';d(0);",
    ];
    script_runtime_equivalence(&sources, "direct-decoder", true)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_provider_runtime_equivalence() -> Result<()> {
    let sources = [
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}[d(16),d(17)];",
        "function p(){var t=['a','b'];events.push('init');p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}[d(16),d(17)];",
        "function p(){var t=['a','b'];p=function(){events.push('read');return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}[d(16),d(17)];",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}p()[0]='z';d(16);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}const escaped=p;escaped()[0]='z';d(16);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}{let p=[];(function(a,n){return n})(p,4);}d(16);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}p=()=>['z'];d(16);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}eval(\"p=()=>['z']\");d(16);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}function e(i,t,v){return i=i-0,t=p(),v=t[i],v;}(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);[d(0),e(0),e(1)];",
    ];
    script_runtime_equivalence(&sources, "provider", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_decoder_alias_runtime_equivalence() -> Result<()> {
    let sources = [
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}const a=d;const b=a;const c=b;[c(16),c(17)];",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}try{a(16)}catch(e){events.push(e.name)}const a=d;a(16);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}try{const b=a;b(16)}catch(e){events.push(e.name)}const a=d;a(16);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function g(){return a(16)}try{g()}catch(e){events.push(e.name)}const a=d;[g(),a(16)];",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(){function f(){return a(16)}const a=d;return f()}outer();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(){function f(){return a(16)}try{f()}catch(e){events.push(e.name)}const a=d;return f()}outer();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(){const a=d;return ()=>a(16)}outer()();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(){const a=d;function f(){return a(16)}return f}outer()();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(a){for(a=d;false;){}function f(){return a(16)}return f()}outer();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(a){for(a=d;false;){}arguments[0]=()=>7;return a(16)}outer(null);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(a){for(a=d;false;){}let mutate=()=>{arguments[0]=()=>7};mutate();return a(16)}outer(null);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(a){for(a=d;false;){}var arguments;arguments[0]=()=>7;return a(16)}outer(null);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(a){'use strict';for(a=d;false;){}arguments[0]=()=>7;return a(16)}outer(null);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(a){function f(){return a(16)}for(a=d;false;){}return f()}outer();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(a,v=a(16)){for(a=d;false;){}return [v,a(16)]}outer(()=>7);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(){eval('var d=()=>7');const a=d;return a(16)}outer();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(){const a=d;function other(a,d,p){eval('1')}return a(16)}outer();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}function outer(){let a=d;a=()=>7;return a(16)}outer();",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}const a=d;const b=a;(b)(16);",
        "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}const run=()=>{let a=d;return a(16)};run();",
    ];
    script_runtime_equivalence(&sources, "decoder-alias", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_rotation_order_runtime_equivalence() -> Result<()> {
    let sources = [
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}events.push(d(0));(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}if(events.length)(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}events.length&&(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}events.length?(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22):0;d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}for(let i=0;i<2;i++){(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);}d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}function before(){return d(0)}events.push(before());(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);d(0);",
        "function run(){function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}function after(){return d(0)}(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);return after()}run();",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,33);d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);events.push(d(0));(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,33);d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}((function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22),d(0));",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}for((function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);false;){}d(0);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}const x=(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);[d(0),x];",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}42;(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);",
        "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}42;!(function(provider,target){var alias=d,table=provider();while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}})(p,22);",
    ];
    script_runtime_equivalence(&sources, "rotation-order", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_rotation_effects_runtime_equivalence() -> Result<()> {
    let prefix = "function p(){var t=['11','22','33'];p=function(){return t;};return p();}function d(i,t,v){return i=i-0,t=p(),v=t[i],v;}";
    let setup = "var alias=d,table=provider();";
    let body = "while(true){try{var checksum=parseInt(alias(0));if(checksum===target)break;else table.push(table.shift());}catch(err){table.push(table.shift());}}";
    let mut sources = [
        (setup.to_string(), body.to_string()),
        (setup.to_string(), body.replace("while(true)", "for(;;)")),
        (setup.to_string(), body.replace("table.push(table.shift())", "table['push'](table['shift']())")),
        ("var alias=d,table=provider(),sum=0;".to_string(), body.replace("var checksum=parseInt(alias(0));if(checksum===target)", "if(sum=parseInt(alias(0)),sum===target)")),
        (setup.to_string(), body.replace("var checksum=parseInt(alias(0));if(checksum===target)", "if(target===parseInt(alias(0)))")),
        (setup.to_string(), body.replace("var checksum=parseInt(alias(0));", "var checksum=parseInt(alias(0));events.push(checksum);")),
        (format!("{setup}events.push('before');"), body.to_string()),
        (setup.to_string(), format!("{body}events.push('after');")),
        (setup.to_string(), body.replace("while(true)", "while(false)")),
        (setup.to_string(), body.replace("while(true)", "for(;true;events.push('update'))")),
        (setup.to_string(), body.replace("else table.push(table.shift());", "else {table.push(table.shift());table.push(table.shift());}")),
        (setup.to_string(), format!("{}finally{{events.push('finally')}}}}", body.strip_suffix('}').unwrap_or_default())),
        (setup.to_string(), body.replace("break;", "return 1;")),
    ].into_iter().map(|(initialization, loop_body)| format!("{prefix}const result=(function(provider,target){{{initialization}{loop_body}}})(p,22);[result,d(0)];")).collect::<Vec<_>>();
    for (first, target) in [("bad", 22), ("0x10", 16), ("18446744073709551616", 22)] {
        let prefix = prefix.replace("'11'", &format!("'{first}'"));
        sources.push(format!(
            "{prefix}(function(provider,target){{{setup}{body}}})(p,{target});d(0);"
        ));
    }
    let refs = sources.iter().map(String::as_str).collect::<Vec<_>>();
    script_runtime_equivalence(&refs, "rotation-effects", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_fixed_rotation_runtime_equivalence() -> Result<()> {
    let prefix = "const table=['a','b','c'];";
    let rotation = "(function(a,n){const rotate=function(k){while(--k){a.push(a.shift());}};rotate(++n);})(table,4);";
    let decoder = "const decode=function(i,_unused){i=i-0;let value=table[i];return value;};[decode(0),decode(1)];";
    let sources = [
        (rotation.to_string(), decoder.to_string()),
        (
            rotation.replace("a.push(a.shift())", "a['push'](a['shift']())"),
            decoder.to_string(),
        ),
        (
            rotation.replace(
                "while(--k){a.push(a.shift());}",
                "while((--k))a.push(a.shift());",
            ),
            decoder.to_string(),
        ),
        (
            rotation.to_string(),
            decoder.replace("table[i]", "(table)[(i)]"),
        ),
        (
            rotation.to_string(),
            decoder.replace("i=i-0;", "i=(i)-(0);"),
        ),
        (
            rotation.replace("(table,4)", "(table,0)"),
            decoder.to_string(),
        ),
        (
            rotation.replace("while(--k)", "while(k--)"),
            decoder.to_string(),
        ),
        (
            rotation.replace("rotate(++n)", "rotate(n++)"),
            decoder.to_string(),
        ),
        (
            rotation.replace("a.push(a.shift());", "a.push(a.shift());events.push(k);"),
            decoder.to_string(),
        ),
        (
            rotation.replace("a.push(a.shift());", "a.push(a.shift());a.push(a.shift());"),
            decoder.to_string(),
        ),
        (
            rotation.to_string(),
            decoder.replace("function(i,_unused)", "function(i,i)"),
        ),
        (
            rotation.to_string(),
            decoder.replace("return value;", "events.push(value);return value;"),
        ),
    ]
    .into_iter()
    .map(|(rotation, decoder)| format!("{prefix}{rotation}{decoder}"))
    .collect::<Vec<_>>();
    let refs = sources.iter().map(String::as_str).collect::<Vec<_>>();
    script_runtime_equivalence(&refs, "fixed-rotation", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_decoder_number_runtime_equivalence() -> Result<()> {
    let prefix = "function p(){var t=['a','b','c'];p=function(){return t;};return p();}";
    let sources = [
        ("16","['0x10','+0x10','0b10000','0o20','1.6e1','16.00','16.5','Infinity','NaN'].map(x=>d(x))"),
        ("-16","d('-0x10')"),
        ("0","[d(null),d(true),d(false),d(''),d('  '),d(void 0),d(-0),d(1+1)]"),
        ("9007199254740992","[d('9007199254740993'),d(9007199254740994)]"),
        ("16","[d('0x10'),d('+0x10'),d('0b10000'),d('0o20'),d('1.6e1'),d('16.00'),d('16.5'),d('Infinity'),d('NaN')]"),
        ("16","[d((events.push('test'),true)?'0x10':'17.0'),d((events.push('test2'),false)?'0x10':'17.0')]"),
        ("0","d((events.push('keep'),0))"),
    ].into_iter().map(|(offset, expression)|format!("{prefix}function d(i,t,v){{return i=i-({offset}),t=p(),v=t[i],v;}}{expression};")).collect::<Vec<_>>();
    let refs = sources.iter().map(String::as_str).collect::<Vec<_>>();
    script_runtime_equivalence(&refs, "decoder-number", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_heap_liveness_runtime_equivalence() -> Result<()> {
    let churn = "{let waste={ x:1 };}".repeat(128);
    let temporaries = "({ x:1 }),".repeat(128);
    let sources = [
        format!("let holder;{{let p={{x:7}};let a={{__proto__:p}};holder={{a}};}}{churn}holder.a.x;"),
        format!("let holder={{x:{{y:7}},self:null}};holder.self=holder;{churn}holder.self.x.y;"),
        format!("function f(flag){{let h; if(flag){{let a={{x:7}};h=a;{churn}}}else{{let b={{x:7}};h=b;{churn}}}return h.x;}} [f(true),f(false)];"),
        format!("function f(flag){{let h={{x:7}};if(flag){{h={{x:7}};{churn}}}return h.x;}}[f(true),f(false)];"),
        format!("let a={{x:7}};let b=a;b.x=({temporaries}a={{x: 9}},8);[b.x,a.x];"),
        format!("let a={{child:{{x:7}},extra:({temporaries}0)}};a.child.x;"),
        format!("let holder;{{let a={{x:7}};holder=a;}}{churn}events.push(holder.x);holder.x=8;holder.x;"),
    ];
    let refs = sources.iter().map(String::as_str).collect::<Vec<_>>();
    script_runtime_equivalence(&refs, "heap-liveness", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_plain_decoder_runtime_equivalence() -> Result<()> {
    let prefix = "function p(){var t=['a','b'];p=function(){return t;};return p();}";
    let sources = [
        "function d(i){i=i-16;const t=p();let v=t[i];return v;}",
        "function d(i){i-=16;const t=p();return t[i]}",
        "function d(i){i=(i)-(16);const /*table*/ t=(p)();return (t)[(i)];}",
        "function d(i){const t=p();return (d=function(x){return t[x-=16]})(i)}",
        "function d(i){const t=p();return d=function(x){x-=16;return t[x]},d(i)}",
        "function d(i){const t=p();d=function(x){x-=16;return t[x]};return d(i)}",
        "function d(i){const t=p();d=function(x){x-=16;return t[x]};events.push(i);return d(i)}",
        "function d(i){const t=p();return d=function(x){x=x-16;const v=t[x];return v},d(i)}",
        "function d(i){const t=p();return (d=function named(x){return t[x-=16]})(i)}",
        "function d(i){i=i-16;const t=p();let v=t[i];events.push(v);return v;}",
        "function d(i){const t=p();return d=function(x){x=x-16;const v=t[x];events.push(v);return v},d(i)}",
        "function d(i){const t=p();return (d=function(t){return t[t-=16]})(i)}",
        "function d(i){const t=p();return (d=function(x){return t[x-=16]})(i+1)}",
        "function d(i){const t=p();return (d=function(x=events.push(i)){return t[x-=16]})(i)}",
        "function d(i){const t=p();return (d=function(x){return t[x-=16]})?.(i)}",
        "function d(i){i=i-16;const t=p();let v=t[i];return 'wrong'}",
        "function d(i){i=i-16;const t=p();return t?.[i]}",
    ].into_iter().map(|decoder|format!("{prefix}{decoder}[d(16),d(17)];")).collect::<Vec<_>>();
    let refs = sources.iter().map(String::as_str).collect::<Vec<_>>();
    script_runtime_equivalence(&refs, "plain-decoder", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_callable_installation_runtime_equivalence() -> Result<()> {
    let prefix = "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i){const t=p();return (d=function(x){return t[x-=16]})(i)}";
    let sources = [
        "d(16);",
        "const original=d;original(16);",
        "const original=d;const alias=original;alias(16);",
        "const original=d;const value=d(16);[original===d,value];",
        "const value=d(16);[d.toString(),value];",
        "const value=d(16);[d.name,value];",
        "const alias=d;const value=d(16);[alias===d,value];",
        "let alias;void(alias=d);d(16);",
        "let alias;(alias=d,0);d(16);",
        "let alias;for(alias=d;false;){}d(16);",
        "let alias;alias=d;d(16);",
        "let alias;d(16);alias=d;",
        "let alias;d(16);(alias=d,alias);",
        "function capture(){const alias=d;return alias}const original=capture();[d(16),original===capture()];",
        "const alias=d;alias.extra=1;[d(16),d.extra];",
        "function invoke(alias){return alias(16)}[d(16),invoke(d)];",
    ].into_iter().map(|suffix|format!("{prefix}{suffix}")).collect::<Vec<_>>();
    let refs = sources.iter().map(String::as_str).collect::<Vec<_>>();
    script_runtime_equivalence(&refs, "callable-installation", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_local_alias_regions_runtime_equivalence() -> Result<()> {
    let functions = "function p(){var t=['a','b'];p=function(){return t;};return p();}function d(i,t,v){return i=i-16,t=p(),v=t[i],v;}";
    let sources = [
        "events.push('before');let a=d;return a(16);",
        "events.push('before');var a=d;return a(16);",
        "var before=events.push('before'),a=d;return a(16);",
        "events.push('before');let a=d;events.push('middle');let b=a;return b(16);",
        "events.push('before');{let a=d;return a(16);}",
        "if(flag){var a=d;events.push(a(16));}try{return a(16)}catch(e){return e.name}",
        "try{a(16)}catch(e){events.push(e.name)}var a=d;return a(16);",
        "try{a(16)}catch(e){events.push(e.name)}let a=d;return a(16);",
        "events.push('before');let a=d;a=()=>7;return a(16);",
        "function inner(){return a(16)}events.push('before');var a=d;return inner();",
        "function inner(){return a(16)}try{inner()}catch(e){events.push(e.name)}var a=d;return [inner(),a(16)];",
        "try{if(flag)throw Error('early');var a=d;}catch(error){}try{return a(16)}catch(e){return e.name}",
        "events.push('before');let a=d;eval('a=()=>7');return a(16);",
        "events.push('before');var a=d;let f=()=>a(16);return f();",
        "events.push('before');let a=d;function mutate(){a=()=>7}mutate();return a(16);",
    ].into_iter().map(|body|format!("function run(flag){{{functions}{body}}}[run(false),run(true)];")).collect::<Vec<_>>();
    let refs = sources.iter().map(String::as_str).collect::<Vec<_>>();
    script_runtime_equivalence(&refs, "local-alias-regions", false)
}

fn script_runtime_equivalence(sources: &[&str], suite: &str, browser_globals: bool) -> Result<()> {
    let comparisons = sources
        .iter()
        .enumerate()
        .map(|(index, source)| {
            let label = format!("{suite}-{index}");
            let result =
                deobfuscate_source(source, &label, SourceMode::Auto, 48, false, &budget(&label))?;
            Ok(script_observations::Comparison {
                label,
                original: (*source).to_owned(),
                rewritten: result.source,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    script_observations::compare_pairs(suite, &comparisons, browser_globals)
}

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn depythonify_safe_deob_statement_boundary_and_directive_runtime_equivalence() -> Result<()> {
    let source = r"
function example1(log) {
 function a(){log.push('a');return ()=>log.push('bad');}
 function b(){log.push('b');}
 { a() } (b)()
}
function example2(log) {
 function a(){log.push('a');return ()=>log.push('bad');}
 function b(){log.push('b');}
 a()
 { (b)() }
}
function example3(){ ; 'use strict'; return this === undefined; }
function example4(){ {} 'use strict'; return this === undefined; }
function example5(){ { {} } 'use strict'; return this === undefined; }
function example6(log) {
 function a(){log.push('a');return ()=>log.push('bad');}
 function b(){log.push('b');}
 a()
 {}
 (b)()
}
function example7(log) {
 function a(){log.push('a');return ()=>log.push('bad');}
 function b(){log.push('b');}
 a()
 0;
 (b)()
}
function example8(){0; 'use strict'; return this === undefined;}
function example9(){if(true) 'use strict'; return this === undefined;}
function example10(){'use ' + 'strict'; return this === undefined;}
function example11(){'use strict'; return this === undefined;}
function example12(log){
 function a(){log.push('a');return ()=>log.push('bad');}
 function b(){log.push('b');}
 a()
 if(true) (b)()
}
function example13(){'use strict'
 if(true) (function(){})()
 return this === undefined;
}
const results=[];for(const example of [example1,example2,example6,example7,example12]){const events=[];try{example(events)}catch(e){events.push(e.name)}results.push(events)}
console.log(JSON.stringify([results,example3(),example4(),example5(),example8(),example9(),example10(),example11(),example13()]));
";
    let scratch = TempDir::new()?;
    let result = deobfuscate_source(
        source,
        "statement-boundaries",
        SourceMode::Auto,
        32,
        false,
        &budget("statement-boundaries"),
    )?;
    assert!(result.report.changed);
    assert!(count(&result.report, "flatten_redundant_block") > 0);
    assert!(count(&result.report, "constant_fold") > 0);
    runtime_equivalent(
        scratch.path(),
        "statement-boundaries",
        source,
        &result.source,
    )
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_directive_boundary_matrix_runtime_equivalence() -> Result<()> {
    use std::fmt::Write as _;
    let leading = [
        "",
        "'other';\n",
        "'other'\n",
        "'use strict';\n",
        "'use strict'\n",
    ];
    let prefixes = [
        "",
        ";",
        ";;",
        "/* before */;/* after */;",
        "{}",
        "{;}",
        "{{}}",
        "{}\n;",
        "0;",
        r#"if(false){ record("unreachable"); }"#,
        "if(true) { 0; }",
        "; // separator\n;",
        ";\r\n{}\r\n;",
    ];
    let following = [
        "'use strict';",
        "('use strict');",
        "'use ' + 'strict';",
        r#""other"; "use strict";"#,
        "'other'\n'use strict';",
        "`use strict`;",
        r#"record("seen");"#,
        r#"if(true) record("seen");"#,
        "var local=3; record(local);",
        "record(\"left\")\n{}\n(record)(\"right\");",
        "record(\"left\")\n{ 0; }\n(record)(\"right\");",
        "record(\"left\")\n{}\n[1].forEach(record);",
        "record(\"left\")\n{}\n`template`;",
        "record(\"left\");\n{}\n/regex/.test(\"regex\");",
        r#"if(true) { "use strict"; }"#,
        "",
    ];
    let mut source = String::from("let seen=[];function record(x){seen.push(x);}");
    let mut invocations = String::from("const results=[];");
    let mut index = 0;
    for directive in leading {
        for prefix in prefixes {
            for statement in following {
                writeln!(source, "function fixture_{index}(){{\n{directive}{prefix}\n{statement}\nreturn [this===undefined,this===globalThis,typeof local];\n}}")?;
                writeln!(invocations, "seen=[];try{{results.push([fixture_{index}(),seen]);}}catch(error){{results.push([error.name,seen]);}}")?;
                index += 1;
            }
        }
    }
    assert_eq!(index, 1040);
    source.push_str(&invocations);
    source.push_str("JSON.stringify(results);");
    script_runtime_equivalence(&[source.as_str()], "directive-boundary-matrix", false)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_nested_standalone_blocks_runtime_equivalence() -> Result<()> {
    let deep = format!(
        "function f(x){{{}x+=1;{}return x;}}f(3);",
        "{ /*open*/".repeat(32),
        "/*close*/ }".repeat(32),
    );
    let sources = [
        deep.as_str(),
        "function f(x){ { {x+=1;} {x*=2;} } return x;} f(3);",
        "function f(){let x=1; { { {let x=2;events.push(x);} {events.push(x);} } } return x;} f();",
        "function f(){ { {'use strict';return this===undefined;} } } f();",
        "function f(){ { {var x=3;} } return x;} f();",
        "function f(){function a(){events.push('a');return ()=>events.push('bad');}function b(){events.push('b');} { {a() } {(b)()} } } f();",
        "function f(){let x=0;outer:for(let i=0;i<3;i++){ { {if(i===1)continue outer;x+=i;if(i===2)break outer;} } }return x;} f();",
        "function f(){ { {function inner(){return 3;}events.push(inner());} {events.push(typeof inner);} } } f();",
        "function f(){try{ { {events.push('try');throw Error('x');} } }catch(e){ { {events.push(e.message);} } }finally{ { {events.push('finally');} } }} f();",
        "function f(){{ // open\n {events.push('inner') // close\n } } return 7}f();",
    ];
    script_runtime_equivalence(&sources, "nested-standalone-blocks", false)
}

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn nested_member_target_reassociation_runtime_equivalence() -> Result<()> {
    let source = r"
function execute(mode) {
    const events = [];
    const note = name => { events.push('note:' + name); return name; };
    const state = {value: 1, fn() { events.push('receiver:' + (this === proxy)); }};
    const proxy = new Proxy(state, {
        get(target,key) { events.push('get:' + String(key)); return Reflect.get(target,key); },
        set(target,key,value) {
            events.push('set:' + String(key) + ':' + typeof value);
            return Reflect.set(target,key,value);
        }
    });
    const key = () => { events.push('computed-key'); return 'value'; };
    try {
        const result = mode === 0 ? (((note('object'),proxy).value += (note('rhs'),3))) :
                       mode === 1 ? (((note('computed'),proxy)[key()] = note('write'))) :
                       mode === 2 ? (((note('throw'), (() => {throw Error('abort')})(),proxy).value = note('unreached'))) :
                       mode === 3 ? (((eval('var directLocal = 29'),proxy).value = directLocal)) :
                       mode === 4 ? (((note('callee'),proxy).fn)(), 'called') :
                       mode === 5 ? (((note('function'),proxy).fn = function(){}).name) :
                                    (((note('first'),note('second'),proxy).value = 'ok'));
        events.push('result:' + String(result));
    } catch (error) {
        events.push('throw:' + error.name + ':' + error.message);
    }
    return events;
}
for (const mode of [0,1,2,3,4,5,6]) {
    console.log(JSON.stringify([mode,execute(mode)]));
}
function controlPlacement(mode) {
    const events = [];
    const sink = new Proxy({p: 0}, {
        set(target, key, value) {
            events.push('set:' + key + ':' + value);
            return Reflect.set(target, key, value);
        }
    });
    function first() { events.push('first'); return null; }
    if (mode === 0) ((first(), sink).p = 1);
    if (mode === 1) ((first(), sink).p = 2);
    if (mode === 2) { let n = 0; while (n++ < 2) ((first(), sink).p = n); }
    if (mode === 3) { label: ((first(), sink).p = 4); }
    if (mode === 4) { if (false) ((first(), sink).p = 5); }
    return [events, sink.p];
}
for (const mode of [0,1,2,3,4]) {
    console.log(JSON.stringify(['control', mode, controlPlacement(mode)]));
}
";
    let result = deobfuscate_source(
        source,
        "member-target-comma-reassociation",
        SourceMode::Auto,
        16,
        false,
        &budget("member-target-comma-reassociation"),
    )?;
    assert!(
        count(&result.report, "member_target_comma_reassociation") >= 2,
        "{:?}",
        result.report.transforms
    );
    let scratch = TempDir::new()?;
    runtime_equivalent(
        scratch.path(),
        "member-target-comma-reassociation",
        source,
        &result.source,
    )
}

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn nested_conditional_assignment_runtime_equivalence() -> Result<()> {
    let source = r"
function run(selector) {
    const events = [];
    function Constructor(...args) { events.push('new:' + args.join(',')); this.args = args; }
    const obj = {Ctor: Constructor};
    let chosen;
    const note = (value) => { events.push('eval:' + value); return value; };
    function choose() {
        let target;
        target = selector === 0 ? new obj.Ctor() :
                 selector === 1 ? new obj.Ctor(note('a')) :
                 selector === 2 ? (note('outer'), selector > 1 ? note('inner') : note('no')) :
                 selector === 3 ? (eval('var introduced=31'), introduced) :
                 selector === 4 ? (() => { throw Error('branch error'); })() :
                 2();
        return target;
    }
    try {
        chosen = choose();
        events.push('value:' + (chosen && chosen.args ? chosen.args.join('|') : chosen));
    } catch (error) {
        events.push('throw:' + error.name + ':' + error.message);
    }
    let named;
    named = selector === 0 ? function ExactlyNamed() {} : class AlsoNamed {};
    events.push('named:' + named.name);
    function withVariableEnvironment() {
        let assigned;
        assigned = selector === 2 ?
            (eval('var dynamicLocal=23; function runtimeFunction() { return dynamicLocal }'),
             runtimeFunction() ) : 0;
        events.push('direct-eval:' + assigned);
    }
    try { withVariableEnvironment(); }
    catch (error) { events.push('eval-throw:' + error.name); }
    return events;
}
for (const selector of [0,1,2,3,4,5,-1]) {
    console.log(JSON.stringify([selector, run(selector)]));
}
";
    let result = deobfuscate_source(
        source,
        "nested-conditional-assignment-runtime",
        SourceMode::Auto,
        16,
        false,
        &budget("nested-conditional-assignment-runtime"),
    )?;
    assert!(
        count(&result.report, "assignment_conditional_lowering") >= 2,
        "{:?}",
        result.report.transforms
    );
    let scratch = TempDir::new()?;
    runtime_equivalent(
        scratch.path(),
        "nested-conditional-assignment",
        source,
        &result.source,
    )
}

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn if_guard_binary_left_sequence_runtime_equivalence() -> Result<()> {
    let source = r"
function run(flag) {
    const events = [];
    const obj = new Proxy({value: 3}, {
        get(target,key) { events.push('get:' + String(key)); return target[key]; }
    });
    const right = { valueOf() { events.push('right-value'); return 5; } };
    let assigned = 0;
    if (((assigned = (events.push('prepare'), obj), obj.value) < right))
        events.push('matched');
    events.push('same:' + (assigned === obj));
    if (((eval('var lexical = 17'),obj.value) < right))
        events.push('direct-eval:' + lexical);
    if (flag && ((events.push('guarded'),obj.value) < right))
        events.push('guarded-yes');
    try {
        if (((events.push('throw'),(() => { throw Error('stop'); })(),obj.value) < right))
            events.push('unreachable');
    } catch (error) { events.push('caught:' + error.message); }
    return events;
}
console.log(JSON.stringify([run(false), run(true)]));
";
    let result = deobfuscate_source(
        source,
        "if-guard-binary-left-sequence-runtime",
        SourceMode::Auto,
        16,
        false,
        &budget("if-guard-binary-left-sequence-runtime"),
    )?;
    assert!(
        count(&result.report, "if_guard_binary_left_sequence_lowering") >= 1,
        "{:?}",
        result.report.transforms
    );
    let scratch = TempDir::new()?;
    runtime_equivalent(
        scratch.path(),
        "if-guard-binary-left-sequence",
        source,
        &result.source,
    )
}

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn if_guard_first_member_object_runtime_equivalence() -> Result<()> {
    let source = r"
function execute(gate) {
    const trace = [];
    const note = name => { trace.push(name); return name; };
    const obj = new Proxy({value: 3}, {
        get(target, key) { trace.push('get:' + String(key)); return target[key]; }
    });
    if (((note('start'),obj).value < 5)) trace.push('first-yes');
    if (gate && ((note('guarded'),obj).value < 5)) trace.push('second-yes');
    if (note('left').length + ((note('right'),obj).value) > 0) trace.push('sum-yes');
    if (((eval('var lexical = 17'),obj).value < 5)) trace.push('eval:' + lexical);
    try {
        if (((note('throw'),(() => { throw Error('abort'); })(),obj).value < 5))
            trace.push('unreachable');
    } catch (error) { trace.push('caught:' + error.message); }
    return trace;
}
console.log(JSON.stringify([execute(false), execute(true)]));
";
    let result = deobfuscate_source(
        source,
        "if-guard-member-prefix-runtime",
        SourceMode::Auto,
        12,
        false,
        &budget("if-guard-member-prefix-runtime"),
    )?;
    assert!(
        count(&result.report, "if_guard_member_prefix_lowering") >= 1,
        "{:?}",
        result.report.transforms
    );
    let scratch = TempDir::new()?;
    runtime_equivalent(
        scratch.path(),
        "if-guard-member-prefix",
        source,
        &result.source,
    )
}

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn member_object_sequence_runtime_equivalence() -> Result<()> {
    let source = r"
function run(strict) {
    const trace = [];
    const write = (kind) => { trace.push(kind); return kind; };
    const proxy = new Proxy({}, {
        set(target,key,value) { trace.push('set:' + key); target[key] = value; return true; },
        get(target,key) { trace.push('get:' + key); return target[key]; }
    });
    function outer() {
        // The direct eval must still see the function lexical environment.
        ((eval('var marker = 19'),write('prefix'),proxy).fn =
            function(){ return marker; });
        ((write('before'),proxy)[write('key')] = write('rhs'));
        ((write('compound'),proxy)[write('key-compound')] += write('tail'));
        ((write('logical'),proxy)[write('key')] ||= write('skipped'));
        ((write('nullish'),proxy)[write('key')] ??= write('skipped-nullish'));
        class C {
            #value = 1;
            add() { ((write('private'),this).#value += 2); return this.#value; }
        }
        trace.push('private-value:' + new C().add());
        try {
            ((write('throw'),(() => { throw Error('stop'); })(), proxy).bad = 1);
        } catch (error) { trace.push('catch:' + error.message); }
        const fn = proxy.fn;
        trace.push(fn.name + ':' + fn());
        return trace;
    }
    return outer();
}
console.log(JSON.stringify(run(false)));
";
    let result = deobfuscate_source(
        source,
        "member-object-sequence-runtime",
        SourceMode::Auto,
        12,
        false,
        &budget("member-object-sequence-runtime"),
    )?;
    assert!(
        count(&result.report, "member_object_sequence_lowering") >= 2,
        "{:?}",
        result.report.transforms
    );
    let scratch = TempDir::new()?;
    runtime_equivalent(
        scratch.path(),
        "member-object-sequence",
        source,
        &result.source,
    )
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_generated_runtime_equivalence() -> Result<()> {
    let scratch = TempDir::new()?;
    let mut totals = BTreeMap::<String, usize>::new();
    for &file in MAIN_FIXTURES {
        let ambient = deob_fixture(scratch.path(), file)?;
        // These fixtures exercise own-member transformations. The original
        // classic-script input is still checked for runtime equivalence.
        // A separately scoped variant establishes allocation privacy.
        let outcome = if matches!(
            file,
            "proxy-literals-unary.js"
                | "proxy-members.js"
                | "proxy-calls.js"
                | "safe-mix.js"
                | "obscura-control-flow-storage.js"
        ) {
            let original = fixture(file)?;
            let local = format!("(function(){{\n{original}\n}})();");
            let label = format!("private-{file}");
            runtime_equivalent(scratch.path(), &label, &original, &local)?;
            deob_fixture_source(scratch.path(), &label, &local)?
        } else {
            ambient
        };
        let expected_changed = !matches!(
            file,
            "static-alias-installer-calls.js"
                | "static-alias-live-forwarding.js"
                | "arithmetic-state.js"
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
        ("reaching_heap_compare", 2),
        ("reaching_heap_dispatch", 1),
        ("ordered_switch_unflatten", 1),
        ("dispatch_switch_structured", 2),
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
    assert!(formatted.report.guarantees.presentation_formatted);
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
#[expect(
    clippy::literal_string_with_formatting_args,
    reason = "JavaScript fixture braces are source syntax, not Rust format placeholders"
)]
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

    Ok(())
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_arithmetic_proof_runtime_equivalence() -> Result<()> {
    let scratch = TempDir::new()?;
    let iife = deob_fixture(scratch.path(), "arithmetic-state-iife-recovery.js")?;
    assert_eq!(count(&iife.report, "arithmetic_state_unflatten"), 1);
    assert_eq!(iife.report.arithmetic_state_proofs.len(), 1);
    let proof = &iife.report.arithmetic_state_proofs[0];
    assert_eq!(proof.termination, "conditional");
    assert_eq!(proof.state_path, ["2", "0", "1"]);
    assert_eq!(proof.branch_paths, [vec!["3".to_owned()], vec![]]);

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

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn if_binary_rhs_effect_lifting_runtime_equivalence() -> Result<()> {
    let source = r"
function run(mode) {
  const events = [];
  let reads = 0;
  const U = {};
  const H = new Proxy({}, {
    get(_, key) {
      if (key !== 'length') return undefined;
      const n = ++reads;
      events.push('getter:' + n);
      if (mode === 4 && n === 2) throw new Error('getter-failed');
      return {
        [Symbol.toPrimitive](hint) {
          events.push('primitive:' + n + ':' + hint);
          if (mode === 3) throw new Error('coercion-failed');
          return mode === 1 ? 1 - n : n;
        }
      };
    }
  });
  function effect(name) { events.push('effect:' + name); return 2; }
  try {
    if (H.length < (H.length < (U.fO = void 0, (U.Bn = [], (effect('third'), 2)))))
        events.push('then');
    else events.push('else');
  } catch (e) { events.push('catch:' + e.message); }
  events.push('fields:' + Object.keys(U).join(','));

  const prior = Function.prototype[Symbol.toPrimitive];
  Function.prototype[Symbol.toPrimitive] = function() {
    events.push('function-name:' + this.name);
    return 1;
  };
  try {
    if (function(){} < (effect('anonymous'), 3))
      events.push('fn-matched');
    if ((()=>1) < (effect('arrow'),3)) events.push('arrow-matched');
    if ((class {}) < (effect('class'),3)) events.push('class-matched');
    if ((mode ? function(){} : class {}) < (effect('conditional-name'),3))
      events.push('conditional-matched');
  } finally {
    if (prior === undefined) delete Function.prototype[Symbol.toPrimitive];
    else Function.prototype[Symbol.toPrimitive] = prior;
  }

  try {
    if (mode < (effect('first'), (mode < (effect('second'), 2))))
      events.push('numbers-then');
    else events.push('numbers-else');
  } catch (e) { events.push('numbers-throw:' + e.message); }
  return events;
}
console.log(JSON.stringify(Array.from({length:5},(_, mode) => run(mode))));
";
    let result = deobfuscate_source(
        source,
        "if-binary-rhs-effect-lifting-runtime",
        SourceMode::Auto,
        32,
        false,
        &budget("if-binary-rhs-effect-lifting-runtime"),
    )?;
    assert!(
        count(&result.report, "if_binary_rhs_effect_lifting") >= 2,
        "{:?}",
        result.report.transforms
    );
    let scratch = TempDir::new()?;
    runtime_equivalent(
        scratch.path(),
        "if-binary-rhs-effect-lifting",
        source,
        &result.source,
    )
}
