use super::*;
use anyhow::{anyhow, Context, Result};
use std::{collections::BTreeMap, fs, path::Path, process::Command};
use tempfile::TempDir;
use work_budget::{run_command, BudgetLimits, WorkBudget};

const FIXTURE_DIR: &str = "corpus/generated/reversible-obfuscation";
const MAIN_FIXTURES: [&str; 41] = [
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
    "ordered-switch-bounded.js",
    "arithmetic-state.js",
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
    assert_eq!(outcome.report.schema, "js-safe-deobfuscate/v2", "{label}");
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
        "reference-identity-table.js" | "reference-identity-table-sync.js" => {
            assert!(count(report, "reference_identity_compare") >= 2);
            assert!(count(report, "reference_state_unflatten") >= 1);
        }
        "ordered-switch.js" | "ordered-switch-for.js" => {
            assert!(count(report, "dispatch_switch_structured") >= 1);
            assert_eq!(count(report, "ordered_switch_unflatten"), 0);
        }
        "ordered-switch-bounded.js" => {
            assert_eq!(count(report, "ordered_switch_unflatten"), 1);
            assert!(!outcome.source.contains("switch ("));
        }
        "arithmetic-state.js"
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
        _ => {}
    }
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_script_completion_runtime_equivalence() -> Result<()> {
    let scratch = TempDir::new()?;
    let sources = [
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



    ];
    for (index, source) in sources.iter().enumerate() {
        let label = format!("script-completion-{index}");
        let result =
            deobfuscate_source(source, &label, SourceMode::Auto, 48, false, &budget(&label))?;
        let runner = |text: &str| -> Result<String> {
            let encoded = serde_json::to_string(text)?;
            Ok(format!(
                r#"const vm=require('node:vm');const events=[];try{{const value=vm.runInNewContext({encoded},{{events}},{{timeout:1000}});console.log(JSON.stringify([typeof value,String(value),events]));}}catch(e){{console.log(JSON.stringify(['throw',String(e),events]));}}"#
            ))
        };
        runtime_equivalent(
            scratch.path(),
            &label,
            &runner(source)?,
            &runner(&result.source)?,
        )?;
    }
    Ok(())
}

#[test]
#[ignore = "requires Node; run the focused test explicitly"]
fn depythonify_safe_deob_statement_boundary_and_directive_runtime_equivalence() -> Result<()> {
    let source = r#"
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
"#;
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
    for file in MAIN_FIXTURES {
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
            "arithmetic-state-iife-shadow-safety.js",
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
