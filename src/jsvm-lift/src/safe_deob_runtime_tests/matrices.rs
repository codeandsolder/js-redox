//! Generated, deterministic differential tests for ordinary JavaScript semantics.
//! Every input is synthetic and executed in a fresh VM context.

use super::{
    assert_invariants, budget,
    script_observations::{compare_pairs, Comparison},
};
use crate::safe_deob::{deobfuscate_source, SourceMode};
use anyhow::Result;
use std::fmt::Write as _;
#[path = "number_boundaries.rs"]
mod number_boundaries;

/// Execute a batch of independently parsed scripts in one Node process rather
/// than launching two processes for every tiny fixture.
fn compare_sources(suite: &str, sources: Vec<String>) -> Result<()> {
    let mut comparisons = Vec::with_capacity(sources.len());
    let mut changed = 0;
    for (index, original) in sources.into_iter().enumerate() {
        let label = format!("{suite}-{index}");
        let result = deobfuscate_source(
            &original,
            &label,
            SourceMode::CommonJs,
            48,
            false,
            &budget(&label),
        )?;
        assert_invariants(&label, &result);
        assert!(result.report.analysis_complete, "{label}");
        changed += usize::from(result.report.changed);
        comparisons.push(Comparison {
            label,
            original,
            rewritten: result.source,
        });
    }
    assert!(changed > 0, "{suite} did not exercise any transformation");
    compare_pairs(suite, &comparisons, false)
}

const VALUES: [&str; 27] = [
    "0",
    "-0",
    "1",
    "-1",
    "0x80000000",
    "4294967295",
    "9007199254740991",
    "1.5",
    "(0/0)",
    "(1/0)",
    "(-1/0)",
    "''",
    "'  '",
    "'0x10'",
    "'1.5'",
    "'NaN'",
    "'😀'",
    r"'\ud800'",
    r"'\uE000'",
    "false",
    "true",
    "null",
    "(void 0)",
    "0n",
    "1n",
    "-1n",
    "2147483648n",
];

const POWER_VALUES: [&str; 15] = [
    "0", "-0", "1", "-1", "2", "3", "1.5", "(0/0)", "(1/0)", "(-1/0)", "0n", "1n", "-1n", "2n",
    "3n",
];

const OPERATORS: [&str; 23] = [
    "+", "-", "*", "/", "%", "**", "&", "|", "^", "<<", ">>", ">>>", "==", "!=", "===", "!==", "<",
    "<=", ">", ">=", "&&", "||", "??",
];

const PRIMITIVE_RESULTS: &str = r#"
const result = cases.map(fn => {
    try {
        const x = fn();
        const type = typeof x;
        return [type, type === "number" && Object.is(x, -0) ? "-0" :
            ["number", "bigint", "undefined"].includes(type) ? String(x) : x];
    } catch (error) {
        return ["throw", error.name];
    }
});
JSON.stringify(result);
"#;

fn primitive_sources() -> Result<Vec<String>> {
    let mut sources = Vec::with_capacity(OPERATORS.len());
    let mut total = 0;
    for operator in OPERATORS {
        let values: &[&str] = if operator == "**" {
            &POWER_VALUES
        } else {
            &VALUES
        };
        let mut source = String::from("const cases = [\n");
        for left in values {
            for right in values {
                if matches!(operator, "<<" | ">>" | ">>>")
                    && left.ends_with('n')
                    && *right == "2147483648n"
                {
                    continue;
                }
                writeln!(source, "()=>(({left}){operator}({right})),")?;
                total += 1;
            }
        }
        source.push_str("];\n");
        source.push_str(PRIMITIVE_RESULTS);
        sources.push(source);
    }
    assert_eq!(total, 16_251);
    Ok(sources)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_primitive_operator_matrix() -> Result<()> {
    compare_sources("primitive-operator-matrix", primitive_sources()?)
}

const COMPLETION_STATEMENTS: [&str; 43] = [
    "if(true){}",
    "if(false){}",
    "if(true){3;}",
    "if(false){3;}else{4;}",
    "if(true){var x=1;}",
    r#"if(false){var x=note("never");}"#,
    "if(true) 0;",
    "if(false) 0;",
    r#"if(true) "s";"#,
    r#"if(false){throw Error("never");}else{}"#,
    r#"while(false){note("never");}"#,
    r#"while(false){var x=note("never");}"#,
    "do {3;} while(false);",
    "do {3;break;} while(false);",
    "do {3;continue;} while(false);",
    r#"do {note("before-break");break;} while(false);"#,
    r#"for(note("init");false;note("update")){note("never");}"#,
    r#"for(var i=note("init");false;note("update")){note("never");}"#,
    r#"for(let i=note("init");false;note("update")){note("never");}"#,
    "for(let i=0;i<2;i++){if(i===0){3;continue;}4;}",
    "label:{3;break label;4;}",
    "label:if(true){3;break label;}",
    "label:do{3;break label;}while(false);",
    "outer:do{inner:do{3;continue outer;}while(false);4;}while(false);",
    "switch(1){case 1:3;break;default:4;}",
    "switch(2){case 1:3;break;default:4;case 2:5;}",
    "switch(0){case note(0):3;case note(1):4;break;}",
    "switch(3){default:1;case 2:2;}",
    "switch(0){case 1:3;break;}",
    "try{3;}finally{4;}",
    r#"try{throw Error("x");}catch(e){3;}finally{4;}"#,
    "label:try{3;break label;}finally{4;}",
    "label:try{3;}finally{4;break label;}",
    "try{if(false)3;}finally{}",
    r#"try{throw Error("x");}catch(e){}"#,
    "label:{1;try{2;break label;}finally{3;}}",
    r#"label:{1;try{throw Error("x");}finally{3;break label;}}"#,
    "label:do{try{1;continue label;}finally{2;}}while(false);",
    "label:{if(true){2;break label;}3;}",
    "label:{if(false){2;break label;}3;}",
    r#"try{note("try");throw Error("x");}catch(e){note("catch");}finally{note("finally");}"#,
    "for(const entry of [1,2]){if(entry===1)continue;entry;}",
    r#"for(const entry in {a:1,b:2}){if(entry==="a")continue;entry;}"#,
];

fn completion_sources() -> Vec<String> {
    let mut sources = Vec::new();
    for statement in COMPLETION_STATEMENTS {
        for prefix in ["", "7;", r#"note("before");"#] {
            for suffix in ["", ";", "{}", "var tail;", r#"note("after");"#] {
                sources.push(format!(
                    "function note(x){{events.push(x);return x;}}\n{prefix}\n{statement}\n{suffix}"
                ));
            }
        }
    }
    assert_eq!(sources.len(), 645);
    sources
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_completion_record_matrix() -> Result<()> {
    compare_sources("completion-record-matrix", completion_sources())
}

const REFERENCE_WRAPPERS: [&str; 16] = [
    "(@)",
    "(0,@)",
    "(null,false,0,@)",
    "(0,(0,@))",
    r#"(note("first"),0,@)"#,
    r#"(0,note("first"),@)"#,
    "(false||(@))",
    "(true&&(@))",
    "(null??(@))",
    "(true?(@):bad())",
    "(false?bad():(@))",
    "(true&&(0,@))",
    "(false||(0,@))",
    "(null??(0,@))",
    "(true?(0,@):bad())",
    r#"(true?(note("yes"),@):bad())"#,
];

const REFERENCE_CONTEXTS: [(&str, &str); 17] = [
    ("obj.method", "const value=@();"),
    ("obj.method", "const value=@?.();"),
    ("obj.method", "const value=@`abc`;"),
    ("obj.value", "const value=delete @;"),
    ("obj?.value", "const value=delete @;"),
    ("missingName", "const value=typeof @;"),
    ("eval", r#"const value=@("typeof local");"#),
    ("eval", r#"const value=@?.("typeof local");"#),
    ("function(){}", "const named=@;const value=named.name;"),
    ("()=>0", "const named=@;const value=named.name;"),
    ("class {}", "const named=@;const value=named.name;"),
    ("function(){}", "let named;named=@;const value=named.name;"),
    ("function(){}", "const [named=@]=[];const value=named.name;"),
    (
        "function(){}",
        "const named={property:@};const value=named.property.name;",
    ),
    ("obj.ctor", "const value=(new @()).marker;"),
    ("nil?.method", "const value=@?.();"),
    ("function(){}", "obj.named=@;const value=obj.named.name;"),
];

const REFERENCE_SETUP: &str = r#"
let events=[];let local=7;const nil=null;
const obj={value:3,
    get method(){
        events.push("get");
        return function(){
            "use strict";
            const own=this===obj;
            events.push(own?"own":this===undefined?"undefined":"other");
            return own;
        };
    },
    ctor:function(){this.marker=9;}
};
function note(x){events.push(x);return x;}
function bad(){events.push("bad");throw Error("bad");}
"#;

const REFERENCE_OBSERVATION: &str = r#"
return [typeof value,typeof value==="undefined"?"undefined":value,
    Object.hasOwn(obj,"value"),events];
}catch(e){return ["throw",e.name,Object.hasOwn(obj,"value"),events];}
"#;

fn reference_sources() -> Result<Vec<String>> {
    let mut sources = Vec::new();
    let mut total = 0;
    // Batch by consumer context to keep failure diagnostics focused and
    // avoid repeating semantic analysis of unrelated fixtures.
    for (operand, context) in REFERENCE_CONTEXTS {
        let mut source = String::new();
        let mut calls = Vec::new();
        for strict in ["", r#""use strict";"#] {
            for wrapper in REFERENCE_WRAPPERS {
                let expression = wrapper.replace('@', operand);
                let operation = context.replace('@', &expression);
                writeln!(
                    source,
                    "function fixture_{total}(){{\n{strict}\n{REFERENCE_SETUP}\ntry{{{operation}\n{REFERENCE_OBSERVATION}\n}}"
                )?;
                calls.push(format!("fixture_{total}()"));
                total += 1;
            }
        }
        writeln!(source, "JSON.stringify([{}]);", calls.join(","))?;
        sources.push(source);
    }
    assert_eq!(total, 544);
    Ok(sources)
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_reference_value_matrix() -> Result<()> {
    compare_sources("reference-value-matrix", reference_sources()?)
}
