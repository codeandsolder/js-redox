//! Direct ECMAScript conformance of independent literal proof claims.
//! The synthetic environment records observable evaluation and deliberately
//! makes implicit object coercion and array iteration effectful.

use super::script_observations::{compare_pairs, Comparison};
use anyhow::{bail, ensure, Result};
use jsvm_safe_core::{
    eval_static_primitive, is_inert_static_literal, known_static_bool_with_resolver,
    StaticPrimitiveValue,
};
use oxc_allocator::Allocator;
use oxc_ast::ast::Statement;
use oxc_parser::Parser;
use oxc_span::SourceType;
use std::fmt::Write as _;

const ATOMS: [&str; 44] = [
    "0",
    "1",
    "-0",
    "(0/0)",
    "true",
    "false",
    "null",
    "void 0",
    "0n",
    "1n",
    "''",
    "'a'",
    r"'\ud800'",
    "/x/",
    "[]",
    "{}",
    "[1,2]",
    r#"({"data": 1})"#,
    "({get v(){return effect('getter')}})",
    "(()=>effect('body'))",
    "2 ** 1.5",
    "effect('call')",
    "fail()",
    "({get v(){return effect('read')}}).v",
    "1n / 0n",
    "({[effect('key')]:1})",
    "({[{}]:1})",
    "({...{get v(){return effect('spread')}}})",
    "[...[]]",
    "class {static {effect('static')}}",
    "class {}",
    "class {field=effect('instance')}",
    "class extends null {}",
    "class extends (class {}) {}",
    "class extends (()=>{}) {}",
    "class {static ['prototype']=effect('initializer')}",
    "class {[effect('key')](){}}",
    "class {static [2 ** 1.5]=1}",
    "class {static [{}]=1}",
    "class {static {throw 1}}",
    "class {static value=({'x':1})}",
    "class extends (2 ** 1.5 ? function(){} : null) {}",
    "class extends (2 ** 1.5 ? function(){} : (()=>{})) {}",
    "class extends ([], class {}) {}",
];

const ENVIRONMENT: &str = r"
function effect(value) { events.push(value); return value; }
function fail() { events.push('throw'); throw Error('fixture throw'); }
Object.prototype.toString = function() { events.push('coercion'); return 'key'; };
const iterator = Array.prototype[Symbol.iterator];
Array.prototype[Symbol.iterator] = function() {
    events.push('iteration'); return iterator.call(this);
};
";

struct Claim {
    label: String,
    expression: String,
    expected: String,
}

fn expected_source(value: &StaticPrimitiveValue) -> Result<String> {
    if let StaticPrimitiveValue::Number(number) = value {
        if number.is_nan() {
            return Ok("(0/0)".into());
        }
        if number.is_infinite() {
            return Ok(if number.is_sign_negative() {
                "(-1/0)".into()
            } else {
                "(1/0)".into()
            });
        }
    }
    value
        .render_expression()
        .ok_or_else(|| anyhow::anyhow!("primitive rendering failed"))
}

fn add_claims(expression: &str, claims: &mut Vec<Claim>) -> Result<()> {
    let source = format!("({expression});");
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, &source, SourceType::cjs()).parse();
    ensure!(
        parsed.diagnostics.is_empty(),
        "fixture did not parse: {source}"
    );
    let [Statement::ExpressionStatement(statement)] = parsed.program.body.as_slice() else {
        bail!("fixture did not contain one expression: {source}");
    };
    let ast = &statement.expression;
    let mut add = |kind: &str, evaluated: String, expected| {
        claims.push(Claim {
            label: format!("{kind}: {expression}"),
            expression: evaluated,
            expected,
        });
    };
    if is_inert_static_literal(ast) {
        add("inert", format!("void ({expression})"), "void 0".into());
    }
    if let Some(truthy) = known_static_bool_with_resolver(ast, &|_| None) {
        add(
            "truthiness",
            format!("!!({expression})"),
            truthy.to_string(),
        );
    }
    if let Some(value) = eval_static_primitive(ast) {
        add(
            "primitive",
            format!("({expression})"),
            expected_source(&value)?,
        );
    }
    Ok(())
}

fn add_expression_family(expression: &str, claims: &mut Vec<Claim>) -> Result<()> {
    for expression in [
        expression.to_owned(),
        format!("typeof ({expression})"),
        format!("void ({expression})"),
    ] {
        add_claims(&expression, claims)?;
    }
    Ok(())
}

fn literal_claims() -> Result<Vec<Claim>> {
    let mut claims = Vec::new();
    for left in ATOMS {
        add_expression_family(left, &mut claims)?;
        for right in ATOMS {
            for operator in ["&&", "||", "??", ","] {
                add_expression_family(&format!("({left}) {operator} ({right})"), &mut claims)?;
            }
        }
        for (yes, no) in [
            ("null", "1"),
            ("[]", "false"),
            ("true", "''"),
            ("0n", "1n"),
            ("'x'", "void 0"),
            ("effect('yes')", "0"),
            ("0", "fail()"),
            ("({get v(){return effect('getter')}})", "[]"),
        ] {
            add_expression_family(&format!("({left}) ? ({yes}) : ({no})"), &mut claims)?;
        }
    }
    Ok(claims)
}

fn batch_claims(claims: &[Claim]) -> Result<Vec<Comparison>> {
    claims
        .chunks(128)
        .enumerate()
        .map(|(index, batch)| {
            let mut original = format!("{ENVIRONMENT}\n[\n");
            let mut rewritten = original.clone();
            for claim in batch {
                let label = serde_json::to_string(&claim.label)?;
                writeln!(&mut original, "[{label},({})],", claim.expression)?;
                writeln!(&mut rewritten, "[{label},({})],", claim.expected)?;
            }
            original.push_str("];");
            rewritten.push_str("];");
            Ok(Comparison {
                label: format!("literal-proof-batch-{index}"),
                original,
                rewritten,
            })
        })
        .collect()
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_literal_proofs_agree_with_ecmascript() -> Result<()> {
    let claims = literal_claims()?;
    ensure!(
        claims.len() > 1000,
        "fixture matrix must exercise real proof claims"
    );
    let comparisons = batch_claims(&claims)?;
    eprintln!(
        "{} literal proof observations in {} batches",
        claims.len(),
        comparisons.len()
    );
    compare_pairs("literal-proof-conformance", &comparisons, false)
}
