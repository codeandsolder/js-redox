use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{Argument, ArrayExpressionElement, Expression, ObjectPropertyKind, PropertyKey},
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_span::{GetSpan, SourceType};
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Inventory statically explicit Webpack/Next JSONP chunk module tables")]
struct Args {
    input: PathBuf,
}

#[derive(Debug, Clone, Serialize)]
struct ModuleRecord {
    id: String,
    property_start: u32,
    property_end: u32,
    value_start: u32,
    value_end: u32,
    value_kind: String,
    method: bool,
}

#[derive(Debug, Clone, Serialize)]
struct BundleRecord {
    kind: String,
    start: u32,
    end: u32,
    callee: String,
    chunk_ids: Vec<String>,
    module_table_start: u32,
    module_table_end: u32,
    modules: Vec<ModuleRecord>,
}

#[derive(Debug, Serialize)]
struct Report {
    schema: &'static str,
    input: String,
    diagnostics: usize,
    panicked: bool,
    bundles: Vec<BundleRecord>,
}

struct Collector<'s> {
    source: &'s str,
    bundles: Vec<BundleRecord>,
}

impl Collector<'_> {
    fn fragment(&self, span: oxc_span::Span) -> &str {
        self.source
            .get(span.start as usize..(span.end as usize).min(self.source.len()))
            .unwrap_or_default()
    }

    fn property_key(key: &PropertyKey<'_>) -> Option<String> {
        match key {
            PropertyKey::StaticIdentifier(id) => Some(id.name.to_string()),
            PropertyKey::NumericLiteral(n) if n.value.is_finite() && n.value.fract() == 0.0 => {
                Some(format!("{:.0}", n.value))
            }
            PropertyKey::StringLiteral(s) => Some(s.value.to_string()),
            _ => None,
        }
    }

    fn array_literal_ids(arr: &oxc_ast::ast::ArrayExpression<'_>) -> Option<Vec<String>> {
        let mut ids = Vec::new();
        for element in &arr.elements {
            match element {
                ArrayExpressionElement::NumericLiteral(n)
                    if n.value.is_finite() && n.value.fract() == 0.0 =>
                {
                    ids.push(format!("{:.0}", n.value));
                }
                ArrayExpressionElement::StringLiteral(s) => ids.push(s.value.to_string()),
                _ => return None,
            }
        }
        Some(ids)
    }

    fn record_call(&mut self, call: &oxc_ast::ast::CallExpression<'_>) {
        let callee = self.fragment(call.callee.span()).trim().to_string();
        if !(callee.ends_with(".push")
            || callee.ends_with("['push']")
            || callee.ends_with("[\"push\"]"))
        {
            return;
        }
        let Some(Argument::ArrayExpression(payload)) = call.arguments.first() else {
            return;
        };
        if payload.elements.len() < 2 {
            return;
        }
        let ArrayExpressionElement::ArrayExpression(chunk_ids_expr) = &payload.elements[0] else {
            return;
        };
        let Some(chunk_ids) = Self::array_literal_ids(chunk_ids_expr) else {
            return;
        };
        if chunk_ids.is_empty() {
            return;
        }
        let ArrayExpressionElement::ObjectExpression(module_table) = &payload.elements[1] else {
            return;
        };

        let mut modules = Vec::new();
        let mut unsupported = 0usize;
        for item in &module_table.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                unsupported += 1;
                continue;
            };
            if prop.computed || prop.kind != oxc_ast::ast::PropertyKind::Init {
                unsupported += 1;
                continue;
            }
            let Some(id) = Self::property_key(&prop.key) else {
                unsupported += 1;
                continue;
            };
            let (value_kind, span) = match &prop.value {
                Expression::FunctionExpression(f) => ("function", f.span),
                Expression::ArrowFunctionExpression(f) => ("arrow", f.span),
                _ => {
                    unsupported += 1;
                    continue;
                }
            };
            modules.push(ModuleRecord {
                id,
                property_start: prop.span.start,
                property_end: prop.span.end,
                value_start: span.start,
                value_end: span.end,
                value_kind: value_kind.to_string(),
                method: prop.method,
            });
        }

        // A Webpack/Next JSONP payload module table is overwhelmingly function-valued.
        // Reject generic object pushes and partially dynamic tables rather than guessing.
        if modules.is_empty() || unsupported > 0 || modules.len() != module_table.properties.len() {
            return;
        }

        self.bundles.push(BundleRecord {
            kind: "webpack_chunk_push".into(),
            start: call.span.start,
            end: call.span.end,
            callee,
            chunk_ids,
            module_table_start: module_table.span.start,
            module_table_end: module_table.span.end,
            modules,
        });
    }
}

impl<'a> Visit<'a> for Collector<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        if let AstKind::CallExpression(call) = kind {
            self.record_call(call);
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn parse<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    source_type: SourceType,
) -> oxc_parser::ParserReturn<'a> {
    Parser::new(allocator, source, source_type).parse()
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let allocator = Allocator::default();
    let mut parsed = parse(&allocator, &source, SourceType::mjs());
    if parsed.panicked {
        parsed = parse(&allocator, &source, SourceType::cjs());
    }

    let diagnostics = parsed.diagnostics.len();
    let panicked = parsed.panicked;
    let mut collector = Collector {
        source: &source,
        bundles: Vec::new(),
    };
    if !panicked {
        collector.visit_program(&parsed.program);
    }
    collector.bundles.sort_by_key(|b| b.start);

    let report = Report {
        schema: "js-bundle-inventory/v1",
        input: args.input.display().to_string(),
        diagnostics,
        panicked,
        bundles: collector.bundles,
    };
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
