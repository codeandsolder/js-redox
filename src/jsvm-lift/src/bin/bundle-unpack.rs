use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{
        Argument, ArrayExpressionElement, BindingPattern, Expression, ObjectPropertyKind,
        PropertyKey,
    },
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_span::{GetSpan, SourceType};
use serde::Serialize;
use std::{
    collections::{BTreeSet, HashSet},
    fs,
    path::PathBuf,
};

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
    dependencies: Vec<String>,
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

struct DependencyCollector<'n> {
    require_name: &'n str,
    dependencies: BTreeSet<String>,
}

impl<'a> Visit<'a> for DependencyCollector<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        let AstKind::CallExpression(call) = kind else {
            return;
        };
        let Expression::Identifier(callee) = &call.callee else {
            return;
        };
        if callee.name.as_str() != self.require_name {
            return;
        }
        let Some(first) = call.arguments.first() else {
            return;
        };
        let dependency = match first {
            Argument::NumericLiteral(value)
                if value.value.is_finite() && value.value.fract() == 0.0 =>
            {
                Some(format!("{:.0}", value.value))
            }
            Argument::StringLiteral(value) => Some(value.value.to_string()),
            _ => None,
        };
        if let Some(dependency) = dependency {
            self.dependencies.insert(dependency);
        }
    }
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

    fn module_dependencies(value: &Expression<'_>) -> Vec<String> {
        let (params, body) = match value {
            Expression::FunctionExpression(function) => {
                let Some(body) = function.body.as_ref() else {
                    return Vec::new();
                };
                (&function.params, body.as_ref())
            }
            Expression::ArrowFunctionExpression(function) => {
                (&function.params, function.body.as_ref())
            }
            _ => return Vec::new(),
        };
        let Some(require_param) = params.items.get(2) else {
            return Vec::new();
        };
        let BindingPattern::BindingIdentifier(require_id) = &require_param.pattern else {
            return Vec::new();
        };
        let mut collector = DependencyCollector {
            require_name: require_id.name.as_str(),
            dependencies: BTreeSet::new(),
        };
        collector.visit_function_body(body);
        collector.dependencies.into_iter().collect()
    }

    fn module_records(
        &self,
        module_table: &oxc_ast::ast::ObjectExpression<'_>,
    ) -> Option<Vec<ModuleRecord>> {
        let mut modules = Vec::with_capacity(module_table.properties.len());
        for item in &module_table.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                return None;
            };
            if prop.computed || prop.kind != oxc_ast::ast::PropertyKind::Init {
                return None;
            }
            let id = Self::property_key(&prop.key)?;
            let (value_kind, span) = match &prop.value {
                Expression::FunctionExpression(f) => ("function", f.span),
                Expression::ArrowFunctionExpression(f) => ("arrow", f.span),
                _ => return None,
            };
            modules.push(ModuleRecord {
                id,
                property_start: prop.span.start,
                property_end: prop.span.end,
                value_start: span.start,
                value_end: span.end,
                value_kind: value_kind.to_string(),
                method: prop.method,
                dependencies: Self::module_dependencies(&prop.value),
            });
        }
        (!modules.is_empty()).then_some(modules)
    }

    fn direct_table_is_webpack_like(
        module_table: &oxc_ast::ast::ObjectExpression<'_>,
        modules: &[ModuleRecord],
    ) -> bool {
        if modules.len() < 16
            || modules
                .iter()
                .any(|m| !m.id.bytes().all(|b| b.is_ascii_digit()))
        {
            return false;
        }

        let mut conventional_arity = 0usize;
        for item in &module_table.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                return false;
            };
            let arity = match &prop.value {
                Expression::FunctionExpression(f) => f.params.items.len(),
                Expression::ArrowFunctionExpression(f) => f.params.items.len(),
                _ => return false,
            };
            if (2..=3).contains(&arity) {
                conventional_arity += 1;
            }
        }

        conventional_arity * 4 >= modules.len() * 3
    }

    fn record_object(&mut self, module_table: &oxc_ast::ast::ObjectExpression<'_>) {
        let Some(modules) = self.module_records(module_table) else {
            return;
        };
        if !Self::direct_table_is_webpack_like(module_table, &modules) {
            return;
        }
        self.bundles.push(BundleRecord {
            kind: "webpack_module_table".into(),
            start: module_table.span.start,
            end: module_table.span.end,
            callee: "<direct-object-module-table>".into(),
            chunk_ids: Vec::new(),
            module_table_start: module_table.span.start,
            module_table_end: module_table.span.end,
            modules,
        });
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

        // A Webpack/Next JSONP payload module table is overwhelmingly
        // function-valued. Reject generic or partially dynamic object pushes.
        let Some(modules) = self.module_records(module_table) else {
            return;
        };

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
        match kind {
            AstKind::CallExpression(call) => self.record_call(call),
            AstKind::ObjectExpression(object) => self.record_object(object),
            _ => {}
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

    // The object inside a JSONP chunk push also satisfies the direct-table
    // shape. Prefer the richer chunk-push record when both describe the same
    // table.
    let pushed_tables = collector
        .bundles
        .iter()
        .filter(|bundle| bundle.kind == "webpack_chunk_push")
        .map(|bundle| (bundle.module_table_start, bundle.module_table_end))
        .collect::<HashSet<_>>();
    collector.bundles.retain(|bundle| {
        bundle.kind != "webpack_module_table"
            || !pushed_tables.contains(&(bundle.module_table_start, bundle.module_table_end))
    });
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
