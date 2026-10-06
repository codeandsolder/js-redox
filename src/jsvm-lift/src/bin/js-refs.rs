use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, CallExpression, ExportAllDeclaration, ExportNamedDeclaration, Expression,
    ImportDeclaration, ImportExpression, NewExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, SourceType};
use rolldown_redox::ecmascript::{dynamic_import_to_glob, parse_program};
use serde::Serialize;
use std::{collections::BTreeSet, fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Extract JavaScript module/worker execution-boundary references with Oxc")]
struct Args {
    input: PathBuf,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Serialize)]
struct JsReference {
    kind: String,
    specifier: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    glob: Option<String>,
    start: u32,
    end: u32,
}

struct Collector<'s> {
    source: &'s str,
    refs: BTreeSet<JsReference>,
}

impl Collector<'_> {
    fn push(&mut self, kind: &str, specifier: impl Into<String>, start: u32, end: u32) {
        self.refs.insert(JsReference {
            kind: kind.to_string(),
            specifier: specifier.into(),
            glob: None,
            start,
            end,
        });
    }

    fn push_glob(&mut self, specifier: impl Into<String>, glob: String, start: u32, end: u32) {
        self.refs.insert(JsReference {
            kind: "import_dynamic_glob".to_string(),
            specifier: specifier.into(),
            glob: Some(glob),
            start,
            end,
        });
    }

    fn literal_expr(expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::StringLiteral(value) => Some(value.value.to_string()),
            Expression::TemplateLiteral(value) if value.expressions.is_empty() => value
                .quasis
                .first()
                .map(|quasi| quasi.value.raw.to_string()),
            _ => None,
        }
    }

    fn literal_arg(arg: &Argument<'_>) -> Option<String> {
        match arg {
            Argument::StringLiteral(value) => Some(value.value.to_string()),
            Argument::TemplateLiteral(value) if value.expressions.is_empty() => value
                .quasis
                .first()
                .map(|quasi| quasi.value.raw.to_string()),
            _ => None,
        }
    }

    fn callee_ident(expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::Identifier(id) => Some(id.name.to_string()),
            _ => None,
        }
    }

    fn source_fragment(&self, span: oxc_span::Span) -> &str {
        self.source
            .get(span.start as usize..(span.end as usize).min(self.source.len()))
            .unwrap_or_default()
    }

    fn worker_url_from_arg(arg: &Argument<'_>) -> Option<String> {
        match arg {
            Argument::StringLiteral(value) => Some(value.value.to_string()),
            Argument::TemplateLiteral(value) if value.expressions.is_empty() => value
                .quasis
                .first()
                .map(|quasi| quasi.value.raw.to_string()),
            Argument::NewExpression(new_expr)
                if Self::callee_ident(&new_expr.callee).as_deref() == Some("URL") =>
            {
                new_expr.arguments.first().and_then(Self::literal_arg)
            }
            _ => None,
        }
    }
}

impl<'a> Visit<'a> for Collector<'_> {
    fn visit_import_declaration(&mut self, it: &ImportDeclaration<'a>) {
        self.push(
            "import_static",
            it.source.value.to_string(),
            it.span.start,
            it.span.end,
        );
        walk::walk_import_declaration(self, it);
    }

    fn visit_export_named_declaration(&mut self, it: &ExportNamedDeclaration<'a>) {
        if let Some(source) = &it.source {
            self.push(
                "reexport_named",
                source.value.to_string(),
                it.span.start,
                it.span.end,
            );
        }
        walk::walk_export_named_declaration(self, it);
    }

    fn visit_export_all_declaration(&mut self, it: &ExportAllDeclaration<'a>) {
        self.push(
            "reexport_all",
            it.source.value.to_string(),
            it.span.start,
            it.span.end,
        );
        walk::walk_export_all_declaration(self, it);
    }

    fn visit_import_expression(&mut self, it: &ImportExpression<'a>) {
        if let Some(specifier) = Self::literal_expr(&it.source) {
            self.push("import_dynamic", specifier, it.span.start, it.span.end);
        } else if let Ok(Some(glob)) = dynamic_import_to_glob(&it.source) {
            self.push_glob(
                self.source_fragment(it.source.span()).to_string(),
                glob,
                it.span.start,
                it.span.end,
            );
        }
        walk::walk_import_expression(self, it);
    }

    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        if let Some(name) = Self::callee_ident(&it.callee) {
            if matches!(name.as_str(), "require" | "importScripts") {
                if let Some(specifier) = it.arguments.first().and_then(Self::literal_arg) {
                    self.push(
                        if name == "require" {
                            "require"
                        } else {
                            "import_scripts"
                        },
                        specifier,
                        it.span.start,
                        it.span.end,
                    );
                }
            }
        }

        let callee = self.source_fragment(it.callee.span());
        if callee == "navigator.serviceWorker.register"
            || callee.ends_with(".serviceWorker.register")
        {
            if let Some(specifier) = it.arguments.first().and_then(Self::literal_arg) {
                self.push(
                    "service_worker_register",
                    specifier,
                    it.span.start,
                    it.span.end,
                );
            }
        }

        walk::walk_call_expression(self, it);
    }

    fn visit_new_expression(&mut self, it: &NewExpression<'a>) {
        if let Some(name) = Self::callee_ident(&it.callee) {
            if matches!(name.as_str(), "Worker" | "SharedWorker") {
                if let Some(specifier) = it.arguments.first().and_then(Self::worker_url_from_arg) {
                    self.push(
                        if name == "Worker" {
                            "worker"
                        } else {
                            "shared_worker"
                        },
                        specifier,
                        it.span.start,
                        it.span.end,
                    );
                }
            } else if name == "URL" {
                let import_meta_base = it
                    .arguments
                    .get(1)
                    .is_some_and(|arg| self.source_fragment(arg.span()) == "import.meta.url");
                if import_meta_base {
                    if let Some(specifier) = it.arguments.first().and_then(Self::literal_arg) {
                        self.push("module_url", specifier, it.span.start, it.span.end);
                    }
                }
            }
        }
        walk::walk_new_expression(self, it);
    }
}

fn parse<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    source_type: SourceType,
) -> Option<oxc_ast::ast::Program<'a>> {
    let parsed = parse_program(allocator, source, source_type);
    if parsed.is_clean() {
        Some(parsed.program)
    } else {
        None
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let allocator = Allocator::default();
    let program = parse(&allocator, &source, SourceType::mjs())
        .or_else(|| parse(&allocator, &source, SourceType::cjs()))
        .ok_or_else(|| anyhow::anyhow!("Oxc could not parse source as module or script"))?;

    let mut collector = Collector {
        source: &source,
        refs: BTreeSet::new(),
    };
    collector.visit_program(&program);
    println!("{}", serde_json::to_string(&collector.refs)?);
    Ok(())
}
