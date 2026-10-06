use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_ast_visit::{walk, Visit};
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, fs, path::PathBuf};

#[derive(ClapParser, Debug)]
#[command(about = "Emit alpha-normalized signatures for function-table VM handlers")]
struct Args {
    source: PathBuf,
    scan: PathBuf,
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    handler_function_tables: Vec<HandlerTable>,
    table_vms: Vec<TableVm>,
}

#[derive(Debug, Deserialize)]
struct HandlerTable {
    binding: String,
    start: u32,
    end: u32,
    handlers: Vec<HandlerSlot>,
}

#[derive(Debug, Deserialize)]
struct HandlerSlot {
    key: String,
    start: u32,
    end: u32,
}

#[derive(Debug, Deserialize)]
struct TableVm {
    handler_table: String,
}

#[derive(Debug, Serialize)]
struct HandlerSignature {
    table: String,
    table_start: u32,
    table_end: u32,
    key: String,
    start: u32,
    end: u32,
    exact_hash: String,
    coarse_hash: String,
}

#[derive(Debug, Serialize)]
struct Output {
    source: String,
    handlers: Vec<HandlerSignature>,
}

struct ShapeVisitor {
    ids: HashMap<String, usize>,
    props: HashMap<String, usize>,
    next_id: usize,
    next_prop: usize,
    coarse_properties: bool,
    tokens: Vec<String>,
}

impl ShapeVisitor {
    fn new(coarse_properties: bool) -> Self {
        Self {
            ids: HashMap::new(),
            props: HashMap::new(),
            next_id: 0,
            next_prop: 0,
            coarse_properties,
            tokens: Vec::new(),
        }
    }

    fn canonical_id(&mut self, name: &str) -> usize {
        if let Some(id) = self.ids.get(name) {
            return *id;
        }
        let id = self.next_id;
        self.next_id += 1;
        self.ids.insert(name.to_string(), id);
        id
    }

    fn canonical_prop(&mut self, name: &str) -> usize {
        if let Some(id) = self.props.get(name) {
            return *id;
        }
        let id = self.next_prop;
        self.next_prop += 1;
        self.props.insert(name.to_string(), id);
        id
    }
}

impl<'a> Visit<'a> for ShapeVisitor {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        self.tokens.push(format!("K{}", kind.ty() as u8));
        match kind {
            AstKind::IdentifierReference(id) => {
                let n = self.canonical_id(id.name.as_str());
                self.tokens.push(format!("I{n}"));
            }
            AstKind::BindingIdentifier(id) => {
                let n = self.canonical_id(id.name.as_str());
                self.tokens.push(format!("B{n}"));
            }
            AstKind::IdentifierName(id) => {
                if self.coarse_properties {
                    let n = self.canonical_prop(id.name.as_str());
                    self.tokens.push(format!("P{n}"));
                } else {
                    self.tokens.push(format!("P:{}", id.name));
                }
            }
            AstKind::NumericLiteral(_) => self.tokens.push("NUM".into()),
            AstKind::StringLiteral(_) => self.tokens.push("STR".into()),
            AstKind::BooleanLiteral(b) => self.tokens.push(format!("BOOL:{}", b.value)),
            AstKind::NullLiteral(_) => self.tokens.push("NULL".into()),
            AstKind::BinaryExpression(e) => {
                self.tokens.push(format!("BIN:{}", e.operator.as_str()));
            }
            AstKind::LogicalExpression(e) => {
                self.tokens.push(format!("LOG:{}", e.operator.as_str()));
            }
            AstKind::UnaryExpression(e) => self.tokens.push(format!("UN:{}", e.operator.as_str())),
            AstKind::UpdateExpression(e) => {
                self.tokens
                    .push(format!("UP:{}:{}", e.operator.as_str(), e.prefix));
            }
            AstKind::AssignmentExpression(e) => {
                self.tokens.push(format!("AS:{}", e.operator.as_str()));
            }
            AstKind::StaticMemberExpression(e) => {
                if self.coarse_properties {
                    let n = self.canonical_prop(e.property.name.as_str());
                    self.tokens.push(format!("MEM:P{n}"));
                } else {
                    self.tokens.push(format!("MEM:{}", e.property.name));
                }
            }
            AstKind::ComputedMemberExpression(_) => self.tokens.push("MEM:[]".into()),
            AstKind::CallExpression(e) => {
                self.tokens
                    .push(format!("CALL:{}:{}", e.arguments.len(), e.optional));
            }
            AstKind::NewExpression(e) => self.tokens.push(format!("NEW:{}", e.arguments.len())),
            AstKind::Function(f) => self.tokens.push(format!(
                "FN:{}:{}:{}",
                f.params.items.len(),
                f.r#async,
                f.generator
            )),
            AstKind::ArrowFunctionExpression(f) => {
                self.tokens
                    .push(format!("ARROW:{}:{}", f.params.items.len(), f.r#async));
            }
            _ => {}
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn fnv1a64(data: &[u8]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325_u64;
    for byte in data {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

fn shape_hash(source: &str, coarse_properties: bool) -> Result<String> {
    let wrapped = format!("({source})");
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &wrapped, SourceType::cjs());
    anyhow::ensure!(!parsed.panicked, "parser panicked");
    anyhow::ensure!(parsed.diagnostics == 0, "parse diagnostics");
    let mut visitor = ShapeVisitor::new(coarse_properties);
    visitor.visit_program(&parsed.program);
    Ok(format!(
        "{:016x}",
        fnv1a64(visitor.tokens.join("|").as_bytes())
    ))
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.source)
        .with_context(|| format!("reading {}", args.source.display()))?;
    let scan_text = fs::read_to_string(&args.scan)
        .with_context(|| format!("reading {}", args.scan.display()))?;
    let report: ScanReport = serde_json::from_str(scan_text.trim())
        .with_context(|| format!("parsing {}", args.scan.display()))?;

    let active: std::collections::HashSet<_> = report
        .table_vms
        .iter()
        .map(|v| v.handler_table.as_str())
        .collect();

    let mut handlers = Vec::new();
    for table in report
        .handler_function_tables
        .iter()
        .filter(|table| active.contains(table.binding.as_str()))
    {
        for slot in &table.handlers {
            let start = slot.start as usize;
            let end = (slot.end as usize).min(source.len());
            let Some(raw) = source.get(start..end) else {
                continue;
            };
            handlers.push(HandlerSignature {
                table: table.binding.clone(),
                table_start: table.start,
                table_end: table.end,
                key: slot.key.clone(),
                start: slot.start,
                end: slot.end,
                exact_hash: shape_hash(raw, false).unwrap_or_else(|_| "PARSEFAIL".into()),
                coarse_hash: shape_hash(raw, true).unwrap_or_else(|_| "PARSEFAIL".into()),
            });
        }
    }

    let output = Output {
        source: args.source.display().to_string(),
        handlers,
    };
    let json = serde_json::to_string_pretty(&output)?;
    if let Some(path) = args.output {
        fs::write(&path, format!("{json}\n"))
            .with_context(|| format!("writing {}", path.display()))?;
    } else {
        println!("{json}");
    }
    Ok(())
}
