use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_ast_visit::{walk, Visit};
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::Deserialize;
use std::{
    collections::{BTreeSet, HashMap},
    fs,
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Cluster reduced VM effects by alpha-normalized AST shape")]
struct Args {
    input: PathBuf,
    #[arg(long, default_value_t = 2)]
    min_decoders: usize,
    #[arg(long, default_value_t = 35)]
    top: usize,
}

#[derive(Debug, Deserialize)]
struct ReducedVm {
    file: String,
    decoder: String,
    opcodes: Vec<ReducedOpcode>,
}

#[derive(Debug, Deserialize)]
struct ReducedOpcode {
    opcode: u64,
    paths: Vec<ReducedPath>,
}

#[derive(Debug, Deserialize)]
struct ReducedPath {
    effects: Vec<String>,
}

#[derive(Default)]
struct ShapeVisitor {
    ids: HashMap<String, usize>,
    next_id: usize,
    tokens: Vec<String>,
}

impl ShapeVisitor {
    fn canonical_id(&mut self, name: &str) -> usize {
        if let Some(id) = self.ids.get(name) {
            return *id;
        }
        let id = self.next_id;
        self.next_id += 1;
        self.ids.insert(name.to_string(), id);
        id
    }

    fn finish(self) -> String {
        self.tokens.join("|")
    }
}

impl<'a> Visit<'a> for ShapeVisitor {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        // AstType discriminants are stable for the pinned Oxc version and give
        // a compact preorder structural stream.
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
                // Static property names are semantic and should survive
                // variable alpha-renaming.
                self.tokens.push(format!("P:{}", id.name));
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
            AstKind::UnaryExpression(e) => {
                self.tokens.push(format!("UN:{}", e.operator.as_str()));
            }
            AstKind::UpdateExpression(e) => {
                self.tokens
                    .push(format!("UP:{}:{}", e.operator.as_str(), e.prefix));
            }
            AstKind::AssignmentExpression(e) => {
                self.tokens.push(format!("AS:{}", e.operator.as_str()));
            }
            AstKind::StaticMemberExpression(e) => {
                self.tokens.push(format!("MEM:{}", e.property.name));
            }
            AstKind::ComputedMemberExpression(_) => self.tokens.push("MEM:[]".into()),
            AstKind::CallExpression(e) => {
                self.tokens
                    .push(format!("CALL:{}:{}", e.arguments.len(), e.optional));
            }
            AstKind::NewExpression(e) => {
                self.tokens.push(format!("NEW:{}", e.arguments.len()));
            }
            AstKind::Function(f) => {
                self.tokens.push(format!(
                    "FN:{}:{}:{}",
                    f.params.items.len(),
                    f.r#async,
                    f.generator
                ));
            }
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

#[derive(Default)]
struct Cluster {
    count: usize,
    decoders: BTreeSet<String>,
    families: BTreeSet<String>,
    samples: Vec<String>,
    shape: String,
}

fn fnv1a64(data: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for byte in data {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn parse_shape(source: &str) -> String {
    for candidate in [source.to_string(), format!("({source})")] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &candidate, SourceType::cjs());
        if !parsed.is_clean() {
            continue;
        }
        let mut visitor = ShapeVisitor::default();
        visitor.visit_program(&parsed.program);
        return visitor.finish();
    }
    "PARSEFAIL".to_string()
}

fn family(file: &str) -> String {
    PathBuf::from(file)
        .file_name()
        .and_then(|x| x.to_str())
        .unwrap_or(file)
        .to_string()
}

fn main() -> Result<()> {
    let args = Args::parse();
    let text = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;

    let mut effects: HashMap<u64, Cluster> = HashMap::new();
    let mut paths: HashMap<String, Cluster> = HashMap::new();
    let mut vm_count = 0usize;

    for (line_no, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let vm: ReducedVm =
            serde_json::from_str(line).with_context(|| format!("parsing line {}", line_no + 1))?;
        vm_count += 1;
        let fam = family(&vm.file);

        for op in &vm.opcodes {
            for path in &op.paths {
                let mut hashes = Vec::new();

                for raw in &path.effects {
                    if raw == "[no-state-change]" {
                        continue;
                    }
                    let shape = parse_shape(raw);
                    let hash = fnv1a64(shape.as_bytes());
                    hashes.push(format!("{hash:016x}"));

                    let cluster = effects.entry(hash).or_default();
                    cluster.count += 1;
                    cluster.decoders.insert(vm.decoder.clone());
                    cluster.families.insert(fam.clone());
                    if cluster.shape.is_empty() {
                        cluster.shape = shape;
                    }
                    if cluster.samples.len() < 4 && !cluster.samples.contains(raw) {
                        cluster.samples.push(raw.clone());
                    }
                }

                let signature = hashes.join("|");
                let cluster = paths.entry(signature).or_default();
                cluster.count += 1;
                cluster.decoders.insert(vm.decoder.clone());
                cluster.families.insert(fam.clone());
                if cluster.samples.len() < 4 {
                    cluster.samples.push(format!(
                        "{} op {} :: {}",
                        vm.decoder,
                        op.opcode,
                        path.effects.join(" ; ")
                    ));
                }
            }
        }
    }

    let mut effect_rows: Vec<_> = effects
        .into_iter()
        .filter(|(_, c)| c.decoders.len() >= args.min_decoders)
        .collect();
    effect_rows.sort_by(|a, b| {
        b.1.decoders
            .len()
            .cmp(&a.1.decoders.len())
            .then_with(|| b.1.count.cmp(&a.1.count))
    });

    let mut path_rows: Vec<_> = paths
        .into_iter()
        .filter(|(_, c)| c.decoders.len() >= args.min_decoders)
        .collect();
    path_rows.sort_by(|a, b| {
        b.1.decoders
            .len()
            .cmp(&a.1.decoders.len())
            .then_with(|| b.1.count.cmp(&a.1.count))
    });

    println!(
        "VMs {vm_count} shared_effect_shapes {} shared_path_signatures {}",
        effect_rows.len(),
        path_rows.len()
    );
    println!(
        "
TOP EFFECT SHAPES"
    );
    for (hash, c) in effect_rows.into_iter().take(args.top) {
        println!(
            "
{hash:016x} uses {} decoders {} families {}",
            c.count,
            c.decoders.len(),
            c.families.iter().cloned().collect::<Vec<_>>().join(",")
        );
        for sample in c.samples.iter().take(3) {
            let clipped: String = sample.chars().take(240).collect();
            println!("  {clipped}");
        }
    }

    println!(
        "
SHARED FULL PATH SIGNATURES"
    );
    for (sig, c) in path_rows.into_iter().take(args.top) {
        let effects = if sig.is_empty() {
            0
        } else {
            sig.split('|').count()
        };
        println!(
            "
uses {} decoders {} families {} effects {}",
            c.count,
            c.decoders.len(),
            c.families.iter().cloned().collect::<Vec<_>>().join(","),
            effects
        );
        for sample in c.samples.iter().take(2) {
            let clipped: String = sample.chars().take(420).collect();
            println!("  {clipped}");
        }
    }

    Ok(())
}
