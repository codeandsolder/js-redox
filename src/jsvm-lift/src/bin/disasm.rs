use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::numeric::exact_u64;
use jsvm_lift::pipeline::{read_jsonl, BindingInfo, NormalizedPath, NormalizedVm};
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{Argument, AssignmentTarget, Expression},
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
};

#[derive(ClapParser, Debug)]
#[command(about = "Disassemble linked JS VM bytecode using normalized handler semantics")]
struct Args {
    scan: PathBuf,
    normalized: PathBuf,
    #[arg(long)]
    output_dir: PathBuf,
    #[arg(long)]
    decoder: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    file: String,
    decoder_candidates: Vec<DecoderCandidate>,
    push_builders: Vec<PushBuilder>,
}

#[derive(Debug, Deserialize)]
struct DecoderCandidate {
    function_id: String,
    builder_var: Option<String>,
    builder_start: Option<u32>,
    ip: String,
    width: u64,
    operand_vars: BTreeMap<String, String>,
}

#[derive(Debug, Deserialize)]
struct PushBuilder {
    start: u32,
    end: u32,
    #[serde(rename = "receiver")]
    _receiver: String,
    arguments: usize,
    values: Vec<Option<u64>>,
    unknowns: Vec<BuilderUnknown>,
}

#[derive(Debug, Deserialize)]
struct BuilderUnknown {
    index: usize,
    preview: String,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "kind", content = "value")]
enum Field {
    Known(u64),
    Symbolic(String),
    Missing,
}

#[derive(Debug, Serialize)]
struct Instruction {
    index: usize,
    pc: usize,
    opcode: Field,
    operands: Vec<Field>,
    semantics: Vec<NormalizedPath>,
}

#[derive(Debug, Serialize)]
struct Disassembly {
    file: String,
    decoder: String,
    parent: String,
    builder_var: String,
    builder_span: [u32; 2],
    width: usize,
    ip_var: String,
    operand_vars: BTreeMap<String, String>,
    role_bindings: BTreeMap<String, BindingInfo>,
    arguments: usize,
    resolved_symbolic_fields: usize,
    unresolved_fields: usize,
    instructions: Vec<Instruction>,
}

#[derive(Default)]
struct ParseIntAliasVisitor {
    aliases: BTreeSet<String>,
}

fn target_ident(target: &AssignmentTarget<'_>) -> Option<String> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.to_string()),
        _ => None,
    }
}

impl<'a> Visit<'a> for ParseIntAliasVisitor {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::VariableDeclarator(v) => {
                let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &v.id else {
                    return;
                };
                let Some(Expression::Identifier(rhs)) = v.init.as_ref() else {
                    return;
                };
                if rhs.name.as_str() == "parseInt" {
                    self.aliases.insert(id.name.to_string());
                }
            }
            AstKind::AssignmentExpression(a) if a.operator.is_assign() => {
                let Some(name) = target_ident(&a.left) else {
                    return;
                };
                let Expression::Identifier(rhs) = &a.right else {
                    return;
                };
                if rhs.name.as_str() == "parseInt" {
                    self.aliases.insert(name);
                }
            }
            _ => {}
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn parse_int_aliases(source: &str) -> BTreeSet<String> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::cjs());
    if parsed.panicked {
        return BTreeSet::new();
    }
    let mut visitor = ParseIntAliasVisitor::default();
    visitor.visit_program(&parsed.program);
    visitor.aliases
}

fn expression_from_program<'a>(
    program: &'a oxc_ast::ast::Program<'a>,
) -> Option<&'a Expression<'a>> {
    let stmt = program.body.first()?;
    let oxc_ast::ast::Statement::ExpressionStatement(es) = stmt else {
        return None;
    };
    Some(&es.expression)
}

fn resolve_parse_int(preview: &str, aliases: &BTreeSet<String>) -> Option<u64> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, preview, SourceType::cjs());
    if !parsed.is_clean() {
        return None;
    }

    let mut expr = expression_from_program(&parsed.program)?;
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    let Expression::CallExpression(call) = expr else {
        return None;
    };
    let Expression::Identifier(callee) = &call.callee else {
        return None;
    };
    if callee.name.as_str() != "parseInt" && !aliases.contains(callee.name.as_str()) {
        return None;
    }
    if call.arguments.len() < 2 {
        return None;
    }
    let Argument::StringLiteral(text) = &call.arguments[0] else {
        return None;
    };
    let Argument::NumericLiteral(radix) = &call.arguments[1] else {
        return None;
    };
    let radix = u32::try_from(exact_u64(radix.value)?).ok()?;
    if !(2..=36).contains(&radix) {
        return None;
    }
    let raw = text.value.trim();
    let raw = raw.strip_prefix('+').unwrap_or(raw);
    u64::from_str_radix(raw, radix).ok()
}

fn compact_semantics(paths: &[NormalizedPath]) -> String {
    if paths.is_empty() {
        return "<unknown opcode>".into();
    }
    paths
        .iter()
        .map(|path| {
            let body = if path.effects.is_empty() {
                "<no-op>".to_string()
            } else {
                path.effects.join("; ")
            };
            if path.guards.is_empty() {
                body
            } else {
                format!("[{}] {}", path.guards.join(" && "), body)
            }
        })
        .collect::<Vec<_>>()
        .join(" || ")
}

fn field_text(field: &Field) -> String {
    match field {
        Field::Known(v) => v.to_string(),
        Field::Symbolic(v) => format!("{{{v}}}"),
        Field::Missing => "?".into(),
    }
}

fn safe_name(decoder: &str) -> String {
    decoder
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

fn resolve_fields(builder: &PushBuilder, aliases: &BTreeSet<String>) -> (Vec<Field>, usize, usize) {
    let unknowns: HashMap<_, _> = builder
        .unknowns
        .iter()
        .map(|unknown| (unknown.index, unknown.preview.as_str()))
        .collect();
    let mut resolved_symbolic = 0;
    let mut unresolved = 0;
    let fields = builder
        .values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            if let Some(value) = value {
                Field::Known(*value)
            } else if let Some(preview) = unknowns.get(&index) {
                if let Some(value) = resolve_parse_int(preview, aliases) {
                    resolved_symbolic += 1;
                    Field::Known(value)
                } else {
                    unresolved += 1;
                    Field::Symbolic((*preview).to_string())
                }
            } else {
                unresolved += 1;
                Field::Missing
            }
        })
        .collect();
    (fields, resolved_symbolic, unresolved)
}

fn build_instructions(fields: &[Field], width: usize, vm: &NormalizedVm) -> Vec<Instruction> {
    let semantics: HashMap<_, _> = vm
        .opcodes
        .iter()
        .map(|opcode| (opcode.opcode, opcode.paths.clone()))
        .collect();
    (0..fields.len() / width)
        .map(|index| {
            let pc = index * width;
            let opcode = fields.get(pc).cloned().unwrap_or(Field::Missing);
            let operands = (1..width)
                .map(|offset| fields.get(pc + offset).cloned().unwrap_or(Field::Missing))
                .collect::<Vec<_>>();
            let semantic_paths = match opcode {
                Field::Known(value) => semantics.get(&value).cloned().unwrap_or_default(),
                _ => Vec::new(),
            };
            Instruction {
                index,
                pc,
                opcode,
                operands,
                semantics: semantic_paths,
            }
        })
        .collect()
}

fn build_disassembly(
    report: &ScanReport,
    decoder: &DecoderCandidate,
    builder: &PushBuilder,
    vm: &NormalizedVm,
    aliases: &BTreeSet<String>,
) -> Option<Disassembly> {
    let width = usize::try_from(decoder.width).ok()?;
    if width == 0 {
        return None;
    }
    let (fields, resolved_symbolic_fields, unresolved_fields) = resolve_fields(builder, aliases);
    Some(Disassembly {
        file: report.file.clone(),
        decoder: decoder.function_id.clone(),
        parent: vm.parent.clone(),
        builder_var: decoder.builder_var.clone().unwrap_or_default(),
        builder_span: [builder.start, builder.end],
        width,
        ip_var: decoder.ip.clone(),
        operand_vars: decoder.operand_vars.clone(),
        role_bindings: vm.role_bindings.clone(),
        arguments: builder.arguments,
        resolved_symbolic_fields,
        unresolved_fields,
        instructions: build_instructions(&fields, width, vm),
    })
}

fn render_disassembly(disasm: &Disassembly) -> String {
    let mut text = format!(
        "# {}\n# source: {}\n# width: {}  instructions: {}  resolved-symbolic: {}  unresolved: {}\n# builder: {} @ {}..{}\n\n",
        disasm.decoder,
        disasm.file,
        disasm.width,
        disasm.instructions.len(),
        disasm.resolved_symbolic_fields,
        disasm.unresolved_fields,
        disasm.builder_var,
        disasm.builder_span[0],
        disasm.builder_span[1]
    );
    for instruction in &disasm.instructions {
        let mut words = vec![field_text(&instruction.opcode)];
        words.extend(instruction.operands.iter().map(field_text));
        let semantic = compact_semantics(&instruction.semantics);
        let clipped: String = semantic.chars().take(500).collect();
        let _ = writeln!(
            text,
            "{:04} pc={:04}  {:<32} | {}",
            instruction.index,
            instruction.pc,
            words.join(" "),
            clipped
        );
    }
    text
}

fn disassemble_report(
    report: &ScanReport,
    normalized_by_decoder: &HashMap<String, NormalizedVm>,
    output_dir: &Path,
    wanted: Option<&str>,
) -> Result<Vec<Disassembly>> {
    let source = fs::read_to_string(&report.file)
        .with_context(|| format!("reading source {}", report.file))?;
    let aliases = parse_int_aliases(&source);
    let builders: HashMap<_, _> = report
        .push_builders
        .iter()
        .map(|builder| (builder.start, builder))
        .collect();
    let mut output = Vec::new();
    for decoder in &report.decoder_candidates {
        if decoder.builder_var.is_none()
            || wanted.is_some_and(|wanted| decoder.function_id != wanted)
        {
            continue;
        }
        let Some(vm) = normalized_by_decoder.get(&decoder.function_id) else {
            continue;
        };
        let Some(builder) = decoder
            .builder_start
            .and_then(|start| builders.get(&start).copied())
        else {
            continue;
        };
        let Some(disasm) = build_disassembly(report, decoder, builder, vm, &aliases) else {
            continue;
        };
        let text_path = output_dir.join(format!("{}.txt", safe_name(&decoder.function_id)));
        fs::write(&text_path, render_disassembly(&disasm))
            .with_context(|| format!("writing {}", text_path.display()))?;
        output.push(disasm);
    }
    Ok(output)
}

fn print_summary(all: &[Disassembly], output_dir: &Path) {
    let instructions: usize = all.iter().map(|disasm| disasm.instructions.len()).sum();
    let unresolved: usize = all.iter().map(|disasm| disasm.unresolved_fields).sum();
    let resolved: usize = all
        .iter()
        .map(|disasm| disasm.resolved_symbolic_fields)
        .sum();
    println!(
        "disassembled {} VMs / {} instructions; resolved {} symbolic fields, {} unresolved -> {}",
        all.len(),
        instructions,
        resolved,
        unresolved,
        output_dir.display()
    );
}

fn main() -> Result<()> {
    let args = Args::parse();
    fs::create_dir_all(&args.output_dir)
        .with_context(|| format!("creating {}", args.output_dir.display()))?;
    let scans: Vec<ScanReport> = read_jsonl(&args.scan)?;
    let normalized: Vec<NormalizedVm> = serde_json::from_str(
        &fs::read_to_string(&args.normalized)
            .with_context(|| format!("reading {}", args.normalized.display()))?,
    )?;
    let normalized_by_decoder = normalized
        .into_iter()
        .map(|vm| (vm.decoder.clone(), vm))
        .collect::<HashMap<_, _>>();
    let mut all = Vec::new();
    for report in &scans {
        all.extend(disassemble_report(
            report,
            &normalized_by_decoder,
            &args.output_dir,
            args.decoder.as_deref(),
        )?);
    }
    let json_path = args.output_dir.join("disassembly.json");
    fs::write(&json_path, serde_json::to_string_pretty(&all)?)
        .with_context(|| format!("writing {}", json_path.display()))?;
    print_summary(&all, &args.output_dir);
    Ok(())
}
