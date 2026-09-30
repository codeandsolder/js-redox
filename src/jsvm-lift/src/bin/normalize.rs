use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::SemanticBuilder;
use oxc_span::SourceType;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs,
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Rewrite reduced VM effects using inferred semantic role names")]
struct Args {
    reduced: PathBuf,
    roles: PathBuf,
    #[arg(long)]
    output: PathBuf,
}

#[derive(Debug, Deserialize)]
struct ReducedVm {
    file: String,
    decoder: String,
    parent: String,
    state_machine: serde_json::Value,
    opcodes: Vec<ReducedOpcode>,
}

#[derive(Debug, Deserialize)]
struct ReducedOpcode {
    opcode: u64,
    derived_env: BTreeMap<String, serde_json::Value>,
    paths: Vec<ReducedPath>,
}

#[derive(Debug, Deserialize)]
struct ReducedPath {
    guards: Vec<String>,
    states: Vec<u64>,
    effects: Vec<String>,
    terminal: Option<String>,
}

#[derive(Debug, Deserialize)]
struct VmRoles {
    decoder: String,
    roles: BTreeMap<String, RoleAssignment>,
}

#[derive(Debug, Clone, Deserialize)]
struct RoleAssignment {
    name: String,
    source: String,
}

#[derive(Debug, Serialize)]
struct NormalizedVm {
    file: String,
    decoder: String,
    parent: String,
    role_bindings: BTreeMap<String, BindingInfo>,
    state_machine: serde_json::Value,
    opcodes: Vec<NormalizedOpcode>,
}

#[derive(Debug, Serialize)]
struct BindingInfo {
    original: String,
    normalized: String,
    source: String,
}

#[derive(Debug, Serialize)]
struct NormalizedOpcode {
    opcode: u64,
    derived_env: BTreeMap<String, serde_json::Value>,
    paths: Vec<NormalizedPath>,
}

#[derive(Debug, Serialize)]
struct NormalizedPath {
    guards: Vec<String>,
    states: Vec<u64>,
    effects: Vec<String>,
    terminal: Option<String>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Replacement {
    start: usize,
    end: usize,
    value: String,
}

struct RenameVisitor<'s> {
    unresolved: &'s HashSet<u32>,
    rename: &'s HashMap<String, String>,
    offset: usize,
    source_len: usize,
    replacements: Vec<Replacement>,
}

impl RenameVisitor<'_> {
    fn record(&mut self, name: &str, start: u32, end: u32) {
        let Some(value) = self.rename.get(name) else {
            return;
        };
        let start = start as usize;
        let end = end as usize;
        if start < self.offset || end > self.offset + self.source_len {
            return;
        }
        self.replacements.push(Replacement {
            start: start - self.offset,
            end: end - self.offset,
            value: value.clone(),
        });
    }
}

impl<'a> Visit<'a> for RenameVisitor<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        if let AstKind::IdentifierReference(id) = kind {
            if let Some(reference_id) = id.reference_id.get() {
                if self.unresolved.contains(&(reference_id.index() as u32)) {
                    self.record(id.name.as_str(), id.span.start, id.span.end);
                }
            }
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn safe_role_name(role: &str) -> String {
    match role {
        "instruction pointer" => "ip".into(),
        "opcode" => "opcode".into(),
        "operand1" => "op1".into(),
        "operand2" => "op2".into(),
        "operand3" => "op3".into(),
        "value stack / argument stack" => "stack".into(),
        "captured environment/register array" => "env".into(),
        "temporary/register array" => "tmp".into(),
        "current JS arguments array" => "args".into(),
        "pending argument count" => "argc".into(),
        "internal return/control-value stack" => "control".into(),
        "array_push" => "push".into(),
        "array_pop" => "pop".into(),
        "array_splice" => "splice".into(),
        "function_call" => "fn_call".into(),
        "function_apply" => "fn_apply".into(),
        other => {
            let mut out = String::new();
            for ch in other.chars() {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    out.push(ch.to_ascii_lowercase());
                } else if !out.ends_with('_') {
                    out.push('_');
                }
            }
            out.trim_matches('_').to_string()
        }
    }
}

fn collect_replacements(
    candidate: &str,
    offset: usize,
    source_len: usize,
    rename: &HashMap<String, String>,
) -> Option<Vec<Replacement>> {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, candidate, SourceType::cjs()).parse();
    if parsed.panicked || !parsed.diagnostics.is_empty() {
        return None;
    }

    let semantic_ret = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&parsed.program);
    if !semantic_ret.diagnostics.is_empty() {
        return None;
    }
    let semantic = semantic_ret.semantic;
    let unresolved: HashSet<u32> = semantic
        .scoping()
        .root_unresolved_references_ids()
        .flatten()
        .map(|reference_id| reference_id.index() as u32)
        .collect();

    let mut visitor = RenameVisitor {
        unresolved: &unresolved,
        rename,
        offset,
        source_len,
        replacements: Vec::new(),
    };
    visitor.visit_program(&parsed.program);
    Some(visitor.replacements)
}

fn normalize_source(source: &str, rename: &HashMap<String, String>) -> String {
    if source.is_empty() || rename.is_empty() {
        return source.to_string();
    }

    let direct = collect_replacements(source, 0, source.len(), rename);
    let replacements = if let Some(replacements) = direct {
        replacements
    } else {
        let prefix = "function __vm_wrap(){";
        let wrapped = format!("{prefix}{source}}}");
        collect_replacements(&wrapped, prefix.len(), source.len(), rename).unwrap_or_default()
    };

    let mut unique = HashSet::new();
    let mut replacements: Vec<_> = replacements
        .into_iter()
        .filter(|r| unique.insert((r.start, r.end, r.value.clone())))
        .collect();
    replacements.sort_by(|a, b| b.start.cmp(&a.start).then_with(|| b.end.cmp(&a.end)));

    let mut out = source.to_string();
    for r in replacements {
        if r.start <= r.end && r.end <= out.len() {
            out.replace_range(r.start..r.end, &r.value);
        }
    }
    out
}

fn normalize_env(
    env: &BTreeMap<String, serde_json::Value>,
    rename: &HashMap<String, String>,
) -> BTreeMap<String, serde_json::Value> {
    env.iter()
        .map(|(name, value)| {
            (
                rename.get(name).cloned().unwrap_or_else(|| name.clone()),
                value.clone(),
            )
        })
        .collect()
}

fn main() -> Result<()> {
    let args = Args::parse();
    let role_rows: Vec<VmRoles> = serde_json::from_str(
        &fs::read_to_string(&args.roles)
            .with_context(|| format!("reading {}", args.roles.display()))?,
    )?;
    let roles_by_decoder: HashMap<_, _> = role_rows
        .into_iter()
        .map(|r| (r.decoder, r.roles))
        .collect();

    let text = fs::read_to_string(&args.reduced)
        .with_context(|| format!("reading {}", args.reduced.display()))?;
    let mut output = Vec::new();

    for (line_no, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let vm: ReducedVm = serde_json::from_str(line)
            .with_context(|| format!("parsing reduced line {}", line_no + 1))?;
        let roles = roles_by_decoder
            .get(&vm.decoder)
            .cloned()
            .unwrap_or_default();

        let mut rename = HashMap::new();
        let mut role_bindings = BTreeMap::new();
        for (role, binding) in roles {
            let normalized = safe_role_name(&role);
            rename.insert(binding.name.clone(), normalized.clone());
            role_bindings.insert(
                role,
                BindingInfo {
                    original: binding.name,
                    normalized,
                    source: binding.source,
                },
            );
        }

        let opcodes = vm
            .opcodes
            .into_iter()
            .map(|op| NormalizedOpcode {
                opcode: op.opcode,
                derived_env: normalize_env(&op.derived_env, &rename),
                paths: op
                    .paths
                    .into_iter()
                    .map(|path| NormalizedPath {
                        guards: path
                            .guards
                            .iter()
                            .map(|x| normalize_source(x, &rename))
                            .collect(),
                        states: path.states,
                        effects: path
                            .effects
                            .iter()
                            .map(|x| normalize_source(x, &rename))
                            .collect(),
                        terminal: path.terminal,
                    })
                    .collect(),
            })
            .collect();

        output.push(NormalizedVm {
            file: vm.file,
            decoder: vm.decoder,
            parent: vm.parent,
            role_bindings,
            state_machine: vm.state_machine,
            opcodes,
        });
    }

    fs::write(&args.output, serde_json::to_string_pretty(&output)?)
        .with_context(|| format!("writing {}", args.output.display()))?;

    println!(
        "normalized {} VMs -> {}",
        output.len(),
        args.output.display()
    );
    Ok(())
}
