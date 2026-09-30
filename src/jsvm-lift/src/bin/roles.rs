use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_span::SourceType;
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::{Path, PathBuf},
};

#[derive(ClapParser, Debug)]
#[command(about = "Transfer VM register/helper roles across alpha-equivalent handlers")]
struct Args {
    reduced: PathBuf,
    scan: PathBuf,
    ground_truth: PathBuf,
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Deserialize)]
struct ReducedVm {
    file: String,
    decoder: String,
    opcodes: Vec<ReducedOpcode>,
}

#[derive(Debug, Deserialize)]
struct ReducedOpcode {
    paths: Vec<ReducedPath>,
}

#[derive(Debug, Deserialize)]
struct ReducedPath {
    effects: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    decoder_candidates: Vec<DecoderCandidate>,
}

#[derive(Debug, Deserialize)]
struct DecoderCandidate {
    function_id: String,
    builder_var: Option<String>,
    ip: String,
    operand_vars: BTreeMap<String, String>,
    selector_var: Option<String>,
}

#[derive(Debug, Deserialize)]
struct GroundTruth {
    decoder_function_id: String,
    register_roles: BTreeMap<String, String>,
    helper_roles: BTreeMap<String, String>,
}

#[derive(Clone, Debug)]
struct EffectShape {
    hash: u64,
    ids: HashMap<String, usize>,
    reverse: HashMap<usize, String>,
}

#[derive(Clone, Debug)]
struct PathInfo {
    effects: Vec<EffectShape>,
    signature: Vec<u64>,
}

#[derive(Default)]
struct ShapeVisitor {
    ids: HashMap<String, usize>,
    reverse: HashMap<usize, String>,
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
        self.reverse.insert(id, name.to_string());
        id
    }

    fn shape_text(&self) -> String {
        self.tokens.join("|")
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
            AstKind::IdentifierName(id) => self.tokens.push(format!("P:{}", id.name)),
            AstKind::NumericLiteral(_) => self.tokens.push("NUM".into()),
            AstKind::StringLiteral(_) => self.tokens.push("STR".into()),
            AstKind::BooleanLiteral(b) => self.tokens.push(format!("BOOL:{}", b.value)),
            AstKind::NullLiteral(_) => self.tokens.push("NULL".into()),
            AstKind::BinaryExpression(e) => {
                self.tokens.push(format!("BIN:{}", e.operator.as_str()))
            }
            AstKind::LogicalExpression(e) => {
                self.tokens.push(format!("LOG:{}", e.operator.as_str()))
            }
            AstKind::UnaryExpression(e) => self.tokens.push(format!("UN:{}", e.operator.as_str())),
            AstKind::UpdateExpression(e) => {
                self.tokens
                    .push(format!("UP:{}:{}", e.operator.as_str(), e.prefix))
            }
            AstKind::AssignmentExpression(e) => {
                self.tokens.push(format!("AS:{}", e.operator.as_str()))
            }
            AstKind::StaticMemberExpression(e) => {
                self.tokens.push(format!("MEM:{}", e.property.name))
            }
            AstKind::ComputedMemberExpression(_) => self.tokens.push("MEM:[]".into()),
            AstKind::CallExpression(e) => {
                self.tokens
                    .push(format!("CALL:{}:{}", e.arguments.len(), e.optional))
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
                    .push(format!("ARROW:{}:{}", f.params.items.len(), f.r#async))
            }
            _ => {}
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn fnv1a64(data: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for byte in data {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn effect_shape(source: &str) -> EffectShape {
    for candidate in [source.to_string(), format!("({source})")] {
        let allocator = Allocator::default();
        let parsed = Parser::new(&allocator, &candidate, SourceType::cjs()).parse();
        if parsed.panicked || !parsed.diagnostics.is_empty() {
            continue;
        }
        let mut visitor = ShapeVisitor::default();
        visitor.visit_program(&parsed.program);
        let text = visitor.shape_text();
        return EffectShape {
            hash: fnv1a64(text.as_bytes()),
            ids: visitor.ids,
            reverse: visitor.reverse,
        };
    }

    EffectShape {
        hash: fnv1a64(b"PARSEFAIL"),
        ids: HashMap::new(),
        reverse: HashMap::new(),
    }
}

fn path_info(path: &ReducedPath) -> PathInfo {
    let effects: Vec<_> = path
        .effects
        .iter()
        .filter(|raw| raw.as_str() != "[no-state-change]")
        .map(|raw| effect_shape(raw))
        .collect();
    let signature = effects.iter().map(|x| x.hash).collect();
    PathInfo { effects, signature }
}

fn read_jsonl<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<Vec<T>> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    text.lines()
        .enumerate()
        .filter(|(_, line)| !line.trim().is_empty())
        .map(|(i, line)| {
            serde_json::from_str(line)
                .with_context(|| format!("parsing {} line {}", path.display(), i + 1))
        })
        .collect()
}

fn family(file: &str) -> String {
    PathBuf::from(file)
        .file_name()
        .and_then(|x| x.to_str())
        .unwrap_or(file)
        .to_string()
}

fn hard_anchors(scans: &[ScanReport]) -> HashMap<String, BTreeMap<String, String>> {
    let mut out = HashMap::new();

    for scan in scans {
        for d in &scan.decoder_candidates {
            if d.builder_var.is_none() {
                continue;
            }
            let mut a = BTreeMap::new();
            a.insert("instruction pointer".into(), d.ip.clone());

            let vars: HashMap<u64, String> = d
                .operand_vars
                .iter()
                .filter_map(|(k, v)| k.parse::<u64>().ok().map(|n| (n, v.clone())))
                .collect();
            if let Some(v) = vars.get(&0) {
                a.insert("opcode".into(), v.clone());
            } else if let Some(v) = d.selector_var.as_ref() {
                a.insert("opcode".into(), v.clone());
            }
            for offset in 1..=3 {
                if let Some(v) = vars.get(&offset) {
                    a.insert(format!("operand{offset}"), v.clone());
                }
            }
            out.insert(d.function_id.clone(), a);
        }
    }

    out
}

fn hungarian_max(
    weights: &HashMap<String, HashMap<String, i64>>,
    roles: &[String],
    names: &[String],
) -> HashMap<String, String> {
    if roles.is_empty() {
        return HashMap::new();
    }

    let mut cols = names.to_vec();
    cols.extend((0..roles.len()).map(|i| format!("__dummy_{i}")));
    let n = roles.len();
    let m = cols.len();

    let mut u = vec![0i64; n + 1];
    let mut v = vec![0i64; m + 1];
    let mut p = vec![0usize; m + 1];
    let mut way = vec![0usize; m + 1];
    const INF: i64 = i64::MAX / 4;

    for i in 1..=n {
        p[0] = i;
        let mut j0 = 0usize;
        let mut minv = vec![INF; m + 1];
        let mut used = vec![false; m + 1];

        loop {
            used[j0] = true;
            let i0 = p[j0];
            let role = &roles[i0 - 1];
            let mut delta = INF;
            let mut j1 = 0usize;

            for j in 1..=m {
                if used[j] {
                    continue;
                }
                let name = &cols[j - 1];
                let weight = if name.starts_with("__dummy_") {
                    0
                } else {
                    weights
                        .get(role)
                        .and_then(|x| x.get(name))
                        .copied()
                        .unwrap_or(0)
                };
                let cur = -weight - u[i0] - v[j];
                if cur < minv[j] {
                    minv[j] = cur;
                    way[j] = j0;
                }
                if minv[j] < delta {
                    delta = minv[j];
                    j1 = j;
                }
            }

            for j in 0..=m {
                if used[j] {
                    u[p[j]] += delta;
                    v[j] -= delta;
                } else {
                    minv[j] -= delta;
                }
            }

            j0 = j1;
            if p[j0] == 0 {
                break;
            }
        }

        loop {
            let j1 = way[j0];
            p[j0] = p[j1];
            j0 = j1;
            if j0 == 0 {
                break;
            }
        }
    }

    let mut out = HashMap::new();
    for j in 1..=m {
        if p[j] == 0 {
            continue;
        }
        let role = roles[p[j] - 1].clone();
        let name = cols[j - 1].clone();
        if !name.starts_with("__dummy_") {
            out.insert(role, name);
        }
    }
    out
}

#[derive(Debug, Serialize)]
struct RoleAssignment {
    name: String,
    source: String,
    votes: Option<i64>,
    margin: Option<i64>,
}

#[derive(Debug, Serialize)]
struct VmRoles {
    file: String,
    decoder: String,
    matched_paths: usize,
    roles: BTreeMap<String, RoleAssignment>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let vms: Vec<ReducedVm> = read_jsonl(&args.reduced)?;
    let scans: Vec<ScanReport> = read_jsonl(&args.scan)?;
    let gt: GroundTruth = serde_json::from_str(
        &fs::read_to_string(&args.ground_truth)
            .with_context(|| format!("reading {}", args.ground_truth.display()))?,
    )?;

    let ground = vms
        .iter()
        .find(|x| x.decoder == gt.decoder_function_id)
        .context("ground decoder missing from reduced input")?;

    let mut role_by_ground_name = gt.register_roles;
    role_by_ground_name.extend(gt.helper_roles);
    let anchors = hard_anchors(&scans);

    let mut ground_by_signature: HashMap<Vec<u64>, Vec<PathInfo>> = HashMap::new();
    for op in &ground.opcodes {
        for path in &op.paths {
            let info = path_info(path);
            ground_by_signature
                .entry(info.signature.clone())
                .or_default()
                .push(info);
        }
    }

    let mut output = Vec::new();

    let mut ground_roles = BTreeMap::new();
    for (name, role) in &role_by_ground_name {
        ground_roles.insert(
            role.clone(),
            RoleAssignment {
                name: name.clone(),
                source: "ground_truth".into(),
                votes: None,
                margin: None,
            },
        );
    }
    output.push(VmRoles {
        file: family(&ground.file),
        decoder: ground.decoder.clone(),
        matched_paths: ground.opcodes.iter().map(|op| op.paths.len()).sum(),
        roles: ground_roles,
    });

    for vm in &vms {
        if vm.decoder == ground.decoder {
            continue;
        }

        let mut votes: HashMap<String, HashMap<String, i64>> = HashMap::new();
        let mut matched_paths = 0usize;

        for op in &vm.opcodes {
            for path in &op.paths {
                let target = path_info(path);
                let Some(ground_paths) = ground_by_signature.get(&target.signature) else {
                    continue;
                };
                if ground_paths.len() != 1 {
                    continue;
                }
                let ground_path = &ground_paths[0];
                matched_paths += 1;

                for (g_effect, t_effect) in ground_path.effects.iter().zip(target.effects.iter()) {
                    if g_effect.hash != t_effect.hash {
                        continue;
                    }
                    for (ground_name, canonical_id) in &g_effect.ids {
                        let Some(role) = role_by_ground_name.get(ground_name) else {
                            continue;
                        };
                        let Some(target_name) = t_effect.reverse.get(canonical_id) else {
                            continue;
                        };
                        *votes
                            .entry(role.clone())
                            .or_default()
                            .entry(target_name.clone())
                            .or_insert(0) += 1;
                    }
                }
            }
        }

        let hard = anchors.get(&vm.decoder).cloned().unwrap_or_default();
        let used: BTreeSet<_> = hard.values().cloned().collect();

        let mut roles: Vec<String> = votes
            .keys()
            .filter(|role| !hard.contains_key(*role))
            .cloned()
            .collect();
        roles.sort();

        let names: BTreeSet<String> = roles
            .iter()
            .flat_map(|role| votes.get(role).into_iter().flat_map(|m| m.keys()))
            .filter(|name| !used.contains(*name))
            .cloned()
            .collect();

        let filtered: HashMap<String, HashMap<String, i64>> = roles
            .iter()
            .map(|role| {
                let m = votes
                    .get(role)
                    .into_iter()
                    .flat_map(|x| x.iter())
                    .filter(|(name, _)| !used.contains(*name))
                    .map(|(name, score)| (name.clone(), *score))
                    .collect();
                (role.clone(), m)
            })
            .collect();

        let assigned = hungarian_max(&filtered, &roles, &names.into_iter().collect::<Vec<_>>());

        let mut final_roles = BTreeMap::new();
        for (role, name) in hard {
            final_roles.insert(
                role,
                RoleAssignment {
                    name,
                    source: "decoder".into(),
                    votes: None,
                    margin: None,
                },
            );
        }

        for (role, name) in assigned {
            let Some(by_name) = filtered.get(&role) else {
                continue;
            };
            let score = by_name.get(&name).copied().unwrap_or(0);
            let second = by_name
                .iter()
                .filter(|(other, _)| *other != &name)
                .map(|(_, score)| *score)
                .max()
                .unwrap_or(0);
            let margin = score - second;
            if score >= 2 && margin >= 1 {
                final_roles.insert(
                    role,
                    RoleAssignment {
                        name,
                        source: "transfer".into(),
                        votes: Some(score),
                        margin: Some(margin),
                    },
                );
            }
        }

        output.push(VmRoles {
            file: family(&vm.file),
            decoder: vm.decoder.clone(),
            matched_paths,
            roles: final_roles,
        });
    }

    output.sort_by(|a, b| {
        b.roles
            .len()
            .cmp(&a.roles.len())
            .then_with(|| a.decoder.cmp(&b.decoder))
    });

    let json = serde_json::to_string_pretty(&output)?;
    if let Some(path) = args.output.as_ref() {
        fs::write(path, &json).with_context(|| format!("writing {}", path.display()))?;
    }

    println!("VMs {}", output.len());
    let mut by_family: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for vm in &output {
        by_family
            .entry(vm.file.clone())
            .or_default()
            .push(vm.roles.len());
    }
    for (fam, counts) in by_family {
        let avg = counts.iter().sum::<usize>() as f64 / counts.len().max(1) as f64;
        println!(
            "{} vms {} avg_roles {:.2} >=5 {} >=8 {} >=10 {}",
            fam,
            counts.len(),
            avg,
            counts.iter().filter(|x| **x >= 5).count(),
            counts.iter().filter(|x| **x >= 8).count(),
            counts.iter().filter(|x| **x >= 10).count()
        );
    }
    println!(
        "
TOP"
    );
    for vm in output.iter().take(25) {
        let roles = vm
            .roles
            .iter()
            .map(|(role, value)| format!("{}={}[{}]", role, value.name, value.source))
            .collect::<Vec<_>>()
            .join(" ");
        println!(
            "{} {} matched {} roles {} {}",
            vm.file,
            vm.decoder,
            vm.matched_paths,
            vm.roles.len(),
            roles
        );
    }

    Ok(())
}
