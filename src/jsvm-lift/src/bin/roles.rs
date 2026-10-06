use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::effect_shape::{analyze_effect, family_name, EffectShape};
use jsvm_lift::pipeline::{read_jsonl, RoleAssignment, VmRoles};
use serde::Deserialize;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::PathBuf,
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
struct PathInfo {
    effects: Vec<EffectShape>,
    signature: Vec<u64>,
}

fn path_info(path: &ReducedPath) -> PathInfo {
    let effects: Vec<_> = path
        .effects
        .iter()
        .filter(|raw| raw.as_str() != "[no-state-change]")
        .map(|raw| analyze_effect(raw))
        .collect();
    let signature = effects.iter().map(|x| x.hash).collect();
    PathInfo { effects, signature }
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
    const INF: i64 = i64::MAX / 4;

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

type Votes = HashMap<String, HashMap<String, i64>>;

fn index_ground_paths(ground: &ReducedVm) -> HashMap<Vec<u64>, Vec<PathInfo>> {
    let mut by_signature = HashMap::new();
    for op in &ground.opcodes {
        for path in &op.paths {
            let info = path_info(path);
            by_signature
                .entry(info.signature.clone())
                .or_insert_with(Vec::new)
                .push(info);
        }
    }
    by_signature
}

fn ground_vm_roles(ground: &ReducedVm, role_by_ground_name: &BTreeMap<String, String>) -> VmRoles {
    let roles = role_by_ground_name
        .iter()
        .map(|(name, role)| {
            (
                role.clone(),
                RoleAssignment {
                    name: name.clone(),
                    source: "ground_truth".into(),
                    votes: None,
                    margin: None,
                },
            )
        })
        .collect();
    VmRoles {
        file: family_name(&ground.file),
        decoder: ground.decoder.clone(),
        matched_paths: ground.opcodes.iter().map(|op| op.paths.len()).sum(),
        roles,
    }
}

fn collect_votes(
    vm: &ReducedVm,
    ground_by_signature: &HashMap<Vec<u64>, Vec<PathInfo>>,
    role_by_ground_name: &BTreeMap<String, String>,
) -> (Votes, usize) {
    let mut votes = HashMap::new();
    let mut matched_paths = 0;
    for op in &vm.opcodes {
        for path in &op.paths {
            let target = path_info(path);
            let Some(ground_paths) = ground_by_signature.get(&target.signature) else {
                continue;
            };
            if ground_paths.len() != 1 {
                continue;
            }
            matched_paths += 1;
            for (ground_effect, target_effect) in
                ground_paths[0].effects.iter().zip(&target.effects)
            {
                if ground_effect.hash != target_effect.hash {
                    continue;
                }
                for (ground_name, canonical_id) in &ground_effect.ids {
                    let (Some(role), Some(target_name)) = (
                        role_by_ground_name.get(ground_name),
                        target_effect.reverse.get(canonical_id),
                    ) else {
                        continue;
                    };
                    *votes
                        .entry(role.clone())
                        .or_insert_with(HashMap::new)
                        .entry(target_name.clone())
                        .or_insert(0) += 1;
                }
            }
        }
    }
    (votes, matched_paths)
}

fn assign_roles(votes: &Votes, hard: BTreeMap<String, String>) -> BTreeMap<String, RoleAssignment> {
    let used: BTreeSet<_> = hard.values().cloned().collect();
    let mut roles: Vec<_> = votes
        .keys()
        .filter(|role| !hard.contains_key(*role))
        .cloned()
        .collect();
    roles.sort();

    let names: Vec<_> = roles
        .iter()
        .flat_map(|role| votes.get(role).into_iter().flat_map(|m| m.keys()))
        .filter(|name| !used.contains(*name))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let filtered: Votes = roles
        .iter()
        .map(|role| {
            let by_name = votes
                .get(role)
                .into_iter()
                .flat_map(|x| x.iter())
                .filter(|(name, _)| !used.contains(*name))
                .map(|(name, score)| (name.clone(), *score))
                .collect();
            (role.clone(), by_name)
        })
        .collect();
    let assigned = hungarian_max(&filtered, &roles, &names);

    let mut final_roles = hard
        .into_iter()
        .map(|(role, name)| {
            (
                role,
                RoleAssignment {
                    name,
                    source: "decoder".into(),
                    votes: None,
                    margin: None,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
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
    final_roles
}

fn transfer_vm_roles(
    vm: &ReducedVm,
    ground_by_signature: &HashMap<Vec<u64>, Vec<PathInfo>>,
    role_by_ground_name: &BTreeMap<String, String>,
    anchors: &HashMap<String, BTreeMap<String, String>>,
) -> VmRoles {
    let (votes, matched_paths) = collect_votes(vm, ground_by_signature, role_by_ground_name);
    let hard = anchors.get(&vm.decoder).cloned().unwrap_or_default();
    VmRoles {
        file: family_name(&vm.file),
        decoder: vm.decoder.clone(),
        matched_paths,
        roles: assign_roles(&votes, hard),
    }
}

fn infer_vm_roles(
    vms: &[ReducedVm],
    ground: &ReducedVm,
    role_by_ground_name: &BTreeMap<String, String>,
    anchors: &HashMap<String, BTreeMap<String, String>>,
) -> Vec<VmRoles> {
    let ground_by_signature = index_ground_paths(ground);
    let mut output = vec![ground_vm_roles(ground, role_by_ground_name)];
    output.extend(
        vms.iter()
            .filter(|vm| vm.decoder != ground.decoder)
            .map(|vm| transfer_vm_roles(vm, &ground_by_signature, role_by_ground_name, anchors)),
    );
    output.sort_by(|a, b| {
        b.roles
            .len()
            .cmp(&a.roles.len())
            .then_with(|| a.decoder.cmp(&b.decoder))
    });
    output
}

fn print_summary(output: &[VmRoles]) {
    println!("VMs {}", output.len());
    let mut by_family: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for vm in output {
        by_family
            .entry(vm.file.clone())
            .or_default()
            .push(vm.roles.len());
    }
    for (fam, counts) in by_family {
        let total_roles = u32::try_from(counts.iter().sum::<usize>()).unwrap_or(u32::MAX);
        let vm_count = u32::try_from(counts.len().max(1)).unwrap_or(u32::MAX);
        let avg = f64::from(total_roles) / f64::from(vm_count);
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
    println!("\nTOP");
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
        .find(|vm| vm.decoder == gt.decoder_function_id)
        .context("ground decoder missing from reduced input")?;
    let mut role_by_ground_name = gt.register_roles;
    role_by_ground_name.extend(gt.helper_roles);
    let output = infer_vm_roles(&vms, ground, &role_by_ground_name, &hard_anchors(&scans));

    let json = serde_json::to_string_pretty(&output)?;
    if let Some(path) = args.output.as_ref() {
        fs::write(path, &json).with_context(|| format!("writing {}", path.display()))?;
    }
    print_summary(&output);
    Ok(())
}
