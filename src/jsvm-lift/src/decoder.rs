use crate::bytecode::{PushBuilderCandidate, WidthHint};
use oxc_ast::ast::{AssignmentTarget, Expression};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct BuilderSite {
    pub start: u32,
    pub end: u32,
    pub arguments: usize,
    pub width_hints: Vec<WidthHint>,
}

#[derive(Debug, Clone)]
pub enum IndexShape {
    AssignMul {
        base: String,
        ip: String,
        width: u64,
    },
    BaseOffset {
        base: String,
        offset: u64,
    },
    DirectMul {
        ip: String,
        width: u64,
    },
    Identifier(String),
}

#[derive(Debug, Clone)]
pub struct IndexedAccess {
    pub object: String,
    pub shape: IndexShape,
    pub start: u32,
    pub end: u32,
    pub preview: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct DecoderCandidate {
    pub function_id: String,
    pub object: String,
    pub builder_var: Option<String>,
    pub builder_start: Option<u32>,
    pub builder_end: Option<u32>,
    pub builder_arguments: Option<usize>,
    pub builder_width_hints: Vec<WidthHint>,
    pub base: Option<String>,
    pub ip: String,
    pub width: u64,
    pub operand_offsets: Vec<u64>,
    pub operand_vars: BTreeMap<u64, String>,
    pub selector_var: Option<String>,
    pub selector_masks: Vec<u64>,
    pub start: u32,
    pub end: u32,
    pub preview: String,
}

pub fn expr_ident(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::Identifier(id) => Some(id.name.to_string()),
        Expression::ParenthesizedExpression(paren) => expr_ident(&paren.expression),
        _ => None,
    }
}

pub fn target_ident(target: &AssignmentTarget<'_>) -> Option<String> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.to_string()),
        _ => None,
    }
}

fn numeric_u64(expr: &Expression<'_>) -> Option<u64> {
    match expr {
        Expression::NumericLiteral(n)
            if n.value.is_finite() && n.value >= 0.0 && n.value.fract() == 0.0 =>
        {
            Some(n.value as u64)
        }
        Expression::ParenthesizedExpression(paren) => numeric_u64(&paren.expression),
        _ => None,
    }
}

pub fn origin_ident(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::Identifier(id) => Some(id.name.to_string()),
        Expression::ParenthesizedExpression(paren) => origin_ident(&paren.expression),
        Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
            origin_ident(&assign.right)
        }
        _ => None,
    }
}

pub fn origin_u64(expr: &Expression<'_>) -> Option<u64> {
    match expr {
        Expression::NumericLiteral(n)
            if n.value.is_finite() && n.value >= 0.0 && n.value.fract() == 0.0 =>
        {
            Some(n.value as u64)
        }
        Expression::ParenthesizedExpression(paren) => origin_u64(&paren.expression),
        Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
            origin_u64(&assign.right)
        }
        _ => None,
    }
}

fn mul_width_ip(expr: &Expression<'_>) -> Option<(u64, String)> {
    let Expression::BinaryExpression(binary) = expr else {
        return None;
    };
    if binary.operator.as_str() != "*" {
        return None;
    }
    if let (Some(width), Some(ip)) = (numeric_u64(&binary.left), expr_ident(&binary.right)) {
        return Some((width, ip));
    }
    if let (Some(ip), Some(width)) = (expr_ident(&binary.left), numeric_u64(&binary.right)) {
        return Some((width, ip));
    }
    None
}

pub fn index_shape(expr: &Expression<'_>) -> Option<IndexShape> {
    match expr {
        Expression::ParenthesizedExpression(paren) => index_shape(&paren.expression),
        Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
            let target = target_ident(&assign.left)?;
            if let Some((width, ip)) = mul_width_ip(&assign.right) {
                return Some(IndexShape::AssignMul {
                    base: target,
                    ip,
                    width,
                });
            }
            if let Expression::BinaryExpression(binary) = &assign.right {
                if binary.operator.as_str() == "+" {
                    if let (Some(base), Some(offset)) =
                        (expr_ident(&binary.left), numeric_u64(&binary.right))
                    {
                        return Some(IndexShape::BaseOffset { base, offset });
                    }
                    if let (Some(offset), Some(base)) =
                        (numeric_u64(&binary.left), expr_ident(&binary.right))
                    {
                        return Some(IndexShape::BaseOffset { base, offset });
                    }
                }
            }
            if let Some(base) = expr_ident(&assign.right) {
                return Some(IndexShape::Identifier(base));
            }
            None
        }
        Expression::BinaryExpression(binary) if binary.operator.as_str() == "+" => {
            if let (Some(base), Some(offset)) =
                (expr_ident(&binary.left), numeric_u64(&binary.right))
            {
                return Some(IndexShape::BaseOffset { base, offset });
            }
            if let (Some(offset), Some(base)) =
                (numeric_u64(&binary.left), expr_ident(&binary.right))
            {
                return Some(IndexShape::BaseOffset { base, offset });
            }
            None
        }
        Expression::BinaryExpression(_) => {
            let (width, ip) = mul_width_ip(expr)?;
            Some(IndexShape::DirectMul { ip, width })
        }
        Expression::Identifier(id) => Some(IndexShape::Identifier(id.name.to_string())),
        _ => None,
    }
}

pub fn resolve_alias(name: &str, aliases: &HashMap<String, String>) -> String {
    let mut current = name.to_string();
    let mut seen = HashSet::new();
    while seen.insert(current.clone()) {
        let Some(next) = aliases.get(&current) else {
            break;
        };
        current.clone_from(next);
    }
    current
}

pub fn derive_candidates(function_id: &str, accesses: &[IndexedAccess]) -> Vec<DecoderCandidate> {
    let mut out = Vec::new();
    for access in accesses {
        match &access.shape {
            IndexShape::AssignMul { base, ip, width } => {
                if *width < 2 || *width > 16 {
                    continue;
                }
                let mut offsets = BTreeSet::new();
                offsets.insert(0u64);
                let mut end = access.end;
                for other in accesses {
                    if other.object != access.object {
                        continue;
                    }
                    match &other.shape {
                        IndexShape::BaseOffset {
                            base: other_base,
                            offset,
                        } if other_base == base && *offset < *width => {
                            offsets.insert(*offset);
                            end = end.max(other.end);
                        }
                        IndexShape::Identifier(other_base) if other_base == base => {
                            offsets.insert(0);
                            end = end.max(other.end);
                        }
                        _ => {}
                    }
                }
                out.push(DecoderCandidate {
                    function_id: function_id.to_string(),
                    object: access.object.clone(),
                    builder_var: None,
                    builder_start: None,
                    builder_end: None,
                    builder_arguments: None,
                    builder_width_hints: Vec::new(),
                    base: Some(base.clone()),
                    ip: ip.clone(),
                    width: *width,
                    operand_offsets: offsets.into_iter().collect(),
                    operand_vars: BTreeMap::new(),
                    selector_var: None,
                    selector_masks: Vec::new(),
                    start: access.start,
                    end,
                    preview: access.preview.clone(),
                });
            }
            IndexShape::DirectMul { ip, width } if *width >= 2 && *width <= 16 => {
                out.push(DecoderCandidate {
                    function_id: function_id.to_string(),
                    object: access.object.clone(),
                    builder_var: None,
                    builder_start: None,
                    builder_end: None,
                    builder_arguments: None,
                    builder_width_hints: Vec::new(),
                    base: None,
                    ip: ip.clone(),
                    width: *width,
                    operand_offsets: vec![0],
                    operand_vars: BTreeMap::new(),
                    selector_var: None,
                    selector_masks: Vec::new(),
                    start: access.start,
                    end: access.end,
                    preview: access.preview.clone(),
                });
            }
            _ => {}
        }
    }
    out.sort_by(|a, b| {
        (&a.function_id, &a.object, &a.base, &a.ip, a.width, a.start).cmp(&(
            &b.function_id,
            &b.object,
            &b.base,
            &b.ip,
            b.width,
            b.start,
        ))
    });
    out.dedup_by(|a, b| {
        a.function_id == b.function_id
            && a.object == b.object
            && a.base == b.base
            && a.ip == b.ip
            && a.width == b.width
    });
    out
}

pub fn annotate_bitfield_selectors(
    candidates: &mut [DecoderCandidate],
    indexed_value_vars: &HashMap<String, IndexedAccess>,
    bit_masks: &HashMap<String, BTreeSet<u64>>,
    aliases: &HashMap<String, String>,
) {
    let mut reads: Vec<_> = indexed_value_vars.iter().collect();
    reads.sort_by_key(|(_, access)| access.start);
    for candidate in candidates {
        for (var, access) in &reads {
            if access.object != candidate.object {
                continue;
            }
            let offset = match (&candidate.base, &access.shape) {
                (
                    Some(base),
                    IndexShape::AssignMul {
                        base: other_base,
                        ip,
                        width,
                    },
                ) if base == other_base && candidate.ip == *ip && candidate.width == *width => {
                    Some(0)
                }
                (
                    Some(base),
                    IndexShape::BaseOffset {
                        base: other_base,
                        offset,
                    },
                ) if base == other_base && *offset < candidate.width => Some(*offset),
                (Some(base), IndexShape::Identifier(other_base)) if base == other_base => Some(0),
                (None, IndexShape::DirectMul { ip, width })
                    if candidate.ip == *ip && candidate.width == *width =>
                {
                    Some(0)
                }
                _ => None,
            };
            let Some(offset) = offset else {
                continue;
            };
            candidate
                .operand_vars
                .entry(offset)
                .or_insert_with(|| (*var).clone());
            if offset == 0 && candidate.selector_var.is_none() {
                let resolved = resolve_alias(var, aliases);
                let masks = bit_masks.get(*var).or_else(|| bit_masks.get(&resolved));
                if let Some(masks) = masks {
                    if masks.len() >= 2 {
                        candidate.selector_var = Some((*var).clone());
                        candidate.selector_masks = masks.iter().copied().collect();
                    }
                }
            }
        }
    }
}

pub fn link_candidates(
    candidates: &mut [DecoderCandidate],
    aliases: &HashMap<String, String>,
    push_builder_vars: &BTreeSet<String>,
    push_builder_sites: &HashMap<String, BuilderSite>,
) {
    for candidate in candidates {
        if candidate.builder_var.is_some() {
            continue;
        }
        let resolved = resolve_alias(&candidate.object, aliases);
        if push_builder_vars.contains(&resolved) {
            candidate.builder_var = Some(resolved.clone());
            if let Some(site) = push_builder_sites.get(&resolved) {
                candidate.builder_start = Some(site.start);
                candidate.builder_end = Some(site.end);
                candidate.builder_arguments = Some(site.arguments);
                candidate.builder_width_hints.clone_from(&site.width_hints);
            }
        }
    }
}

pub fn complete_selector_masks(
    candidates: &mut [DecoderCandidate],
    builders: &[PushBuilderCandidate],
) {
    let builders_by_start: HashMap<u32, &PushBuilderCandidate> = builders
        .iter()
        .map(|builder| (builder.start, builder))
        .collect();
    for decoder in candidates {
        let (Some(builder_start), Ok(width)) =
            (decoder.builder_start, usize::try_from(decoder.width))
        else {
            continue;
        };
        if width == 0 {
            continue;
        }
        let Some(builder) = builders_by_start.get(&builder_start) else {
            continue;
        };
        let max_opcode = builder
            .values
            .iter()
            .enumerate()
            .filter(|(index, _)| index % width == 0)
            .filter_map(|(_, value)| *value)
            .max();
        let Some(max_opcode) = max_opcode else {
            continue;
        };
        let mut required = BTreeSet::new();
        required.extend(decoder.selector_masks.iter().copied());
        let mut bit = 1u64;
        while bit <= max_opcode && bit != 0 {
            required.insert(bit);
            let Some(next) = bit.checked_mul(2) else {
                break;
            };
            bit = next;
        }
        decoder.selector_masks = required.into_iter().collect();
    }
}

pub fn observed_opcodes(decoder: &DecoderCandidate, builders: &[PushBuilderCandidate]) -> Vec<u64> {
    let (Some(builder_start), Ok(width)) = (decoder.builder_start, usize::try_from(decoder.width))
    else {
        return Vec::new();
    };
    if width == 0 {
        return Vec::new();
    }
    let Some(builder) = builders
        .iter()
        .find(|builder| builder.start == builder_start)
    else {
        return Vec::new();
    };
    builder
        .values
        .chunks(width)
        .filter_map(|chunk| chunk.first().copied().flatten())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::PushBuilderCandidate;

    fn access(shape: IndexShape, start: u32) -> IndexedAccess {
        IndexedAccess {
            object: "code".to_string(),
            shape,
            start,
            end: start + 1,
            preview: "code[...]".to_string(),
        }
    }

    #[test]
    fn derives_annotates_and_links_decoder() {
        let accesses = vec![
            access(
                IndexShape::AssignMul {
                    base: "base".to_string(),
                    ip: "ip".to_string(),
                    width: 3,
                },
                10,
            ),
            access(
                IndexShape::BaseOffset {
                    base: "base".to_string(),
                    offset: 1,
                },
                11,
            ),
            access(IndexShape::Identifier("base".to_string()), 12),
        ];
        let mut candidates = derive_candidates("fn@test", &accesses);
        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].operand_offsets, vec![0, 1]);

        let mut indexed_value_vars = HashMap::new();
        indexed_value_vars.insert("opcode".to_string(), accesses[0].clone());
        let mut bit_masks = HashMap::new();
        bit_masks.insert("opcode".to_string(), BTreeSet::from([1, 2]));
        annotate_bitfield_selectors(
            &mut candidates,
            &indexed_value_vars,
            &bit_masks,
            &HashMap::new(),
        );
        assert_eq!(candidates[0].selector_var.as_deref(), Some("opcode"));
        assert_eq!(candidates[0].selector_masks, vec![1, 2]);

        let aliases = HashMap::from([("code".to_string(), "stream".to_string())]);
        let builder_vars = BTreeSet::from(["stream".to_string()]);
        let builder_sites = HashMap::from([(
            "stream".to_string(),
            BuilderSite {
                start: 100,
                end: 200,
                arguments: 12,
                width_hints: Vec::new(),
            },
        )]);
        link_candidates(&mut candidates, &aliases, &builder_vars, &builder_sites);
        assert_eq!(candidates[0].builder_var.as_deref(), Some("stream"));
        assert_eq!(candidates[0].builder_start, Some(100));

        let builders = vec![PushBuilderCandidate {
            start: 100,
            end: 200,
            receiver: "stream".to_string(),
            arguments: 12,
            numeric_literals: 12,
            byte_literals: 12,
            call_arguments: 0,
            other_arguments: 0,
            width_hints: Vec::new(),
            values: vec![
                Some(0),
                Some(9),
                Some(9),
                Some(1),
                Some(8),
                Some(8),
                Some(2),
                Some(7),
                Some(7),
                Some(3),
                Some(6),
                Some(6),
            ],
            unknowns: Vec::new(),
            preview: "stream.push(...)".to_string(),
        }];
        complete_selector_masks(&mut candidates, &builders);
        assert_eq!(candidates[0].selector_masks, vec![1, 2]);
        assert_eq!(
            observed_opcodes(&candidates[0], &builders),
            vec![0, 1, 2, 3]
        );
    }

    #[test]
    fn alias_resolution_stops_on_cycles() {
        let aliases = HashMap::from([
            ("a".to_string(), "b".to_string()),
            ("b".to_string(), "a".to_string()),
        ]);
        assert!(matches!(resolve_alias("a", &aliases).as_str(), "a" | "b"));
    }
}
