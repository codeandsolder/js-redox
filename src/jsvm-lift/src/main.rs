mod state_flatten;
mod table_vm;

use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{Argument, ArrayExpressionElement, Expression, ObjectPropertyKind},
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, SourceType};
use oxc_syntax::scope::ScopeFlags;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use state_flatten::{
    detect_for_state_machines, DecoderControlInfo, IfLadderStateMachineCandidate,
    OpcodeMapCandidate, StateMachineCandidate, StateMachineInfo,
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Detect and inventory JavaScript VM-obfuscation structures")]
struct Args {
    #[arg(required = true)]
    files: Vec<PathBuf>,

    /// Emit one JSON object per file.
    #[arg(long)]
    json: bool,

    /// Minimum VM-likelihood score for text output.
    #[arg(long, default_value_t = 8)]
    min_score: u32,

    /// Materialize statically recovered Function(...) bodies as synthetic JS files.
    #[arg(long)]
    dump_embedded: Option<PathBuf>,
}

#[derive(Debug, Clone, Serialize)]
struct WidthHint {
    width: usize,
    opcode_unique: usize,
    opcode_max: u64,
    operand_max: u64,
    score: i32,
}

#[derive(Debug, Clone, Serialize)]
struct ArrayCandidate {
    start: u32,
    end: u32,
    elements: usize,
    numeric: usize,
    byte_values: usize,
    numeric_ratio: f64,
    width_hints: Vec<WidthHint>,
    preview: String,
}

#[derive(Debug, Clone, Serialize)]
struct BuilderUnknown {
    index: usize,
    preview: String,
}

#[derive(Debug, Clone, Serialize)]
struct PushBuilderCandidate {
    start: u32,
    end: u32,
    receiver: String,
    arguments: usize,
    numeric_literals: usize,
    byte_literals: usize,
    call_arguments: usize,
    other_arguments: usize,
    width_hints: Vec<WidthHint>,
    values: Vec<Option<u64>>,
    unknowns: Vec<BuilderUnknown>,
    preview: String,
}

#[derive(Debug, Clone)]
struct BuilderSite {
    start: u32,
    end: u32,
    arguments: usize,
    width_hints: Vec<WidthHint>,
}

#[derive(Debug, Clone)]
enum IndexShape {
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
struct IndexedAccess {
    object: String,
    shape: IndexShape,
    start: u32,
    end: u32,
    preview: String,
}

#[derive(Debug, Clone, Serialize)]
struct DecoderCandidate {
    function_id: String,
    object: String,
    builder_var: Option<String>,
    builder_start: Option<u32>,
    builder_end: Option<u32>,
    builder_arguments: Option<usize>,
    builder_width_hints: Vec<WidthHint>,
    base: Option<String>,
    ip: String,
    width: u64,
    operand_offsets: Vec<u64>,
    operand_vars: BTreeMap<u64, String>,
    selector_var: Option<String>,
    selector_masks: Vec<u64>,
    start: u32,
    end: u32,
    preview: String,
}

#[derive(Debug, Clone, Serialize)]
struct HandlerTableCandidate {
    start: u32,
    end: u32,
    container_kind: String,
    properties: usize,
    function_values: usize,
    async_function_values: usize,
    preview: String,
}

#[derive(Debug, Clone, Serialize)]
struct DirectSwitchHandler {
    key: Option<u64>,
    key_source: Option<String>,
    semantic: Vec<String>,
    terminal: String,
}

#[derive(Debug, Clone, Serialize)]
struct DirectSwitchMapCandidate {
    parent_function_id: String,
    start: u32,
    end: u32,
    selector: String,
    numeric_cases: usize,
    opcode_max: u64,
    vm_evidence_score: u32,
    vm_reasons: Vec<String>,
    confirmed_vm: bool,
    handlers: Vec<DirectSwitchHandler>,
}

#[derive(Debug, Clone)]
struct EmbeddedCodeCandidate {
    outer_start: u32,
    outer_end: u32,
    kind: String,
    params: Vec<String>,
    body: String,
}

#[derive(Debug, Serialize)]
struct EmbeddedScanReport {
    outer_start: u32,
    outer_end: u32,
    kind: String,
    body_bytes: usize,
    dump_path: Option<String>,
    diagnostics: usize,
    panicked: bool,
    arrays: Vec<ArrayCandidate>,
    push_builders: Vec<PushBuilderCandidate>,
    decoder_candidates: Vec<DecoderCandidate>,
    state_machines: Vec<StateMachineCandidate>,
    if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    opcode_maps: Vec<OpcodeMapCandidate>,
    direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    handler_tables: Vec<HandlerTableCandidate>,
    handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    table_vms: Vec<table_vm::TableVmCandidate>,
    functions: Vec<FunctionMetrics>,
    embedded: Vec<EmbeddedScanReport>,
}

#[derive(Debug, Clone, Default, Serialize)]
struct FunctionMetrics {
    id: String,
    kind: String,
    name: Option<String>,
    start: u32,
    end: u32,
    bytes: usize,
    switches: usize,
    switch_cases: usize,
    loops: usize,
    conditionals: usize,
    computed_members: usize,
    computed_calls: usize,
    calls: usize,
    assignments: usize,
    binary_exprs: usize,
    unary_exprs: usize,
    sequence_exprs: usize,
    arrays: usize,
    large_arrays: usize,
    numeric_literals: usize,
    string_literals: usize,
    tries: usize,
    confirmed_dispatch: bool,
    dispatch_reasons: Vec<String>,
    indexed_read_chain: Vec<String>,
    score: u32,
    reasons: Vec<String>,
}

#[derive(Debug, Serialize)]
struct ScanReport {
    file: String,
    bytes: usize,
    diagnostics: usize,
    panicked: bool,
    arrays: Vec<ArrayCandidate>,
    push_builders: Vec<PushBuilderCandidate>,
    decoder_candidates: Vec<DecoderCandidate>,
    state_machines: Vec<StateMachineCandidate>,
    if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    opcode_maps: Vec<OpcodeMapCandidate>,
    direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    handler_tables: Vec<HandlerTableCandidate>,
    handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    table_vms: Vec<table_vm::TableVmCandidate>,
    functions: Vec<FunctionMetrics>,
    embedded: Vec<EmbeddedScanReport>,
}

#[derive(Debug, Clone, Default)]
struct ExprEvidence {
    computed_members: usize,
    calls: usize,
    identifiers: BTreeSet<String>,
    computed_previews: BTreeSet<String>,
}

struct EvidenceVisitor<'s> {
    source: &'s str,
    evidence: ExprEvidence,
}

impl<'a> Visit<'a> for EvidenceVisitor<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::ComputedMemberExpression(cm) => {
                self.evidence.computed_members += 1;
                let start = cm.span.start as usize;
                let end = (cm.span.end as usize).min(self.source.len());
                if let Some(raw) = self.source.get(start..end) {
                    let mut preview = raw.split_whitespace().collect::<Vec<_>>().join(" ");
                    if preview.len() > 160 {
                        preview.truncate(160);
                    }
                    self.evidence.computed_previews.insert(preview);
                }
            }
            AstKind::CallExpression(_) => self.evidence.calls += 1,
            AstKind::IdentifierReference(id) => {
                self.evidence.identifiers.insert(id.name.to_string());
            }
            _ => {}
        }
    }
}

fn expression_evidence(source: &str, expr: &Expression<'_>) -> ExprEvidence {
    let mut v = EvidenceVisitor {
        source,
        evidence: ExprEvidence::default(),
    };
    v.visit_expression(expr);
    v.evidence
}

#[derive(Default)]
struct FunctionBuilder {
    m: FunctionMetrics,
    vars: HashMap<String, ExprEvidence>,
    switch_inputs: Vec<ExprEvidence>,
    computed_call_indices: Vec<ExprEvidence>,
    local_function_table_lengths: Vec<usize>,
    local_numeric_array_lengths: Vec<usize>,
    aliases: HashMap<String, String>,
    push_builder_vars: BTreeSet<String>,
    push_builder_sites: HashMap<String, BuilderSite>,
    indexed_accesses: Vec<IndexedAccess>,
    child_indexed_accesses: Vec<IndexedAccess>,
    indexed_value_vars: HashMap<String, IndexedAccess>,
    bit_masks: HashMap<String, BTreeSet<u64>>,
    decoder_candidates: Vec<DecoderCandidate>,
}

struct Scanner<'s> {
    source: &'s str,
    arrays: Vec<ArrayCandidate>,
    push_builders: Vec<PushBuilderCandidate>,
    decoder_candidates: Vec<DecoderCandidate>,
    state_machines: Vec<StateMachineCandidate>,
    if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    opcode_maps: Vec<OpcodeMapCandidate>,
    direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    handler_tables: Vec<HandlerTableCandidate>,
    functions: Vec<FunctionMetrics>,
    embedded_code: Vec<EmbeddedCodeCandidate>,
    stack: Vec<FunctionBuilder>,
}

impl<'s> Scanner<'s> {
    fn new(source: &'s str) -> Self {
        Self {
            source,
            arrays: Vec::new(),
            push_builders: Vec::new(),
            decoder_candidates: Vec::new(),
            state_machines: Vec::new(),
            if_ladder_state_machines: Vec::new(),
            opcode_maps: Vec::new(),
            direct_switch_maps: Vec::new(),
            handler_tables: Vec::new(),
            functions: Vec::new(),
            embedded_code: Vec::new(),
            stack: Vec::new(),
        }
    }

    fn source_preview(&self, start: u32, end: u32, cap: usize) -> String {
        let start = start as usize;
        let end = (end as usize).min(self.source.len());
        let s = self.source.get(start..end).unwrap_or_default();
        let mut out = String::with_capacity(cap.min(s.len()));
        for c in s.chars() {
            if out.len() >= cap {
                break;
            }
            out.push(if c.is_whitespace() { ' ' } else { c });
        }
        out
    }

    fn expr_ident(expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::Identifier(id) => Some(id.name.to_string()),
            Expression::ParenthesizedExpression(p) => Self::expr_ident(&p.expression),
            _ => None,
        }
    }

    fn target_ident(target: &oxc_ast::ast::AssignmentTarget<'_>) -> Option<String> {
        match target {
            oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(id) => {
                Some(id.name.to_string())
            }
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
            Expression::ParenthesizedExpression(p) => Self::numeric_u64(&p.expression),
            _ => None,
        }
    }

    fn origin_ident(expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::Identifier(id) => Some(id.name.to_string()),
            Expression::ParenthesizedExpression(p) => Self::origin_ident(&p.expression),
            Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
                Self::origin_ident(&assign.right)
            }
            _ => None,
        }
    }

    fn origin_u64(expr: &Expression<'_>) -> Option<u64> {
        match expr {
            Expression::NumericLiteral(n)
                if n.value.is_finite() && n.value >= 0.0 && n.value.fract() == 0.0 =>
            {
                Some(n.value as u64)
            }
            Expression::ParenthesizedExpression(p) => Self::origin_u64(&p.expression),
            Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
                Self::origin_u64(&assign.right)
            }
            _ => None,
        }
    }

    fn mul_width_ip(expr: &Expression<'_>) -> Option<(u64, String)> {
        let Expression::BinaryExpression(bin) = expr else {
            return None;
        };
        if bin.operator.as_str() != "*" {
            return None;
        }

        if let (Some(width), Some(ip)) =
            (Self::numeric_u64(&bin.left), Self::expr_ident(&bin.right))
        {
            return Some((width, ip));
        }
        if let (Some(ip), Some(width)) =
            (Self::expr_ident(&bin.left), Self::numeric_u64(&bin.right))
        {
            return Some((width, ip));
        }
        None
    }

    fn index_shape(expr: &Expression<'_>) -> Option<IndexShape> {
        match expr {
            Expression::ParenthesizedExpression(p) => Self::index_shape(&p.expression),
            Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
                let target = Self::target_ident(&assign.left)?;
                if let Some((width, ip)) = Self::mul_width_ip(&assign.right) {
                    return Some(IndexShape::AssignMul {
                        base: target,
                        ip,
                        width,
                    });
                }
                if let Expression::BinaryExpression(bin) = &assign.right {
                    if bin.operator.as_str() == "+" {
                        if let (Some(base), Some(offset)) =
                            (Self::expr_ident(&bin.left), Self::numeric_u64(&bin.right))
                        {
                            return Some(IndexShape::BaseOffset { base, offset });
                        }
                        if let (Some(offset), Some(base)) =
                            (Self::numeric_u64(&bin.left), Self::expr_ident(&bin.right))
                        {
                            return Some(IndexShape::BaseOffset { base, offset });
                        }
                    }
                }
                if let Some(base) = Self::expr_ident(&assign.right) {
                    return Some(IndexShape::Identifier(base));
                }
                None
            }
            Expression::BinaryExpression(bin) if bin.operator.as_str() == "+" => {
                if let (Some(base), Some(offset)) =
                    (Self::expr_ident(&bin.left), Self::numeric_u64(&bin.right))
                {
                    return Some(IndexShape::BaseOffset { base, offset });
                }
                if let (Some(offset), Some(base)) =
                    (Self::numeric_u64(&bin.left), Self::expr_ident(&bin.right))
                {
                    return Some(IndexShape::BaseOffset { base, offset });
                }
                None
            }
            Expression::BinaryExpression(_) => {
                let (width, ip) = Self::mul_width_ip(expr)?;
                Some(IndexShape::DirectMul { ip, width })
            }
            Expression::Identifier(id) => Some(IndexShape::Identifier(id.name.to_string())),
            _ => None,
        }
    }

    fn resolve_alias(name: &str, aliases: &HashMap<String, String>) -> String {
        let mut current = name.to_string();
        let mut seen = HashSet::new();
        while seen.insert(current.clone()) {
            let Some(next) = aliases.get(&current) else {
                break;
            };
            current = next.clone();
        }
        current
    }

    fn builder_receiver_ident(expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::Identifier(id) => Some(id.name.to_string()),
            Expression::AssignmentExpression(assign) if assign.operator.is_assign() => {
                Self::target_ident(&assign.left)
            }
            Expression::ParenthesizedExpression(p) => Self::builder_receiver_ident(&p.expression),
            _ => None,
        }
    }

    fn push_function(&mut self, kind: &str, name: Option<String>, start: u32, end: u32) {
        let bytes = end.saturating_sub(start) as usize;
        self.stack.push(FunctionBuilder {
            m: FunctionMetrics {
                id: format!("fn@{start:x}-{end:x}"),
                kind: kind.to_string(),
                name,
                start,
                end,
                bytes,
                ..FunctionMetrics::default()
            },
            ..FunctionBuilder::default()
        });
    }

    fn evidence_reaches_computed(
        evidence: &ExprEvidence,
        vars: &HashMap<String, ExprEvidence>,
        seen: &mut HashSet<String>,
    ) -> bool {
        if evidence.computed_members > 0 {
            return true;
        }
        for name in &evidence.identifiers {
            if !seen.insert(name.clone()) {
                continue;
            }
            if let Some(next) = vars.get(name) {
                if Self::evidence_reaches_computed(next, vars, seen) {
                    return true;
                }
            }
        }
        false
    }

    fn collect_indexed_reads(
        evidence: &ExprEvidence,
        vars: &HashMap<String, ExprEvidence>,
        seen: &mut HashSet<String>,
        out: &mut BTreeSet<String>,
    ) {
        out.extend(evidence.computed_previews.iter().cloned());
        for name in &evidence.identifiers {
            if !seen.insert(name.clone()) {
                continue;
            }
            if let Some(next) = vars.get(name) {
                Self::collect_indexed_reads(next, vars, seen, out);
            }
        }
    }

    fn derive_decoder_candidates(
        function_id: &str,
        accesses: &[IndexedAccess],
    ) -> Vec<DecoderCandidate> {
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

    fn annotate_bitfield_selectors(
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
                    (Some(base), IndexShape::Identifier(other_base)) if base == other_base => {
                        Some(0)
                    }
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
                    let resolved = Self::resolve_alias(var, aliases);
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

    fn link_decoder_candidates(
        candidates: &mut [DecoderCandidate],
        aliases: &HashMap<String, String>,
        push_builder_vars: &BTreeSet<String>,
        push_builder_sites: &HashMap<String, BuilderSite>,
    ) {
        for candidate in candidates {
            if candidate.builder_var.is_some() {
                continue;
            }
            let resolved = Self::resolve_alias(&candidate.object, aliases);
            if push_builder_vars.contains(&resolved) {
                candidate.builder_var = Some(resolved.clone());
                if let Some(site) = push_builder_sites.get(&resolved) {
                    candidate.builder_start = Some(site.start);
                    candidate.builder_end = Some(site.end);
                    candidate.builder_arguments = Some(site.arguments);
                    candidate.builder_width_hints = site.width_hints.clone();
                }
            }
        }
    }

    fn complete_selector_masks(
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

    fn observed_opcodes(decoder: &DecoderCandidate, builders: &[PushBuilderCandidate]) -> Vec<u64> {
        let (Some(builder_start), Ok(width)) =
            (decoder.builder_start, usize::try_from(decoder.width))
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

    fn analyze_opcode_maps(&mut self, function: &oxc_ast::ast::Function<'_>) {
        let (
            parent_function_id,
            mut decoder_candidates,
            accesses,
            indexed_value_vars,
            bit_masks,
            aliases,
            push_builder_vars,
            push_builder_sites,
        ) = {
            let Some(current) = self.stack.last() else {
                return;
            };
            let mut accesses = current.indexed_accesses.clone();
            accesses.extend(current.child_indexed_accesses.iter().cloned());
            (
                current.m.id.clone(),
                current.decoder_candidates.clone(),
                accesses,
                current.indexed_value_vars.clone(),
                current.bit_masks.clone(),
                current.aliases.clone(),
                current.push_builder_vars.clone(),
                current.push_builder_sites.clone(),
            )
        };

        // At function-exit child decoders have already propagated, but local
        // indexed reads have not yet gone through finish_function(). Derive
        // those here as well so opcode flattening does not depend on a nested
        // closure layout.
        let mut local = Self::derive_decoder_candidates(&parent_function_id, &accesses);
        Self::annotate_bitfield_selectors(&mut local, &indexed_value_vars, &bit_masks, &aliases);
        Self::link_decoder_candidates(
            &mut local,
            &aliases,
            &push_builder_vars,
            &push_builder_sites,
        );
        decoder_candidates.extend(local);
        Self::link_decoder_candidates(
            &mut decoder_candidates,
            &aliases,
            &push_builder_vars,
            &push_builder_sites,
        );

        // A selector bit can be decoded in a sibling fetch-control state and
        // therefore be absent from local AST mask tracking. Once the stream is
        // linked, observed opcode values give a conservative lower bound for
        // the selector width. Complete the domain before state simulation.
        Self::complete_selector_masks(&mut decoder_candidates, &self.push_builders);

        let mut seen_decoders = BTreeSet::new();
        let decoders: Vec<DecoderControlInfo> = decoder_candidates
            .iter()
            .filter_map(|decoder| {
                let selector_var = decoder.selector_var.as_ref()?;
                if decoder.selector_masks.len() < 2 {
                    return None;
                }
                let key = (
                    decoder.function_id.clone(),
                    selector_var.clone(),
                    decoder.selector_masks.clone(),
                );
                if !seen_decoders.insert(key.clone()) {
                    return None;
                }
                let observed_source = decoder_candidates
                    .iter()
                    .find(|candidate| {
                        candidate.function_id == decoder.function_id
                            && candidate.selector_var == decoder.selector_var
                            && candidate.builder_start.is_some()
                    })
                    .unwrap_or(decoder);
                let observed_opcodes = Self::observed_opcodes(observed_source, &self.push_builders);
                Some(DecoderControlInfo {
                    function_id: key.0,
                    selector_var: key.1,
                    selector_masks: key.2,
                    observed_opcodes,
                })
            })
            .collect();

        if decoders.is_empty() {
            return;
        }

        let machines: Vec<StateMachineInfo> = self
            .state_machines
            .iter()
            .filter(|machine| machine.function_id == parent_function_id)
            .map(|machine| StateMachineInfo {
                start: machine.start,
                end: machine.end,
                state_var: machine.state_var.clone(),
                init_state: machine.init_state,
                mask: machine.mask,
                shift: machine.shift,
                selector_var: machine.selector_var.clone(),
            })
            .collect();

        if machines.is_empty() {
            return;
        }

        let mut maps = state_flatten::analyze_function(
            self.source,
            function,
            &parent_function_id,
            &decoders,
            &machines,
        );
        self.opcode_maps.append(&mut maps);
    }

    fn finish_function(&mut self) {
        let Some(mut b) = self.stack.pop() else {
            return;
        };

        let mut decoder_accesses = b.indexed_accesses.clone();
        decoder_accesses.extend(b.child_indexed_accesses.iter().cloned());
        let mut local_decoders = Self::derive_decoder_candidates(&b.m.id, &decoder_accesses);
        Self::annotate_bitfield_selectors(
            &mut local_decoders,
            &b.indexed_value_vars,
            &b.bit_masks,
            &b.aliases,
        );
        b.decoder_candidates.extend(local_decoders);
        Self::link_decoder_candidates(
            &mut b.decoder_candidates,
            &b.aliases,
            &b.push_builder_vars,
            &b.push_builder_sites,
        );

        let m = &mut b.m;
        let mut score = 0u32;
        let mut reasons = Vec::new();
        let mut dispatch_reasons = Vec::new();

        // Confirmation follows the stricter retained direct-switch map.
        // The broad indexed-state heuristic remains useful for scoring, but
        // alone it is too permissive for parser/evaluator state machines.
        let switch_from_indexed_state = self
            .direct_switch_maps
            .iter()
            .any(|map| map.parent_function_id == m.id && map.confirmed_vm);
        if switch_from_indexed_state {
            dispatch_reasons
                .push("large switch discriminant traces to computed/indexed state".to_string());
        }

        let large_handler_table_present =
            self.handler_tables.iter().any(|h| h.function_values >= 16);
        let index_reaches_computed = b
            .computed_call_indices
            .iter()
            .any(|e| Self::evidence_reaches_computed(e, &b.vars, &mut HashSet::new()));
        let local_table_schedule_pair = b
            .local_function_table_lengths
            .iter()
            .any(|len| b.local_numeric_array_lengths.iter().any(|n| n == len));
        let table_dispatch = m.loops > 0
            && !b.computed_call_indices.is_empty()
            && (large_handler_table_present
                || (local_table_schedule_pair && index_reaches_computed));
        if table_dispatch {
            dispatch_reasons.push(if large_handler_table_present {
                "looped computed call with a large function-valued handler table".to_string()
            } else {
                "looped computed call uses a same-sized function table and numeric schedule"
                    .to_string()
            });
        }

        m.confirmed_dispatch = switch_from_indexed_state || table_dispatch;
        m.dispatch_reasons = dispatch_reasons;
        let mut indexed_reads = BTreeSet::new();
        if switch_from_indexed_state {
            for e in &b.switch_inputs {
                Self::collect_indexed_reads(e, &b.vars, &mut HashSet::new(), &mut indexed_reads);
            }
        }
        m.indexed_read_chain = indexed_reads.into_iter().collect();

        if m.switch_cases >= 16 {
            score += 8;
            reasons.push(format!("{} switch cases", m.switch_cases));
        } else if m.switches > 0 {
            score += 3;
            reasons.push(format!("{} switch(es)", m.switches));
        }
        if m.loops > 0 {
            score += 3.min(m.loops as u32 + 1);
            reasons.push(format!("{} loop(s)", m.loops));
        }
        if m.conditionals >= 30 {
            score += 5;
            reasons.push(format!("{} ternaries", m.conditionals));
        } else if m.conditionals >= 10 {
            score += 2;
            reasons.push(format!("{} ternaries", m.conditionals));
        }
        if m.computed_members >= 25 {
            score += 5;
            reasons.push(format!(
                "{} computed member reads/writes",
                m.computed_members
            ));
        } else if m.computed_members >= 8 {
            score += 2;
            reasons.push(format!(
                "{} computed member reads/writes",
                m.computed_members
            ));
        }
        if m.loops > 0 && m.computed_calls > 0 && m.computed_members >= 2 {
            score += 6;
            reasons.push(format!(
                "{} computed call(s) inside a loop-shaped function",
                m.computed_calls
            ));
        }
        if m.large_arrays > 0 {
            score += 6;
            reasons.push(format!("{} large literal array(s)", m.large_arrays));
        }
        if m.sequence_exprs >= 12 {
            score += 2;
            reasons.push(format!("{} sequence expressions", m.sequence_exprs));
        }
        if m.binary_exprs >= 80 {
            score += 2;
            reasons.push(format!("{} binary expressions", m.binary_exprs));
        }
        if m.bytes >= 20_000 {
            score += 4;
            reasons.push(format!("{} byte function body", m.bytes));
        } else if m.bytes >= 5_000 {
            score += 2;
            reasons.push(format!("{} byte function body", m.bytes));
        }

        m.score = score;
        m.reasons = reasons;

        let propagated_decoders = b.decoder_candidates.clone();
        let propagated_local_accesses = b.indexed_accesses.clone();
        self.functions.push(b.m);
        if let Some(parent) = self.stack.last_mut() {
            parent.decoder_candidates.extend(propagated_decoders);
            parent
                .child_indexed_accesses
                .extend(propagated_local_accesses);
        } else {
            self.decoder_candidates.extend(propagated_decoders);
        }
    }

    fn record_push_builder(&mut self, call: &oxc_ast::ast::CallExpression<'_>) {
        let Expression::StaticMemberExpression(member) = &call.callee else {
            return;
        };
        if member.property.name.as_str() != "push" || call.arguments.len() < 16 {
            return;
        }

        let mut numeric_literals = 0usize;
        let mut byte_literals = 0usize;
        let mut call_arguments = 0usize;
        let mut other_arguments = 0usize;
        let mut values = Vec::with_capacity(call.arguments.len());
        let mut unknowns = Vec::new();

        for (arg_index, arg) in call.arguments.iter().enumerate() {
            match arg {
                Argument::NumericLiteral(n) => {
                    numeric_literals += 1;
                    if n.value.is_finite() && n.value >= 0.0 && n.value.fract() == 0.0 {
                        let value = n.value as u64;
                        if value <= 255 {
                            byte_literals += 1;
                        }
                        values.push(Some(value));
                    } else {
                        values.push(None);
                    }
                }
                Argument::CallExpression(_) => {
                    call_arguments += 1;
                    values.push(None);
                    let span = arg.span();
                    unknowns.push(BuilderUnknown {
                        index: arg_index,
                        preview: self.source_preview(span.start, span.end, 120),
                    });
                }
                _ => {
                    other_arguments += 1;
                    values.push(None);
                    let span = arg.span();
                    unknowns.push(BuilderUnknown {
                        index: arg_index,
                        preview: self.source_preview(span.start, span.end, 120),
                    });
                }
            }
        }

        let recognized = numeric_literals + call_arguments;
        if recognized * 4 < call.arguments.len() * 3 {
            return;
        }

        let mut width_hints = Vec::new();
        for width in 2usize..=8 {
            if call.arguments.len() < width * 8 || !call.arguments.len().is_multiple_of(width) {
                continue;
            }
            let instructions = call.arguments.len() / width;
            let mut opcode_values = BTreeSet::new();
            let mut opcode_max = 0u64;
            let mut operand_max = 0u64;
            let mut known_opcodes = 0usize;

            for (i, value) in values.iter().enumerate() {
                let Some(value) = value else { continue };
                if i % width == 0 {
                    known_opcodes += 1;
                    opcode_values.insert(*value);
                    opcode_max = opcode_max.max(*value);
                } else {
                    operand_max = operand_max.max(*value);
                }
            }

            if known_opcodes * 2 < instructions {
                continue;
            }

            let mut score = 2i32;
            if known_opcodes * 4 >= instructions * 3 {
                score += 3;
            } else {
                score += 1;
            }
            if opcode_max <= 63 {
                score += 4;
            } else if opcode_max <= 127 {
                score += 2;
            }
            if opcode_values.len() <= 64 {
                score += 2;
            }
            if opcode_values.len() * 2 <= instructions {
                score += 1;
            }
            if operand_max > opcode_max.saturating_mul(2) {
                score += 2;
            }

            if score >= 7 {
                width_hints.push(WidthHint {
                    width,
                    opcode_unique: opcode_values.len(),
                    opcode_max,
                    operand_max,
                    score,
                });
            }
        }
        width_hints.sort_by_key(|h| std::cmp::Reverse(h.score));

        let receiver_ident = Self::builder_receiver_ident(&member.object);
        if let Some(name) = &receiver_ident {
            if let Some(cur) = self.stack.last_mut() {
                cur.push_builder_vars.insert(name.clone());
                cur.push_builder_sites.insert(
                    name.clone(),
                    BuilderSite {
                        start: call.span.start,
                        end: call.span.end,
                        arguments: call.arguments.len(),
                        width_hints: width_hints.clone(),
                    },
                );
            }
        }

        let span = member.object.span();
        self.push_builders.push(PushBuilderCandidate {
            start: call.span.start,
            end: call.span.end,
            receiver: self.source_preview(span.start, span.end, 96),
            arguments: call.arguments.len(),
            numeric_literals,
            byte_literals,
            call_arguments,
            other_arguments,
            width_hints,
            values,
            unknowns,
            preview: self.source_preview(call.span.start, call.span.end, 140),
        });
    }

    fn record_literal_string_join(&mut self, call: &oxc_ast::ast::CallExpression<'_>) {
        if call.optional || call.arguments.len() != 1 {
            return;
        }
        let Expression::StaticMemberExpression(member) = &call.callee else {
            return;
        };
        if member.optional || member.property.name.as_str() != "join" {
            return;
        }
        let Expression::ArrayExpression(array) = &member.object else {
            return;
        };
        let Argument::StringLiteral(separator) = &call.arguments[0] else {
            return;
        };

        let mut parts = Vec::with_capacity(array.elements.len());
        for element in &array.elements {
            let ArrayExpressionElement::StringLiteral(value) = element else {
                return;
            };
            parts.push(value.value.as_str());
        }
        if parts.len() < 2 {
            return;
        }

        let body = parts.join(separator.value.as_str());
        if body.len() < 1024 || body.len() > 5_000_000 {
            return;
        }
        let looks_like_code = body.contains("function")
            && (body.contains("for(")
                || body.contains("for (")
                || body.contains("switch(")
                || body.contains("switch (")
                || body.contains("=>"));
        if !looks_like_code {
            return;
        }

        self.embedded_code.push(EmbeddedCodeCandidate {
            outer_start: call.span.start,
            outer_end: call.span.end,
            kind: "literal Array.join".to_string(),
            params: Vec::new(),
            body,
        });
    }

    fn record_function_constructor(
        &mut self,
        kind: &str,
        start: u32,
        end: u32,
        args: &[Argument<'_>],
    ) {
        if args.is_empty() {
            return;
        }

        let mut strings = Vec::with_capacity(args.len());
        for arg in args {
            let Argument::StringLiteral(s) = arg else {
                return;
            };
            strings.push(s.value.to_string());
        }

        let Some(body) = strings.pop() else {
            return;
        };
        if body.len() < 128 || body.len() > 5_000_000 {
            return;
        }

        self.embedded_code.push(EmbeddedCodeCandidate {
            outer_start: start,
            outer_end: end,
            kind: kind.to_string(),
            params: strings,
            body,
        });
    }

    fn record_direct_switch(&mut self, sw: &oxc_ast::ast::SwitchStatement<'_>) {
        if sw.cases.len() < 8 {
            return;
        }
        let Some(current) = self.stack.last() else {
            return;
        };
        if current.m.loops == 0 {
            return;
        }

        let evidence = expression_evidence(self.source, &sw.discriminant);
        let indexed_selector =
            Self::evidence_reaches_computed(&evidence, &current.vars, &mut HashSet::new());
        let call_selector = evidence.calls > 0;
        if !indexed_selector && !call_selector {
            return;
        }

        let mut handlers = Vec::with_capacity(sw.cases.len());
        let mut numeric_cases = 0usize;
        let mut opcode_max = 0u64;
        for case in &sw.cases {
            let key = case.test.as_ref().and_then(Self::numeric_u64);
            if let Some(value) = key {
                numeric_cases += 1;
                opcode_max = opcode_max.max(value);
            }
            let key_source = case
                .test
                .as_ref()
                .map(|expr| self.source_preview(expr.span().start, expr.span().end, usize::MAX));

            let mut semantic = Vec::new();
            let mut terminal = "fallthrough".to_string();
            for stmt in &case.consequent {
                match stmt {
                    oxc_ast::ast::Statement::BreakStatement(_) => {
                        terminal = "break".to_string();
                    }
                    oxc_ast::ast::Statement::ContinueStatement(_) => {
                        terminal = "continue".to_string();
                    }
                    oxc_ast::ast::Statement::ReturnStatement(_) => {
                        terminal = "return".to_string();
                        semantic.push(self.source_preview(
                            stmt.span().start,
                            stmt.span().end,
                            usize::MAX,
                        ));
                    }
                    oxc_ast::ast::Statement::ThrowStatement(_) => {
                        terminal = "throw".to_string();
                        semantic.push(self.source_preview(
                            stmt.span().start,
                            stmt.span().end,
                            usize::MAX,
                        ));
                    }
                    _ => semantic.push(self.source_preview(
                        stmt.span().start,
                        stmt.span().end,
                        usize::MAX,
                    )),
                }
            }

            handlers.push(DirectSwitchHandler {
                key,
                key_source,
                semantic,
                terminal,
            });
        }

        // VM dispatch switches are overwhelmingly numeric opcode tables.
        // Parser/evaluator switches can have a handful of numeric arms mixed
        // with symbolic cases, so require a strong numeric-case majority.
        if numeric_cases < 8 || numeric_cases * 4 < sw.cases.len() * 3 {
            return;
        }

        let selector = self.source_preview(
            sw.discriminant.span().start,
            sw.discriminant.span().end,
            usize::MAX,
        );
        let semantic_fragments = handlers
            .iter()
            .flat_map(|handler| handler.semantic.iter())
            .collect::<Vec<_>>();
        let stack_ops = semantic_fragments
            .iter()
            .filter(|source| {
                source.contains(".push(") || source.contains(".pop(") || source.contains(".splice(")
            })
            .count();
        let cursor_ops = semantic_fragments
            .iter()
            .filter(|source| {
                (source.contains("++") || source.contains("--"))
                    && (source.contains('[') || source.contains(".length"))
            })
            .count();
        let continue_handlers = handlers
            .iter()
            .filter(|handler| handler.terminal == "continue")
            .count();

        let mut vm_evidence_score = 0u32;
        let mut vm_reasons = Vec::new();
        if numeric_cases >= 16 {
            vm_evidence_score += 2;
            vm_reasons.push(format!("{numeric_cases} numeric opcode-like cases"));
        }
        if stack_ops >= 3 {
            vm_evidence_score += 3;
            vm_reasons.push(format!("{stack_ops} stack-like handler effects"));
        }
        if cursor_ops >= 4 {
            vm_evidence_score += 2;
            vm_reasons.push(format!("{cursor_ops} indexed cursor/stack mutations"));
        }
        if continue_handlers >= 3 {
            vm_evidence_score += 2;
            vm_reasons.push(format!(
                "{continue_handlers} handlers continue dispatch loop"
            ));
        }
        if call_selector && !indexed_selector {
            vm_reasons.push("opcode selector is produced by a call".into());
        }
        let confirmed_vm = vm_evidence_score >= 5;

        self.direct_switch_maps.push(DirectSwitchMapCandidate {
            parent_function_id: current.m.id.clone(),
            start: sw.span.start,
            end: sw.span.end,
            selector,
            numeric_cases,
            opcode_max,
            vm_evidence_score,
            vm_reasons,
            confirmed_vm,
            handlers,
        });
    }

    fn record_handler_table(&mut self, obj: &oxc_ast::ast::ObjectExpression<'_>) {
        let properties = obj.properties.len();
        if properties < 8 {
            return;
        }

        let mut function_values = 0usize;
        let mut async_function_values = 0usize;
        for prop in &obj.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = prop else {
                continue;
            };
            match &prop.value {
                Expression::FunctionExpression(f) => {
                    function_values += 1;
                    if f.r#async {
                        async_function_values += 1;
                    }
                }
                Expression::ArrowFunctionExpression(f) => {
                    function_values += 1;
                    if f.r#async {
                        async_function_values += 1;
                    }
                }
                _ => {}
            }
        }

        if function_values < 8 || function_values * 2 < properties {
            return;
        }

        self.handler_tables.push(HandlerTableCandidate {
            start: obj.span.start,
            end: obj.span.end,
            container_kind: "object".to_string(),
            properties,
            function_values,
            async_function_values,
            preview: self.source_preview(obj.span.start, obj.span.end, 120),
        });
    }

    fn record_array(&mut self, arr: &oxc_ast::ast::ArrayExpression<'_>) {
        let n = arr.elements.len();

        if n >= 4 {
            if arr
                .elements
                .iter()
                .all(|el| matches!(el, ArrayExpressionElement::NumericLiteral(_)))
            {
                if let Some(cur) = self.stack.last_mut() {
                    cur.local_numeric_array_lengths.push(n);
                }
            }

            let mut function_values = 0usize;
            let mut async_function_values = 0usize;
            for el in &arr.elements {
                match el {
                    ArrayExpressionElement::FunctionExpression(f) => {
                        function_values += 1;
                        if f.r#async {
                            async_function_values += 1;
                        }
                    }
                    ArrayExpressionElement::ArrowFunctionExpression(f) => {
                        function_values += 1;
                        if f.r#async {
                            async_function_values += 1;
                        }
                    }
                    _ => {}
                }
            }
            if function_values >= 4 && function_values * 2 >= n {
                if let Some(cur) = self.stack.last_mut() {
                    cur.local_function_table_lengths.push(n);
                }
                self.handler_tables.push(HandlerTableCandidate {
                    start: arr.span.start,
                    end: arr.span.end,
                    container_kind: "array".to_string(),
                    properties: n,
                    function_values,
                    async_function_values,
                    preview: self.source_preview(arr.span.start, arr.span.end, 120),
                });
            }
        }

        if n < 16 {
            return;
        }

        let mut numeric = 0usize;
        let mut byte_values = 0usize;
        let mut values: Vec<Option<u64>> = Vec::with_capacity(n);
        for el in &arr.elements {
            match el {
                ArrayExpressionElement::NumericLiteral(v)
                    if v.value.is_finite() && v.value >= 0.0 =>
                {
                    let iv = v.value as u64;
                    if (iv as f64 - v.value).abs() < f64::EPSILON {
                        numeric += 1;
                        if iv <= 255 {
                            byte_values += 1;
                        }
                        values.push(Some(iv));
                    } else {
                        values.push(None);
                    }
                }
                _ => values.push(None),
            }
        }

        if numeric * 4 < n * 3 {
            return;
        }

        let mut hints = Vec::new();
        if numeric == n && n >= 32 {
            for width in 2usize..=8 {
                if n < width * 8 {
                    continue;
                }
                let mut op = BTreeSet::new();
                let mut op_max = 0u64;
                let mut operand_max = 0u64;
                let mut complete = true;
                for (i, v) in values.iter().enumerate() {
                    let Some(v) = v else {
                        complete = false;
                        break;
                    };
                    if i % width == 0 {
                        op.insert(*v);
                        op_max = op_max.max(*v);
                    } else {
                        operand_max = operand_max.max(*v);
                    }
                }
                if !complete {
                    continue;
                }
                let insts = n / width;
                let mut score = 0i32;
                if n.is_multiple_of(width) {
                    score += 2;
                }
                if op_max <= 63 {
                    score += 4;
                } else if op_max <= 127 {
                    score += 2;
                }
                if operand_max > op_max.saturating_mul(2) {
                    score += 2;
                }
                if op.len() <= 64 {
                    score += 2;
                }
                if op.len() * 2 <= insts {
                    score += 1;
                }
                if score >= 5 {
                    hints.push(WidthHint {
                        width,
                        opcode_unique: op.len(),
                        opcode_max: op_max,
                        operand_max,
                        score,
                    });
                }
            }
            hints.sort_by_key(|h| std::cmp::Reverse(h.score));
        }

        self.arrays.push(ArrayCandidate {
            start: arr.span.start,
            end: arr.span.end,
            elements: n,
            numeric,
            byte_values,
            numeric_ratio: numeric as f64 / n as f64,
            width_hints: hints,
            preview: self.source_preview(arr.span.start, arr.span.end, 120),
        });
    }
}

impl<'a> Visit<'a> for Scanner<'_> {
    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        let name = function.id.as_ref().map(|id| id.name.to_string());
        self.push_function("function", name, function.span.start, function.span.end);
        walk::walk_function(self, function, flags);
        self.analyze_opcode_maps(function);
        self.finish_function();
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.push_function("arrow", None, function.span.start, function.span.end);
        walk::walk_arrow_function_expression(self, function);
        self.finish_function();
    }

    fn visit_object_expression(&mut self, object: &oxc_ast::ast::ObjectExpression<'a>) {
        self.record_handler_table(object);
        walk::walk_object_expression(self, object);
    }

    fn visit_array_expression(&mut self, array: &oxc_ast::ast::ArrayExpression<'a>) {
        self.record_array(array);
        if let Some(current) = self.stack.last_mut() {
            current.m.arrays += 1;
            if array.elements.len() >= 32 {
                current.m.large_arrays += 1;
            }
        }
        walk::walk_array_expression(self, array);
    }

    fn visit_switch_statement(&mut self, switch: &oxc_ast::ast::SwitchStatement<'a>) {
        self.record_direct_switch(switch);
        if let Some(current) = self.stack.last_mut() {
            current.m.switches += 1;
            current.m.switch_cases += switch.cases.len();
            current
                .switch_inputs
                .push(expression_evidence(self.source, &switch.discriminant));
        }
        walk::walk_switch_statement(self, switch);
    }

    fn visit_for_statement(&mut self, statement: &oxc_ast::ast::ForStatement<'a>) {
        if let Some(function_id) = self.stack.last().map(|current| current.m.id.as_str()) {
            let detected = detect_for_state_machines(self.source, function_id, statement);
            self.state_machines.extend(detected.switch_machines);
            self.if_ladder_state_machines
                .extend(detected.if_ladder_machines);
        }
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_for_statement(self, statement);
    }

    fn visit_while_statement(&mut self, statement: &oxc_ast::ast::WhileStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_while_statement(self, statement);
    }

    fn visit_do_while_statement(&mut self, statement: &oxc_ast::ast::DoWhileStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_do_while_statement(self, statement);
    }

    fn visit_for_in_statement(&mut self, statement: &oxc_ast::ast::ForInStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_for_in_statement(self, statement);
    }

    fn visit_for_of_statement(&mut self, statement: &oxc_ast::ast::ForOfStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.loops += 1;
        }
        walk::walk_for_of_statement(self, statement);
    }

    fn visit_conditional_expression(
        &mut self,
        expression: &oxc_ast::ast::ConditionalExpression<'a>,
    ) {
        if let Some(current) = self.stack.last_mut() {
            current.m.conditionals += 1;
        }
        walk::walk_conditional_expression(self, expression);
    }

    fn visit_computed_member_expression(
        &mut self,
        member: &oxc_ast::ast::ComputedMemberExpression<'a>,
    ) {
        let indexed_access = if let Expression::Identifier(object) = &member.object {
            Self::index_shape(&member.expression).map(|shape| IndexedAccess {
                object: object.name.to_string(),
                shape,
                start: member.span.start,
                end: member.span.end,
                preview: self.source_preview(member.span.start, member.span.end, 160),
            })
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            current.m.computed_members += 1;
            if let Some(access) = indexed_access {
                current.indexed_accesses.push(access);
            }
        }
        walk::walk_computed_member_expression(self, member);
    }

    fn visit_variable_declarator(&mut self, declarator: &oxc_ast::ast::VariableDeclarator<'a>) {
        let fetched_access = if let (
            oxc_ast::ast::BindingPattern::BindingIdentifier(id),
            Some(Expression::ComputedMemberExpression(member)),
        ) = (&declarator.id, &declarator.init)
        {
            if let Expression::Identifier(object) = &member.object {
                Self::index_shape(&member.expression).map(|shape| {
                    (
                        id.name.to_string(),
                        IndexedAccess {
                            object: object.name.to_string(),
                            shape,
                            start: member.span.start,
                            end: member.span.end,
                            preview: self.source_preview(member.span.start, member.span.end, 160),
                        },
                    )
                })
            } else {
                None
            }
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            if let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &declarator.id {
                if let Some(init) = &declarator.init {
                    let name = id.name.to_string();
                    current
                        .vars
                        .insert(name.clone(), expression_evidence(self.source, init));
                    if let Some(rhs) = Self::expr_ident(init) {
                        current.aliases.insert(name.clone(), rhs);
                    } else {
                        current.aliases.remove(&name);
                    }
                }
            }
            if let Some((name, access)) = fetched_access {
                current.indexed_value_vars.insert(name, access);
            }
        }
        walk::walk_variable_declarator(self, declarator);
    }

    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        self.record_push_builder(call);
        self.record_literal_string_join(call);
        let is_function_ctor = matches!(
            &call.callee,
            Expression::Identifier(id) if id.name.as_str() == "Function"
        );
        if let Some(current) = self.stack.last_mut() {
            current.m.calls += 1;
            if let Expression::ComputedMemberExpression(member) = &call.callee {
                current.m.computed_calls += 1;
                current
                    .computed_call_indices
                    .push(expression_evidence(self.source, &member.expression));
            }
        }
        if is_function_ctor {
            self.record_function_constructor(
                "Function",
                call.span.start,
                call.span.end,
                &call.arguments,
            );
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_new_expression(&mut self, expression: &oxc_ast::ast::NewExpression<'a>) {
        if matches!(
            &expression.callee,
            Expression::Identifier(id) if id.name.as_str() == "Function"
        ) {
            self.record_function_constructor(
                "new Function",
                expression.span.start,
                expression.span.end,
                &expression.arguments,
            );
        }
        walk::walk_new_expression(self, expression);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        let lhs = if assignment.operator.is_assign() {
            Self::target_ident(&assignment.left)
        } else {
            None
        };
        let rhs = Self::expr_ident(&assignment.right);
        let fetched_access = if let (Some(lhs_name), Expression::ComputedMemberExpression(member)) =
            (lhs.as_ref(), &assignment.right)
        {
            if let Expression::Identifier(object) = &member.object {
                Self::index_shape(&member.expression).map(|shape| {
                    (
                        lhs_name.clone(),
                        IndexedAccess {
                            object: object.name.to_string(),
                            shape,
                            start: member.span.start,
                            end: member.span.end,
                            preview: self.source_preview(member.span.start, member.span.end, 160),
                        },
                    )
                })
            } else {
                None
            }
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            current.m.assignments += 1;
            if let Some(lhs) = lhs {
                if let Some(rhs) = rhs {
                    current.aliases.insert(lhs, rhs);
                } else {
                    current.aliases.remove(&lhs);
                }
            }
            if let Some((name, access)) = fetched_access {
                current.indexed_value_vars.insert(name, access);
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_binary_expression(&mut self, binary: &oxc_ast::ast::BinaryExpression<'a>) {
        let bit_mask = if binary.operator.as_str() == "&" {
            if let (Some(name), Some(mask)) = (
                Self::origin_ident(&binary.left),
                Self::origin_u64(&binary.right),
            ) {
                Some((name, mask))
            } else if let (Some(mask), Some(name)) = (
                Self::origin_u64(&binary.left),
                Self::origin_ident(&binary.right),
            ) {
                Some((name, mask))
            } else {
                None
            }
        } else {
            None
        };

        if let Some(current) = self.stack.last_mut() {
            current.m.binary_exprs += 1;
            if let Some((name, mask)) = bit_mask {
                if mask.is_power_of_two() && mask <= (1u64 << 32) {
                    current
                        .bit_masks
                        .entry(name.clone())
                        .or_default()
                        .insert(mask);
                    let resolved = Self::resolve_alias(&name, &current.aliases);
                    if resolved != name {
                        current.bit_masks.entry(resolved).or_default().insert(mask);
                    }
                }
            }
        }
        walk::walk_binary_expression(self, binary);
    }

    fn visit_unary_expression(&mut self, expression: &oxc_ast::ast::UnaryExpression<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.unary_exprs += 1;
        }
        walk::walk_unary_expression(self, expression);
    }

    fn visit_sequence_expression(&mut self, expression: &oxc_ast::ast::SequenceExpression<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.sequence_exprs += 1;
        }
        walk::walk_sequence_expression(self, expression);
    }

    fn visit_numeric_literal(&mut self, _literal: &oxc_ast::ast::NumericLiteral<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.numeric_literals += 1;
        }
    }

    fn visit_string_literal(&mut self, _literal: &oxc_ast::ast::StringLiteral<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.string_literals += 1;
        }
    }

    fn visit_try_statement(&mut self, statement: &oxc_ast::ast::TryStatement<'a>) {
        if let Some(current) = self.stack.last_mut() {
            current.m.tries += 1;
        }
        walk::walk_try_statement(self, statement);
    }

    fn visit_program(&mut self, program: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, program);
    }
}

struct ScanCore {
    diagnostics: usize,
    panicked: bool,
    arrays: Vec<ArrayCandidate>,
    push_builders: Vec<PushBuilderCandidate>,
    decoder_candidates: Vec<DecoderCandidate>,
    state_machines: Vec<StateMachineCandidate>,
    if_ladder_state_machines: Vec<IfLadderStateMachineCandidate>,
    opcode_maps: Vec<OpcodeMapCandidate>,
    direct_switch_maps: Vec<DirectSwitchMapCandidate>,
    handler_tables: Vec<HandlerTableCandidate>,
    handler_function_tables: Vec<table_vm::DetailedHandlerTableCandidate>,
    byte_transducers: Vec<table_vm::ByteTransducerCandidate>,
    table_vms: Vec<table_vm::TableVmCandidate>,
    functions: Vec<FunctionMetrics>,
    embedded_code: Vec<EmbeddedCodeCandidate>,
}

fn scan_source_core(source: &str) -> ScanCore {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::cjs());

    let mut scanner = Scanner::new(source);
    scanner.visit_program(&parsed.program);
    let mut table_analysis = table_vm::analyze(source, &parsed.program);

    // A direct-switch interpreter may itself execute helper/function tables in
    // individual opcode handlers. Those are nested semantics, not a second
    // dispatcher architecture. Suppress table-dispatch labels for any function
    // lexically contained by a confirmed switch interpreter.
    let direct_switch_owner_spans: Vec<(u32, u32)> = scanner
        .direct_switch_maps
        .iter()
        .filter(|map| map.confirmed_vm)
        .filter_map(|map| {
            scanner
                .functions
                .iter()
                .find(|function| function.id == map.parent_function_id)
                .map(|function| (function.start, function.end))
        })
        .collect();
    let function_spans: HashMap<&str, (u32, u32)> = scanner
        .functions
        .iter()
        .map(|function| (function.id.as_str(), (function.start, function.end)))
        .collect();
    table_analysis.table_vms.retain(|vm| {
        let Some((start, end)) = function_spans.get(vm.dispatcher_function_id.as_str()) else {
            return true;
        };
        !direct_switch_owner_spans
            .iter()
            .any(|(owner_start, owner_end)| owner_start <= start && end <= owner_end)
    });

    scanner.decoder_candidates.sort_by(|a, b| {
        (
            a.start,
            &a.object,
            &a.base,
            &a.ip,
            a.width,
            std::cmp::Reverse(a.operand_offsets.len()),
        )
            .cmp(&(
                b.start,
                &b.object,
                &b.base,
                &b.ip,
                b.width,
                std::cmp::Reverse(b.operand_offsets.len()),
            ))
    });
    scanner.decoder_candidates.dedup_by(|a, b| {
        a.start == b.start
            && a.object == b.object
            && a.base == b.base
            && a.ip == b.ip
            && a.width == b.width
            && a.builder_var == b.builder_var
    });

    // Complete selector width only after every descendant decoder has had a
    // chance to link to its bytecode builder.
    Scanner::complete_selector_masks(&mut scanner.decoder_candidates, &scanner.push_builders);

    // A decoder is propagated upward so a builder declared in an ancestor can
    // be linked. That must not create a second semantic map against an
    // unrelated ancestor state machine. Keep the smallest lexical parent that
    // produced a map for each decoder/selector identity.
    let function_bytes: HashMap<String, usize> = scanner
        .functions
        .iter()
        .map(|f| (f.id.clone(), f.bytes))
        .collect();
    scanner.opcode_maps.sort_by(|a, b| {
        (
            &a.decoder_function_id,
            &a.decoder_selector_var,
            function_bytes
                .get(&a.parent_function_id)
                .copied()
                .unwrap_or(usize::MAX),
            &a.parent_function_id,
        )
            .cmp(&(
                &b.decoder_function_id,
                &b.decoder_selector_var,
                function_bytes
                    .get(&b.parent_function_id)
                    .copied()
                    .unwrap_or(usize::MAX),
                &b.parent_function_id,
            ))
    });
    scanner.opcode_maps.dedup_by(|a, b| {
        a.decoder_function_id == b.decoder_function_id
            && a.decoder_selector_var == b.decoder_selector_var
    });

    // Builder linkage and semantic-dispatch ownership are deliberately
    // independent: attach live bytecodes to the retained lexical map here.
    for map in &mut scanner.opcode_maps {
        let observed = scanner
            .decoder_candidates
            .iter()
            .filter(|decoder| {
                decoder.function_id == map.decoder_function_id
                    && decoder.selector_var.as_deref() == Some(map.decoder_selector_var.as_str())
                    && decoder.builder_start.is_some()
            })
            .max_by_key(|decoder| decoder.selector_masks.len())
            .map(|decoder| Scanner::observed_opcodes(decoder, &scanner.push_builders))
            .unwrap_or_default();
        let observed_set: BTreeSet<u64> = observed.iter().copied().collect();
        map.observed_opcodes = observed;
        for handler in &mut map.handlers {
            handler.observed = observed_set.contains(&handler.opcode);
        }
    }

    // The legacy table heuristic is intentionally broad enough to surface
    // candidates before table identity is known. Once table_vm has resolved
    // exact dispatcher -> table/registry links, make table-based confirmation
    // depend on that link instead of on an unrelated large table elsewhere in
    // the file. Large-switch confirmation remains independent.
    let table_dispatchers: BTreeSet<&str> = table_analysis
        .table_vms
        .iter()
        .map(|vm| vm.dispatcher_function_id.as_str())
        .collect();
    for function in &mut scanner.functions {
        let switch_confirmed = function
            .dispatch_reasons
            .iter()
            .any(|reason| reason.starts_with("large switch discriminant"));
        let table_confirmed = table_dispatchers.contains(function.id.as_str());
        function.confirmed_dispatch = switch_confirmed || table_confirmed;
        function.dispatch_reasons.retain(|reason| {
            reason.starts_with("large switch discriminant")
                || (!reason.contains("handler table")
                    && !reason.contains("function table")
                    && !reason.contains("same-sized"))
        });
        if table_confirmed {
            function.dispatch_reasons.push(
                "looped computed call is linked to its concrete handler table/registry".into(),
            );
        }
    }

    scanner
        .functions
        .sort_by_key(|f| std::cmp::Reverse(f.score));
    scanner
        .arrays
        .sort_by_key(|a| std::cmp::Reverse(a.elements));
    scanner
        .handler_tables
        .sort_by_key(|h| std::cmp::Reverse(h.function_values));

    ScanCore {
        diagnostics: parsed.diagnostics,
        panicked: parsed.panicked,
        arrays: scanner.arrays,
        push_builders: scanner.push_builders,
        decoder_candidates: scanner.decoder_candidates,
        state_machines: scanner.state_machines,
        if_ladder_state_machines: scanner.if_ladder_state_machines,
        opcode_maps: scanner.opcode_maps,
        direct_switch_maps: scanner.direct_switch_maps,
        handler_tables: scanner.handler_tables,
        handler_function_tables: table_analysis.handler_function_tables,
        byte_transducers: table_analysis.byte_transducers,
        table_vms: table_analysis.table_vms,
        functions: scanner.functions,
        embedded_code: scanner.embedded_code,
    }
}

fn embedded_hash(bytes: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for byte in bytes {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn scan_embedded_candidate(
    candidate: EmbeddedCodeCandidate,
    depth: usize,
    dump_dir: Option<&std::path::Path>,
) -> EmbeddedScanReport {
    let wrapper = format!(
        "function __embedded({}) {{\n{}\n}}\n",
        candidate.params.join(","),
        candidate.body
    );

    let dump_path = dump_dir.and_then(|dir| {
        if fs::create_dir_all(dir).is_err() {
            return None;
        }
        let digest = embedded_hash(wrapper.as_bytes());
        let path = dir.join(format!("embedded-{digest:016x}.js"));
        if !path.exists() && fs::write(&path, &wrapper).is_err() {
            return None;
        }
        Some(path.display().to_string())
    });

    let core = scan_source_core(&wrapper);
    let embedded = if depth < 3 {
        core.embedded_code
            .into_iter()
            .map(|c| scan_embedded_candidate(c, depth + 1, dump_dir))
            .collect()
    } else {
        Vec::new()
    };

    EmbeddedScanReport {
        outer_start: candidate.outer_start,
        outer_end: candidate.outer_end,
        kind: candidate.kind,
        body_bytes: candidate.body.len(),
        dump_path,
        diagnostics: core.diagnostics,
        panicked: core.panicked,
        arrays: core.arrays,
        push_builders: core.push_builders,
        decoder_candidates: core.decoder_candidates,
        state_machines: core.state_machines,
        if_ladder_state_machines: core.if_ladder_state_machines,
        opcode_maps: core.opcode_maps,
        direct_switch_maps: core.direct_switch_maps,
        handler_tables: core.handler_tables,
        handler_function_tables: core.handler_function_tables,
        byte_transducers: core.byte_transducers,
        table_vms: core.table_vms,
        functions: core.functions,
        embedded,
    }
}

fn scan_file(path: &PathBuf, dump_dir: Option<&std::path::Path>) -> Result<ScanReport> {
    let source = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let core = scan_source_core(&source);
    let embedded = core
        .embedded_code
        .into_iter()
        .map(|c| scan_embedded_candidate(c, 1, dump_dir))
        .collect();

    Ok(ScanReport {
        file: path.display().to_string(),
        bytes: source.len(),
        diagnostics: core.diagnostics,
        panicked: core.panicked,
        arrays: core.arrays,
        push_builders: core.push_builders,
        decoder_candidates: core.decoder_candidates,
        state_machines: core.state_machines,
        if_ladder_state_machines: core.if_ladder_state_machines,
        opcode_maps: core.opcode_maps,
        direct_switch_maps: core.direct_switch_maps,
        handler_tables: core.handler_tables,
        handler_function_tables: core.handler_function_tables,
        byte_transducers: core.byte_transducers,
        table_vms: core.table_vms,
        functions: core.functions,
        embedded,
    })
}

fn print_embedded(report: &EmbeddedScanReport, min_score: u32, depth: usize) {
    let indent = "  ".repeat(depth);
    println!(
        "{indent}embedded {} @{:x}-{:x}: {} bytes, {} diagnostics, {} arrays, {} push builders, {} decoders, {} state machines, {} opcode maps, {} handler tables{}",
        report.kind,
        report.outer_start,
        report.outer_end,
        report.body_bytes,
        report.diagnostics,
        report.arrays.len(),
        report.push_builders.len(),
        report.decoder_candidates.len(),
        report.state_machines.len(),
        report.opcode_maps.len(),
        report.handler_tables.len(),
        report
            .dump_path
            .as_ref()
            .map(|p| format!(" -> {p}"))
            .unwrap_or_default()
    );

    for d in report.decoder_candidates.iter().take(12) {
        println!(
            "{indent}  decoder {}: object={} builder={} width={} ip={} base={} offsets={:?} {}",
            d.function_id,
            d.object,
            d.builder_var.as_deref().unwrap_or("?"),
            d.width,
            d.ip,
            d.base.as_deref().unwrap_or("<inline>"),
            d.operand_offsets,
            d.preview
        );
    }
    for sm in report.state_machines.iter().take(12) {
        println!(
            "{indent}  state-machine {}: state={} init={} mask={} shift={:?} selector={} cases={}",
            sm.function_id,
            sm.state_var,
            sm.init_state,
            sm.mask,
            sm.shift,
            sm.selector_var.as_deref().unwrap_or("?"),
            sm.switch_cases
        );
    }
    for h in report.handler_tables.iter().take(8) {
        println!(
            "{indent}  handler table ({}) @{:x}-{:x}: entries={} functions={} async={}",
            h.container_kind,
            h.start,
            h.end,
            h.properties,
            h.function_values,
            h.async_function_values
        );
    }
    for f in report
        .functions
        .iter()
        .filter(|f| f.score >= min_score)
        .take(20)
    {
        println!(
            "{indent}  {} score={:2} {} {} @{:x}-{:x} bytes={} switch_cases={} loops={} computed={} computed_calls={} :: {}{}",
            if f.confirmed_dispatch { "[CONFIRMED]" } else { "[candidate]" },
            f.score,
            f.kind,
            f.name.as_deref().unwrap_or("<anon>"),
            f.start,
            f.end,
            f.bytes,
            f.switch_cases,
            f.loops,
            f.computed_members,
            f.computed_calls,
            f.reasons.join("; "),
            if f.dispatch_reasons.is_empty() {
                String::new()
            } else {
                format!(" | dispatch: {}", f.dispatch_reasons.join("; "))
            }
        );
    }
    for child in &report.embedded {
        print_embedded(child, min_score, depth + 1);
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    for path in &args.files {
        let report = scan_file(path, args.dump_embedded.as_deref())?;
        if args.json {
            println!("{}", serde_json::to_string(&report)?);
            continue;
        }

        println!(
            "{}: {} bytes, {} parse diagnostics, {} array candidates, {} push-builder candidates, {} decoder candidates, {} state machines, {} opcode maps, {} handler-table candidates",
            report.file,
            report.bytes,
            report.diagnostics,
            report.arrays.len(),
            report.push_builders.len(),
            report.decoder_candidates.len(),
            report.state_machines.len(),
            report.opcode_maps.len(),
            report.handler_tables.len()
        );

        for a in report.arrays.iter().take(8) {
            let hints = a
                .width_hints
                .iter()
                .take(3)
                .map(|h| format!("w{}:{}", h.width, h.score))
                .collect::<Vec<_>>()
                .join(",");
            println!(
                "  array @{:x}-{:x}: n={} numeric={:.0}% bytes={} hints=[{}] {}",
                a.start,
                a.end,
                a.elements,
                a.numeric_ratio * 100.0,
                a.byte_values,
                hints,
                a.preview
            );
        }

        for b in report.push_builders.iter().take(8) {
            println!(
                "  push builder @{:x}-{:x}: recv={} args={} numeric={} bytes={} calls={} other={} widths={:?} {}",
                b.start,
                b.end,
                b.receiver,
                b.arguments,
                b.numeric_literals,
                b.byte_literals,
                b.call_arguments,
                b.other_arguments,
                b.width_hints
                    .iter()
                    .take(4)
                    .map(|h| (h.width, h.score))
                    .collect::<Vec<_>>(),
                b.preview
            );
        }

        for d in report.decoder_candidates.iter().take(16) {
            println!(
                "  decoder {}: object={} builder={} width={} ip={} base={} offsets={:?} {}",
                d.function_id,
                d.object,
                d.builder_var.as_deref().unwrap_or("?"),
                d.width,
                d.ip,
                d.base.as_deref().unwrap_or("<inline>"),
                d.operand_offsets,
                d.preview
            );
        }

        for sm in report.state_machines.iter().take(20) {
            println!(
                "  state-machine {}: state={} init={} mask={} shift={:?} selector={} cases={} @{:x}-{:x}",
                sm.function_id,
                sm.state_var,
                sm.init_state,
                sm.mask,
                sm.shift,
                sm.selector_var.as_deref().unwrap_or("?"),
                sm.switch_cases,
                sm.start,
                sm.end
            );
        }

        for h in report.handler_tables.iter().take(8) {
            println!(
                "  handler table ({}) @{:x}-{:x}: entries={} functions={} async={} {}",
                h.container_kind,
                h.start,
                h.end,
                h.properties,
                h.function_values,
                h.async_function_values,
                h.preview
            );
        }

        println!("  VM-shaped functions:");
        for f in report
            .functions
            .iter()
            .filter(|f| f.score >= args.min_score)
            .take(20)
        {
            println!(
                "    {} score={:2} {} {} @{:x}-{:x} bytes={} switch_cases={} loops={} ternaries={} computed={} computed_calls={} arrays={} :: {}{}",
                if f.confirmed_dispatch { "[CONFIRMED]" } else { "[candidate]" },
                f.score,
                f.kind,
                f.name.as_deref().unwrap_or("<anon>"),
                f.start,
                f.end,
                f.bytes,
                f.switch_cases,
                f.loops,
                f.conditionals,
                f.computed_members,
                f.computed_calls,
                f.large_arrays,
                f.reasons.join("; "),
                if f.dispatch_reasons.is_empty() {
                    String::new()
                } else {
                    format!(" | dispatch: {}", f.dispatch_reasons.join("; "))
                }
            );
        }

        for embedded in &report.embedded {
            print_embedded(embedded, args.min_score, 1);
        }
    }
    Ok(())
}
