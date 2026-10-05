use crate::decoder::{
    annotate_bitfield_selectors, derive_candidates, link_candidates, BuilderSite, DecoderCandidate,
    IndexedAccess,
};
use oxc_ast::{ast::Expression, AstKind};
use oxc_ast_visit::Visit;
use serde::Serialize;
use std::collections::{BTreeSet, HashMap, HashSet};

#[derive(Debug, Clone, Default, Serialize)]
pub struct FunctionMetrics {
    pub id: String,
    pub kind: String,
    pub name: Option<String>,
    pub start: u32,
    pub end: u32,
    pub bytes: usize,
    pub switches: usize,
    pub switch_cases: usize,
    pub loops: usize,
    pub conditionals: usize,
    pub computed_members: usize,
    pub computed_calls: usize,
    pub calls: usize,
    pub assignments: usize,
    pub binary_exprs: usize,
    pub unary_exprs: usize,
    pub sequence_exprs: usize,
    pub arrays: usize,
    pub large_arrays: usize,
    pub numeric_literals: usize,
    pub string_literals: usize,
    pub tries: usize,
    pub confirmed_dispatch: bool,
    pub dispatch_reasons: Vec<String>,
    pub indexed_read_chain: Vec<String>,
    pub score: u32,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub struct ExprEvidence {
    pub computed_members: usize,
    pub calls: usize,
    pub identifiers: BTreeSet<String>,
    pub computed_previews: BTreeSet<String>,
}

struct EvidenceVisitor<'s> {
    source: &'s str,
    evidence: ExprEvidence,
}

impl<'a> Visit<'a> for EvidenceVisitor<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::ComputedMemberExpression(member) => {
                self.evidence.computed_members += 1;
                let start = member.span.start as usize;
                let end = (member.span.end as usize).min(self.source.len());
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

pub fn expression_evidence(source: &str, expr: &Expression<'_>) -> ExprEvidence {
    let mut visitor = EvidenceVisitor {
        source,
        evidence: ExprEvidence::default(),
    };
    visitor.visit_expression(expr);
    visitor.evidence
}

fn evidence_reaches_computed_inner(
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
            if evidence_reaches_computed_inner(next, vars, seen) {
                return true;
            }
        }
    }
    false
}

pub fn evidence_reaches_computed(
    evidence: &ExprEvidence,
    vars: &HashMap<String, ExprEvidence>,
) -> bool {
    evidence_reaches_computed_inner(evidence, vars, &mut HashSet::new())
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
            collect_indexed_reads(next, vars, seen, out);
        }
    }
}

#[derive(Default)]
pub struct FunctionState {
    pub m: FunctionMetrics,
    pub vars: HashMap<String, ExprEvidence>,
    pub switch_inputs: Vec<ExprEvidence>,
    pub computed_call_indices: Vec<ExprEvidence>,
    pub local_function_table_lengths: Vec<usize>,
    pub local_numeric_array_lengths: Vec<usize>,
    pub aliases: HashMap<String, String>,
    pub push_builder_vars: BTreeSet<String>,
    pub push_builder_sites: HashMap<String, BuilderSite>,
    pub indexed_accesses: Vec<IndexedAccess>,
    pub child_indexed_accesses: Vec<IndexedAccess>,
    pub indexed_value_vars: HashMap<String, IndexedAccess>,
    pub bit_masks: HashMap<String, BTreeSet<u64>>,
    pub decoder_candidates: Vec<DecoderCandidate>,
}

impl FunctionState {
    pub fn new(kind: &str, name: Option<String>, start: u32, end: u32) -> Self {
        Self {
            m: FunctionMetrics {
                id: format!("fn@{start:x}-{end:x}"),
                kind: kind.to_string(),
                name,
                start,
                end,
                bytes: end.saturating_sub(start) as usize,
                ..FunctionMetrics::default()
            },
            ..Self::default()
        }
    }

    pub fn finalize_decoders(&mut self) {
        let mut decoder_accesses = self.indexed_accesses.clone();
        decoder_accesses.extend(self.child_indexed_accesses.iter().cloned());
        let mut local_decoders = derive_candidates(&self.m.id, &decoder_accesses);
        annotate_bitfield_selectors(
            &mut local_decoders,
            &self.indexed_value_vars,
            &self.bit_masks,
            &self.aliases,
        );
        self.decoder_candidates.extend(local_decoders);
        link_candidates(
            &mut self.decoder_candidates,
            &self.aliases,
            &self.push_builder_vars,
            &self.push_builder_sites,
        );
    }

    pub fn finalize_metrics(
        &mut self,
        switch_from_indexed_state: bool,
        large_handler_table_present: bool,
    ) {
        let mut dispatch_reasons = Vec::new();
        if switch_from_indexed_state {
            dispatch_reasons
                .push("large switch discriminant traces to computed/indexed state".to_string());
        }

        let index_reaches_computed = self
            .computed_call_indices
            .iter()
            .any(|evidence| evidence_reaches_computed(evidence, &self.vars));
        let local_table_schedule_pair = self.local_function_table_lengths.iter().any(|len| {
            self.local_numeric_array_lengths
                .iter()
                .any(|numeric| numeric == len)
        });
        let table_dispatch = self.m.loops > 0
            && !self.computed_call_indices.is_empty()
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

        self.m.confirmed_dispatch = switch_from_indexed_state || table_dispatch;
        self.m.dispatch_reasons = dispatch_reasons;
        let mut indexed_reads = BTreeSet::new();
        if switch_from_indexed_state {
            for evidence in &self.switch_inputs {
                collect_indexed_reads(
                    evidence,
                    &self.vars,
                    &mut HashSet::new(),
                    &mut indexed_reads,
                );
            }
        }
        self.m.indexed_read_chain = indexed_reads.into_iter().collect();

        let mut score = 0u32;
        let mut reasons = Vec::new();
        if self.m.switch_cases >= 16 {
            score += 8;
            reasons.push(format!("{} switch cases", self.m.switch_cases));
        } else if self.m.switches > 0 {
            score += 3;
            reasons.push(format!("{} switch(es)", self.m.switches));
        }
        if self.m.loops > 0 {
            score += 3.min(self.m.loops as u32 + 1);
            reasons.push(format!("{} loop(s)", self.m.loops));
        }
        if self.m.conditionals >= 30 {
            score += 5;
            reasons.push(format!("{} ternaries", self.m.conditionals));
        } else if self.m.conditionals >= 10 {
            score += 2;
            reasons.push(format!("{} ternaries", self.m.conditionals));
        }
        if self.m.computed_members >= 25 {
            score += 5;
            reasons.push(format!(
                "{} computed member reads/writes",
                self.m.computed_members
            ));
        } else if self.m.computed_members >= 8 {
            score += 2;
            reasons.push(format!(
                "{} computed member reads/writes",
                self.m.computed_members
            ));
        }
        if self.m.loops > 0 && self.m.computed_calls > 0 && self.m.computed_members >= 2 {
            score += 6;
            reasons.push(format!(
                "{} computed call(s) inside a loop-shaped function",
                self.m.computed_calls
            ));
        }
        if self.m.large_arrays > 0 {
            score += 6;
            reasons.push(format!("{} large literal array(s)", self.m.large_arrays));
        }
        if self.m.sequence_exprs >= 12 {
            score += 2;
            reasons.push(format!("{} sequence expressions", self.m.sequence_exprs));
        }
        if self.m.binary_exprs >= 80 {
            score += 2;
            reasons.push(format!("{} binary expressions", self.m.binary_exprs));
        }
        if self.m.bytes >= 20_000 {
            score += 4;
            reasons.push(format!("{} byte function body", self.m.bytes));
        } else if self.m.bytes >= 5_000 {
            score += 2;
            reasons.push(format!("{} byte function body", self.m.bytes));
        }
        self.m.score = score;
        self.m.reasons = reasons;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn follows_expression_evidence_through_variables() {
        let mut vars = HashMap::new();
        vars.insert(
            "alias".to_string(),
            ExprEvidence {
                identifiers: BTreeSet::from(["indexed".to_string()]),
                ..ExprEvidence::default()
            },
        );
        vars.insert(
            "indexed".to_string(),
            ExprEvidence {
                computed_members: 1,
                ..ExprEvidence::default()
            },
        );
        let evidence = ExprEvidence {
            identifiers: BTreeSet::from(["alias".to_string()]),
            ..ExprEvidence::default()
        };
        assert!(evidence_reaches_computed(&evidence, &vars));
    }

    #[test]
    fn scoring_and_dispatch_policy_are_owned_by_function_state() {
        let mut function = FunctionState::new("function", Some("vm".to_string()), 10, 20_010);
        function.m.switches = 1;
        function.m.switch_cases = 16;
        function.m.loops = 1;
        function.m.computed_members = 25;
        function.m.computed_calls = 1;
        function.m.large_arrays = 1;
        function.switch_inputs.push(ExprEvidence {
            computed_members: 1,
            computed_previews: BTreeSet::from(["code[ip]".to_string()]),
            ..ExprEvidence::default()
        });

        function.finalize_metrics(true, false);

        assert!(function.m.confirmed_dispatch);
        assert!(function.m.score >= 20);
        assert_eq!(function.m.indexed_read_chain, vec!["code[ip]"]);
        assert!(function
            .m
            .dispatch_reasons
            .iter()
            .any(|reason| reason.contains("indexed state")));
    }
}
