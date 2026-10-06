use crate::{
    ast_utils::{exact_u64, expr_ident, numeric_u64, target_ident},
    source_text::preview,
};
use oxc_ast::{
    ast::{Argument, Expression, ForStatement, Function, FunctionBody, Statement, SwitchStatement},
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, Span};
use oxc_syntax::scope::ScopeFlags;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Debug, Clone)]
pub struct DecoderControlInfo {
    pub function_id: String,
    pub selector_var: String,
    pub selector_masks: Vec<u64>,
    pub observed_opcodes: Vec<u64>,
}

#[derive(Debug, Clone)]
pub struct StateMachineInfo {
    pub start: u32,
    pub end: u32,
    pub state_var: String,
    pub init_state: u64,
    pub mask: u64,
    pub shift: Option<u64>,
    pub selector_var: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct StateMachineCandidate {
    pub function_id: String,
    pub start: u32,
    pub end: u32,
    pub state_var: String,
    pub init_state: u64,
    pub mask: u64,
    pub shift: Option<u64>,
    pub selector_var: Option<String>,
    pub switch_cases: usize,
    pub preview: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct IfLadderStateMachineCandidate {
    pub function_id: String,
    pub start: u32,
    pub end: u32,
    pub state_var: String,
    pub init_state: u64,
    pub exit_state: u64,
    pub compared_states: Vec<u64>,
    pub state_assignments: usize,
    pub constant_state_assignments: usize,
    pub dynamic_state_assignments: usize,
    pub preview: String,
}

#[derive(Debug, Default)]
pub struct DetectedStateMachines {
    pub switch_machines: Vec<StateMachineCandidate>,
    pub if_ladder_machines: Vec<IfLadderStateMachineCandidate>,
}

fn for_state_init(for_stmt: &ForStatement<'_>) -> Option<(String, u64)> {
    let init = for_stmt.init.as_ref()?;
    let oxc_ast::ast::ForStatementInit::VariableDeclaration(decl) = init else {
        return None;
    };
    for declarator in &decl.declarations {
        let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &declarator.id else {
            continue;
        };
        let value = declarator.init.as_ref().and_then(numeric_u64)?;
        return Some((id.name.to_string(), value));
    }
    None
}

fn shifted_state(expr: &Expression<'_>, state: &str) -> Option<u64> {
    let binary = match expr {
        Expression::ParenthesizedExpression(paren) => {
            return shifted_state(&paren.expression, state);
        }
        Expression::BinaryExpression(binary) => binary,
        _ => return None,
    };
    if binary.operator.as_str() != ">>" || expr_ident(&binary.left) != Some(state) {
        return None;
    }
    numeric_u64(&binary.right)
}

fn selector_shape(expr: &Expression<'_>, state: &str) -> Option<(u64, u64)> {
    let Expression::BinaryExpression(binary) = expr else {
        return None;
    };
    if binary.operator.as_str() != "&" {
        return None;
    }
    if let Some(mask) = numeric_u64(&binary.left) {
        if let Some(shift) = shifted_state(&binary.right, state) {
            return Some((mask, shift));
        }
    }
    if let Some(mask) = numeric_u64(&binary.right) {
        if let Some(shift) = shifted_state(&binary.left, state) {
            return Some((mask, shift));
        }
    }
    None
}

fn bitand_state(expr: &Expression<'_>, state: &str) -> Option<u64> {
    let Expression::BinaryExpression(binary) = expr else {
        return None;
    };
    if binary.operator.as_str() != "&" {
        return None;
    }
    if expr_ident(&binary.left) == Some(state) {
        return numeric_u64(&binary.right);
    }
    if expr_ident(&binary.right) == Some(state) {
        return numeric_u64(&binary.left);
    }
    None
}

fn binary_state_comparison_literal(
    binary: &oxc_ast::ast::BinaryExpression<'_>,
    state_var: &str,
) -> Option<u64> {
    if !matches!(binary.operator.as_str(), "==" | "===") {
        return None;
    }
    if expr_ident(&binary.left) == Some(state_var) {
        return numeric_u64(&binary.right);
    }
    if expr_ident(&binary.right) == Some(state_var) {
        return numeric_u64(&binary.left);
    }
    None
}

fn state_exit_literal(expr: &Expression<'_>, state_var: &str) -> Option<u64> {
    let Expression::BinaryExpression(binary) = expr else {
        return None;
    };
    if !matches!(binary.operator.as_str(), "!=" | "!==") {
        return None;
    }
    if expr_ident(&binary.left) == Some(state_var) {
        return numeric_u64(&binary.right);
    }
    if expr_ident(&binary.right) == Some(state_var) {
        return numeric_u64(&binary.left);
    }
    None
}

#[derive(Default)]
struct IfLadderEvidence {
    compared_states: BTreeSet<u64>,
    state_assignments: usize,
    constant_state_assignments: usize,
    dynamic_state_assignments: usize,
}

struct IfLadderEvidenceVisitor<'s> {
    state_var: &'s str,
    evidence: IfLadderEvidence,
}

impl<'a> Visit<'a> for IfLadderEvidenceVisitor<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::BinaryExpression(binary) => {
                if let Some(state) = binary_state_comparison_literal(binary, self.state_var) {
                    self.evidence.compared_states.insert(state);
                }
            }
            AstKind::AssignmentExpression(assign)
                if assign.operator.is_assign()
                    && target_ident(&assign.left) == Some(self.state_var) =>
            {
                self.evidence.state_assignments += 1;
                if numeric_u64(&assign.right).is_some() {
                    self.evidence.constant_state_assignments += 1;
                } else {
                    self.evidence.dynamic_state_assignments += 1;
                }
            }
            _ => {}
        }
    }
    fn visit_function(&mut self, _it: &Function<'a>, _flags: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
}

pub fn detect_for_state_machines(
    source: &str,
    function_id: &str,
    for_stmt: &ForStatement<'_>,
) -> DetectedStateMachines {
    let mut detected = DetectedStateMachines::default();
    let Some((state_var, init_state)) = for_state_init(for_stmt) else {
        return detected;
    };
    if for_stmt.update.is_some() {
        return detected;
    }
    if let Some(test) = for_stmt.test.as_ref() {
        let test_preview = preview(source, test.span().start, test.span().end, 180);
        if test_preview.contains(&state_var)
            && (test_preview.contains("void") || test_preview.contains("undefined"))
        {
            if let Statement::BlockStatement(body) = &for_stmt.body {
                let mut selectors = Vec::new();
                let mut switches = Vec::new();
                for stmt in &body.body {
                    match stmt {
                        Statement::VariableDeclaration(decl) => {
                            for declarator in &decl.declarations {
                                let oxc_ast::ast::BindingPattern::BindingIdentifier(id) =
                                    &declarator.id
                                else {
                                    continue;
                                };
                                let Some(init) = declarator.init.as_ref() else {
                                    continue;
                                };
                                if let Some((mask, shift)) = selector_shape(init, &state_var) {
                                    selectors.push((id.name.to_string(), mask, shift));
                                }
                            }
                        }
                        Statement::SwitchStatement(switch) => {
                            if let Some(mask) = bitand_state(&switch.discriminant, &state_var) {
                                switches.push((mask, switch.cases.len()));
                            }
                        }
                        _ => {}
                    }
                }
                for (mask, switch_cases) in switches {
                    let selector = selectors
                        .iter()
                        .find(|(_, selector_mask, _)| *selector_mask == mask);
                    detected.switch_machines.push(StateMachineCandidate {
                        function_id: function_id.to_string(),
                        start: for_stmt.span.start,
                        end: for_stmt.span.end,
                        state_var: state_var.clone(),
                        init_state,
                        mask,
                        shift: selector.map(|(_, _, shift)| *shift),
                        selector_var: selector.map(|(name, _, _)| name.clone()),
                        switch_cases,
                        preview: preview(source, for_stmt.span.start, for_stmt.span.end, 180),
                    });
                }
            }
        }
        if let Some(exit_state) = state_exit_literal(test, &state_var) {
            let mut visitor = IfLadderEvidenceVisitor {
                state_var: &state_var,
                evidence: IfLadderEvidence::default(),
            };
            visitor.visit_statement(&for_stmt.body);
            let evidence = visitor.evidence;
            if evidence.compared_states.len() >= 4 && evidence.state_assignments >= 4 {
                detected
                    .if_ladder_machines
                    .push(IfLadderStateMachineCandidate {
                        function_id: function_id.to_string(),
                        start: for_stmt.span.start,
                        end: for_stmt.span.end,
                        state_var,
                        init_state,
                        exit_state,
                        compared_states: evidence.compared_states.into_iter().collect(),
                        state_assignments: evidence.state_assignments,
                        constant_state_assignments: evidence.constant_state_assignments,
                        dynamic_state_assignments: evidence.dynamic_state_assignments,
                        preview: preview(source, for_stmt.span.start, for_stmt.span.end, 180),
                    });
            }
        }
    }
    detected
}

#[derive(Debug, Clone, Serialize)]
pub struct OpcodeHandler {
    pub opcode: u64,
    pub observed: bool,
    pub path: Vec<u64>,
    pub terminal: String,
    pub semantic: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct OpcodeMapCandidate {
    pub parent_function_id: String,
    pub decoder_function_id: String,
    pub decoder_selector_var: String,
    pub state_machine_start: u32,
    pub state_machine_end: u32,
    pub state_var: String,
    pub selector_bindings: BTreeMap<String, u64>,
    pub opcode_max: u64,
    pub observed_opcodes: Vec<u64>,
    pub handlers: Vec<OpcodeHandler>,
}

fn slice(source: &str, span: Span) -> String {
    let start = span.start as usize;
    let end = (span.end as usize).min(source.len());
    source
        .get(start..end)
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

#[derive(Debug, Clone, Copy)]
enum Scalar {
    Int(i64),
    Undefined,
}

impl Scalar {
    const fn truthy(self) -> bool {
        match self {
            Self::Int(v) => v != 0,
            Self::Undefined => false,
        }
    }

    const fn int(self) -> Option<i64> {
        match self {
            Self::Int(v) => Some(v),
            Self::Undefined => None,
        }
    }
}

fn eval_expr(expr: &Expression<'_>, env: &HashMap<String, Scalar>) -> Option<Scalar> {
    match expr {
        Expression::NumericLiteral(n) if n.value.is_finite() && n.value.fract() == 0.0 => {
            Some(Scalar::Int(n.value as i64))
        }
        Expression::BooleanLiteral(b) => Some(Scalar::Int(i64::from(b.value))),
        Expression::Identifier(id) => {
            if id.name.as_str() == "undefined" {
                Some(Scalar::Undefined)
            } else {
                env.get(id.name.as_str()).copied()
            }
        }
        Expression::ParenthesizedExpression(p) => eval_expr(&p.expression, env),
        Expression::UnaryExpression(u) => {
            let v = eval_expr(&u.argument, env)?;
            match u.operator.as_str() {
                "!" => Some(Scalar::Int(i64::from(!v.truthy()))),
                "~" => Some(Scalar::Int(!v.int()?)),
                "+" => Some(Scalar::Int(v.int()?)),
                "-" => Some(Scalar::Int(-v.int()?)),
                "void" => Some(Scalar::Undefined),
                _ => None,
            }
        }
        Expression::BinaryExpression(b) => {
            let lhs = eval_expr(&b.left, env)?;
            let rhs = eval_expr(&b.right, env)?;
            let op = b.operator.as_str();
            match op {
                "==" | "===" => Some(Scalar::Int(i64::from(match (lhs, rhs) {
                    (Scalar::Undefined, Scalar::Undefined) => true,
                    (Scalar::Int(a), Scalar::Int(b)) => a == b,
                    _ => false,
                }))),
                "!=" | "!==" => Some(Scalar::Int(i64::from(match (lhs, rhs) {
                    (Scalar::Undefined, Scalar::Undefined) => false,
                    (Scalar::Int(a), Scalar::Int(b)) => a != b,
                    _ => true,
                }))),
                "<" => Some(Scalar::Int(i64::from(lhs.int()? < rhs.int()?))),
                "<=" => Some(Scalar::Int(i64::from(lhs.int()? <= rhs.int()?))),
                ">" => Some(Scalar::Int(i64::from(lhs.int()? > rhs.int()?))),
                ">=" => Some(Scalar::Int(i64::from(lhs.int()? >= rhs.int()?))),
                "&" => Some(Scalar::Int(lhs.int()? & rhs.int()?)),
                "|" => Some(Scalar::Int(lhs.int()? | rhs.int()?)),
                "^" => Some(Scalar::Int(lhs.int()? ^ rhs.int()?)),
                "<<" => Some(Scalar::Int(lhs.int()? << rhs.int()?)),
                ">>" => Some(Scalar::Int(lhs.int()? >> rhs.int()?)),
                ">>>" => {
                    let a = lhs.int()? as u64;
                    let b = rhs.int()? as u32;
                    Some(Scalar::Int((a >> b) as i64))
                }
                "+" => Some(Scalar::Int(lhs.int()?.wrapping_add(rhs.int()?))),
                "-" => Some(Scalar::Int(lhs.int()?.wrapping_sub(rhs.int()?))),
                _ => None,
            }
        }
        Expression::LogicalExpression(l) => {
            let lhs = eval_expr(&l.left, env)?;
            match l.operator.as_str() {
                "&&" => {
                    if lhs.truthy() {
                        eval_expr(&l.right, env)
                    } else {
                        Some(lhs)
                    }
                }
                "||" => {
                    if lhs.truthy() {
                        Some(lhs)
                    } else {
                        eval_expr(&l.right, env)
                    }
                }
                _ => None,
            }
        }
        Expression::ConditionalExpression(c) => {
            if eval_expr(&c.test, env)?.truthy() {
                eval_expr(&c.consequent, env)
            } else {
                eval_expr(&c.alternate, env)
            }
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExecStatus {
    Normal,
    Break,
    Return,
    Throw,
}

fn exec_control_expr(
    expr: &Expression<'_>,
    source: &str,
    state_var: &str,
    env: &mut HashMap<String, Scalar>,
    semantic: &mut Vec<String>,
) {
    match expr {
        Expression::ParenthesizedExpression(p) => {
            exec_control_expr(&p.expression, source, state_var, env, semantic);
        }
        Expression::SequenceExpression(s) => {
            for e in &s.expressions {
                exec_control_expr(e, source, state_var, env, semantic);
            }
        }
        Expression::AssignmentExpression(a)
            if a.operator.is_assign() && a.left.get_identifier_name() == Some(state_var) =>
        {
            if let Some(v) = eval_expr(&a.right, env) {
                env.insert(state_var.to_string(), v);
            } else {
                semantic.push(slice(source, a.span));
            }
        }
        Expression::ConditionalExpression(c) => {
            if let Some(test) = eval_expr(&c.test, env) {
                let branch = if test.truthy() {
                    &c.consequent
                } else {
                    &c.alternate
                };
                exec_control_expr(branch, source, state_var, env, semantic);
            } else {
                semantic.push(slice(source, c.span));
            }
        }
        Expression::LogicalExpression(l) => {
            if let Some(lhs) = eval_expr(&l.left, env) {
                match l.operator.as_str() {
                    "&&" if lhs.truthy() => {
                        exec_control_expr(&l.right, source, state_var, env, semantic);
                    }
                    "||" if !lhs.truthy() => {
                        exec_control_expr(&l.right, source, state_var, env, semantic);
                    }
                    "&&" | "||" => {}
                    _ => semantic.push(slice(source, l.span)),
                }
            } else {
                semantic.push(slice(source, l.span));
            }
        }
        _ => semantic.push(slice(source, expr.span())),
    }
}

fn exec_statements(
    statements: &[Statement<'_>],
    source: &str,
    state_var: &str,
    env: &mut HashMap<String, Scalar>,
    semantic: &mut Vec<String>,
) -> ExecStatus {
    for stmt in statements {
        let status = exec_statement(stmt, source, state_var, env, semantic);
        if status != ExecStatus::Normal {
            return status;
        }
    }
    ExecStatus::Normal
}

fn exec_function_body(
    body: &FunctionBody<'_>,
    source: &str,
    state_var: &str,
    env: &mut HashMap<String, Scalar>,
    semantic: &mut Vec<String>,
) -> ExecStatus {
    exec_statements(&body.statements, source, state_var, env, semantic)
}

fn expression_function_body<'a>(expr: &'a Expression<'a>) -> Option<&'a FunctionBody<'a>> {
    match expr {
        Expression::FunctionExpression(fun) => fun.body.as_deref(),
        Expression::ArrowFunctionExpression(fun) => Some(&fun.body),
        Expression::ParenthesizedExpression(paren) => expression_function_body(&paren.expression),
        _ => None,
    }
}

fn argument_function_body<'a>(arg: &'a Argument<'a>) -> Option<&'a FunctionBody<'a>> {
    match arg {
        Argument::FunctionExpression(fun) => fun.body.as_deref(),
        Argument::ArrowFunctionExpression(fun) => Some(&fun.body),
        Argument::ParenthesizedExpression(paren) => expression_function_body(&paren.expression),
        _ => None,
    }
}

fn exec_statement(
    stmt: &Statement<'_>,
    source: &str,
    state_var: &str,
    env: &mut HashMap<String, Scalar>,
    semantic: &mut Vec<String>,
) -> ExecStatus {
    match stmt {
        Statement::BlockStatement(b) => exec_statements(&b.body, source, state_var, env, semantic),
        Statement::ExpressionStatement(e) => {
            if let Expression::CallExpression(call) = &e.expression {
                if let Some(body) = call.arguments.first().and_then(argument_function_body) {
                    return exec_function_body(body, source, state_var, env, semantic);
                }
            }
            exec_control_expr(&e.expression, source, state_var, env, semantic);
            ExecStatus::Normal
        }
        Statement::IfStatement(i) => {
            let Some(test) = eval_expr(&i.test, env) else {
                semantic.push(slice(source, i.span));
                return ExecStatus::Normal;
            };
            if test.truthy() {
                exec_statement(&i.consequent, source, state_var, env, semantic)
            } else if let Some(alt) = &i.alternate {
                exec_statement(alt, source, state_var, env, semantic)
            } else {
                ExecStatus::Normal
            }
        }
        Statement::TryStatement(t) => {
            semantic.push(slice(source, t.span));
            ExecStatus::Normal
        }
        Statement::ThrowStatement(t) => {
            semantic.push(slice(source, t.span));
            ExecStatus::Throw
        }
        Statement::ReturnStatement(r) => {
            semantic.push(slice(source, r.span));
            ExecStatus::Return
        }
        Statement::BreakStatement(_) => ExecStatus::Break,
        _ => {
            semantic.push(slice(source, stmt.span()));
            ExecStatus::Normal
        }
    }
}

struct NumericMaskCollector<'m> {
    masks: &'m BTreeSet<u64>,
    found: BTreeSet<u64>,
}

impl<'a> Visit<'a> for NumericMaskCollector<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        if let AstKind::NumericLiteral(n) = kind {
            if let Some(value) = exact_u64(n.value) {
                if self.masks.contains(&value) {
                    self.found.insert(value);
                }
            }
        }
    }
}

#[derive(Default)]
struct IdentifierCollector {
    names: BTreeSet<String>,
}

impl<'a> Visit<'a> for IdentifierCollector {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        if let AstKind::IdentifierReference(id) = kind {
            self.names.insert(id.name.to_string());
        }
    }
}

struct MaskBindingCollector<'m> {
    loop_start: u32,
    masks: &'m BTreeSet<u64>,
    selector_var: &'m str,
    aliases: HashMap<String, String>,
    targets: HashMap<String, (BTreeSet<u64>, u32)>,
}

impl MaskBindingCollector<'_> {
    fn resolve_alias(&self, name: &str) -> String {
        let mut cur = name.to_string();
        let mut seen = BTreeSet::new();
        while seen.insert(cur.clone()) {
            let Some(next) = self.aliases.get(&cur) else {
                break;
            };
            cur.clone_from(next);
        }
        cur
    }

    fn rhs_depends_on_selector(&self, expr: &Expression<'_>) -> bool {
        let mut ids = IdentifierCollector::default();
        ids.visit_expression(expr);
        ids.names
            .iter()
            .any(|name| name == self.selector_var || self.resolve_alias(name) == self.selector_var)
    }

    fn direct_alias_rhs(&self, expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::Identifier(id) => {
                let resolved = self.resolve_alias(id.name.as_str());
                (resolved == self.selector_var).then_some(resolved)
            }
            Expression::ParenthesizedExpression(p) => self.direct_alias_rhs(&p.expression),
            _ => None,
        }
    }

    fn record_binding(&mut self, target: &str, rhs: &Expression<'_>, start: u32) {
        if start >= self.loop_start {
            return;
        }

        let depends = self.rhs_depends_on_selector(rhs);
        if depends {
            let mut collector = NumericMaskCollector {
                masks: self.masks,
                found: BTreeSet::new(),
            };
            collector.visit_expression(rhs);
            if !collector.found.is_empty() {
                let entry = self
                    .targets
                    .entry(target.to_string())
                    .or_insert_with(|| (BTreeSet::new(), 0));
                entry.0.extend(collector.found);
                entry.1 = entry.1.max(start);
            }
        }

        if let Some(alias) = self.direct_alias_rhs(rhs) {
            self.aliases.insert(target.to_string(), alias);
        } else if !depends {
            self.aliases.remove(target);
        }
    }
}

impl<'a> Visit<'a> for MaskBindingCollector<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::AssignmentExpression(a) => {
                if !a.operator.is_assign() {
                    return;
                }
                let Some(target) = a.left.get_identifier_name() else {
                    return;
                };
                self.record_binding(target, &a.right, a.span.start);
            }
            AstKind::VariableDeclarator(v) => {
                let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &v.id else {
                    return;
                };
                let Some(init) = &v.init else {
                    return;
                };
                self.record_binding(id.name.as_str(), init, v.span.start);
            }
            _ => {}
        }
    }
}

fn derive_bindings(
    source: &str,
    function: &Function<'_>,
    loop_start: u32,
    loop_end: u32,
    selector_var: &str,
    masks: &[u64],
) -> BTreeMap<String, u64> {
    let Some(body) = &function.body else {
        return BTreeMap::new();
    };

    let mask_set: BTreeSet<u64> = masks.iter().copied().collect();
    let mut collector = MaskBindingCollector {
        loop_start,
        masks: &mask_set,
        selector_var,
        aliases: HashMap::new(),
        targets: HashMap::new(),
    };
    collector.visit_function_body(body);

    let loop_text = source
        .get(loop_start as usize..loop_end as usize)
        .unwrap_or_default();

    let mut by_mask: BTreeMap<u64, Vec<(String, u32)>> = BTreeMap::new();
    for (name, (found, last_start)) in collector.targets {
        if found.len() != 1 || !loop_text.contains(&name) {
            continue;
        }
        let Some(mask) = found.iter().next().copied() else {
            continue;
        };
        by_mask.entry(mask).or_default().push((name, last_start));
    }

    let mut out = BTreeMap::new();
    for mask in masks {
        let Some(candidates) = by_mask.get_mut(mask) else {
            continue;
        };
        candidates.sort_by_key(|(_, start)| *start);
        if let Some((name, _)) = candidates.last() {
            out.insert(name.clone(), *mask);
        }
    }
    out
}

struct LoopRunner<'s, 'm> {
    source: &'s str,
    parent_function_id: &'s str,
    decoder: &'m DecoderControlInfo,
    machine: &'m StateMachineInfo,
    bindings: &'m BTreeMap<String, u64>,
    result: Option<OpcodeMapCandidate>,
}

fn numeric_case_map<'a>(switch: &'a SwitchStatement<'a>) -> BTreeMap<u64, &'a [Statement<'a>]> {
    switch
        .cases
        .iter()
        .filter_map(|case| {
            let Expression::NumericLiteral(number) = case.test.as_ref()? else {
                return None;
            };
            exact_u64(number.value).map(|value| (value, case.consequent.as_slice()))
        })
        .collect()
}

impl LoopRunner<'_, '_> {
    fn simulate_opcode<'a>(
        &self,
        opcode: u64,
        case_map: &BTreeMap<u64, &'a [Statement<'a>]>,
        observed_opcodes: &BTreeSet<u64>,
    ) -> OpcodeHandler {
        let mut env = self
            .bindings
            .iter()
            .map(|(name, mask)| (name.clone(), Scalar::Int((opcode & mask) as i64)))
            .collect::<HashMap<_, _>>();
        let mut state = self.machine.init_state;
        let mut path = Vec::new();
        let mut semantic = Vec::new();
        let mut terminal = "step-limit".to_string();

        for _ in 0..128 {
            path.push(state);
            env.insert(self.machine.state_var.clone(), Scalar::Int(state as i64));

            if let (Some(shift), Some(selector)) =
                (self.machine.shift, self.machine.selector_var.as_ref())
            {
                let selected = (state >> shift) & self.machine.mask;
                env.insert(selector.clone(), Scalar::Int(selected as i64));
            }

            let low = state & self.machine.mask;
            let Some(statements) = case_map.get(&low) else {
                terminal = format!("missing-case-{low}");
                break;
            };
            match exec_statements(
                statements,
                self.source,
                &self.machine.state_var,
                &mut env,
                &mut semantic,
            ) {
                ExecStatus::Return => {
                    terminal = "return".to_string();
                    break;
                }
                ExecStatus::Throw => {
                    terminal = "throw".to_string();
                    break;
                }
                ExecStatus::Break | ExecStatus::Normal => {}
            }

            match env.get(&self.machine.state_var).copied() {
                Some(Scalar::Int(next)) if next >= 0 => {
                    let next = next as u64;
                    if next == state {
                        terminal = "stuck".to_string();
                        break;
                    }
                    state = next;
                }
                Some(Scalar::Undefined) | None => {
                    terminal = "exit".to_string();
                    break;
                }
                Some(Scalar::Int(_)) => {
                    terminal = "negative-state".to_string();
                    break;
                }
            }
        }

        OpcodeHandler {
            opcode,
            observed: observed_opcodes.contains(&opcode),
            path,
            terminal,
            semantic,
        }
    }

    fn build_opcode_map(&self, switch: &SwitchStatement<'_>) -> Option<OpcodeMapCandidate> {
        let case_map = numeric_case_map(switch);
        let opcode_max = self
            .decoder
            .selector_masks
            .iter()
            .copied()
            .fold(0u64, |acc, value| acc | value);
        if opcode_max > 255 {
            return None;
        }

        let observed_opcodes = self
            .decoder
            .observed_opcodes
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        let handlers = (0..=opcode_max)
            .map(|opcode| self.simulate_opcode(opcode, &case_map, &observed_opcodes))
            .collect();

        Some(OpcodeMapCandidate {
            parent_function_id: self.parent_function_id.to_string(),
            decoder_function_id: self.decoder.function_id.clone(),
            decoder_selector_var: self.decoder.selector_var.clone(),
            state_machine_start: self.machine.start,
            state_machine_end: self.machine.end,
            state_var: self.machine.state_var.clone(),
            selector_bindings: self.bindings.clone(),
            opcode_max,
            observed_opcodes: self.decoder.observed_opcodes.clone(),
            handlers,
        })
    }
}

impl<'a> Visit<'a> for LoopRunner<'_, '_> {
    fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
        if self.result.is_some() {
            return;
        }
        if statement.span.start != self.machine.start || statement.span.end != self.machine.end {
            walk::walk_for_statement(self, statement);
            return;
        }

        let Statement::BlockStatement(body) = &statement.body else {
            return;
        };
        let switch = body.body.iter().find_map(|statement| {
            if let Statement::SwitchStatement(switch) = statement {
                Some(switch)
            } else {
                None
            }
        });
        self.result = switch.and_then(|switch| self.build_opcode_map(switch));
    }
}

const fn ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'$'
}

fn count_identifier(text: &[u8], name: &str) -> usize {
    let needle = name.as_bytes();
    if needle.is_empty() || text.len() < needle.len() {
        return 0;
    }

    let mut count = 0usize;
    for start in 0..=text.len() - needle.len() {
        if &text[start..start + needle.len()] != needle {
            continue;
        }
        let before_ok = start == 0 || !ident_byte(text[start - 1]);
        let after = start + needle.len();
        let after_ok = after == text.len() || !ident_byte(text[after]);
        if before_ok && after_ok {
            count += 1;
        }
    }
    count
}

fn direct_binding_score(
    source: &str,
    machine: &StateMachineInfo,
    all_machines: &[StateMachineInfo],
    bindings: &BTreeMap<String, u64>,
) -> usize {
    let start = machine.start as usize;
    let end = (machine.end as usize).min(source.len());
    if start >= end {
        return 0;
    }

    // Outer protector loops physically contain the real opcode loop. Remove
    // nested state-machine spans so the outer loop cannot inherit references
    // to opcode-bit variables from the inner semantic dispatcher.
    let mut direct = source.as_bytes()[start..end].to_vec();
    for nested in all_machines {
        if nested.start <= machine.start || nested.end >= machine.end {
            continue;
        }
        let ns = (nested.start as usize)
            .saturating_sub(start)
            .min(direct.len());
        let ne = (nested.end as usize)
            .saturating_sub(start)
            .min(direct.len());
        if ns < ne {
            direct[ns..ne].fill(b' ');
        }
    }

    bindings
        .keys()
        .map(|name| count_identifier(&direct, name))
        .sum()
}

pub fn analyze_function(
    source: &str,
    function: &Function<'_>,
    parent_function_id: &str,
    decoders: &[DecoderControlInfo],
    machines: &[StateMachineInfo],
) -> Vec<OpcodeMapCandidate> {
    let Some(body) = &function.body else {
        return Vec::new();
    };

    let mut out = Vec::new();

    for decoder in decoders {
        if decoder.selector_masks.len() < 2 {
            continue;
        }
        let mask_set: BTreeSet<u64> = decoder.selector_masks.iter().copied().collect();
        if !mask_set.iter().all(|m| m.is_power_of_two()) {
            continue;
        }

        let mut candidates = Vec::new();
        for machine in machines {
            let bindings = derive_bindings(
                source,
                function,
                machine.start,
                machine.end,
                &decoder.selector_var,
                &decoder.selector_masks,
            );
            if bindings.len() != mask_set.len() {
                continue;
            }
            let bound_masks: BTreeSet<u64> = bindings.values().copied().collect();
            if bound_masks != mask_set {
                continue;
            }

            let score = direct_binding_score(source, machine, machines, &bindings);
            if score == 0 {
                continue;
            }
            candidates.push((score, machine.end - machine.start, machine, bindings));
        }

        // Prefer the machine that actually consumes the opcode-bit flags.
        // Smaller span wins a tie so an inner semantic dispatcher beats an
        // enclosing control/exception loop.
        candidates.sort_by(|a, b| {
            b.0.cmp(&a.0)
                .then_with(|| a.1.cmp(&b.1))
                .then_with(|| a.2.start.cmp(&b.2.start))
        });

        for (_, _, machine, bindings) in candidates {
            let mut runner = LoopRunner {
                source,
                parent_function_id,
                decoder,
                machine,
                bindings: &bindings,
                result: None,
            };
            runner.visit_function_body(body);
            if let Some(result) = runner.result {
                out.push(result);
                break;
            }
        }
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    #[derive(Default)]
    struct DetectorHarness<'s> {
        source: &'s str,
        detected: DetectedStateMachines,
    }

    impl<'a> Visit<'a> for DetectorHarness<'_> {
        fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
            let detected = detect_for_state_machines(self.source, "test-function", statement);
            self.detected
                .switch_machines
                .extend(detected.switch_machines);
            self.detected
                .if_ladder_machines
                .extend(detected.if_ladder_machines);
            walk::walk_for_statement(self, statement);
        }
    }

    fn detect(source: &str) -> DetectedStateMachines {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let mut harness = DetectorHarness {
            source,
            detected: DetectedStateMachines::default(),
        };
        harness.visit_program(&parsed.program);
        harness.detected
    }

    #[test]
    fn detects_switch_state_machine() {
        let detected = detect(
            r"
            function vm() {
                for (let state = 17; state !== undefined;) {
                    let selector = (state >> 3) & 7;
                    switch (state & 7) {
                        case 0: state = 8; break;
                        case 1: state = 9; break;
                        default: state = undefined;
                    }
                }
            }
            ",
        );

        assert_eq!(detected.switch_machines.len(), 1);
        let machine = &detected.switch_machines[0];
        assert_eq!(machine.function_id, "test-function");
        assert_eq!(machine.state_var, "state");
        assert_eq!(machine.init_state, 17);
        assert_eq!(machine.mask, 7);
        assert_eq!(machine.shift, Some(3));
        assert_eq!(machine.selector_var.as_deref(), Some("selector"));
        assert_eq!(machine.switch_cases, 3);
        assert!(detected.if_ladder_machines.is_empty());
    }

    #[test]
    fn detects_if_ladder_state_machine() {
        let detected = detect(
            r"
            function flattened() {
                for (let state = 0; state !== 99;) {
                    if (state === 0) { state = 1; }
                    else if (state === 1) { state = 2; }
                    else if (state === 2) { state = 3; }
                    else if (state === 3) { state = 99; }
                }
            }
            ",
        );

        assert!(detected.switch_machines.is_empty());
        assert_eq!(detected.if_ladder_machines.len(), 1);
        let machine = &detected.if_ladder_machines[0];
        assert_eq!(machine.state_var, "state");
        assert_eq!(machine.init_state, 0);
        assert_eq!(machine.exit_state, 99);
        assert_eq!(machine.compared_states, vec![0, 1, 2, 3]);
        assert_eq!(machine.state_assignments, 4);
        assert_eq!(machine.constant_state_assignments, 4);
        assert_eq!(machine.dynamic_state_assignments, 0);
    }

    #[test]
    fn ignores_ordinary_counted_loop() {
        let detected = detect("for (let i = 0; i < 10; i += 1) { work(i); }");
        assert!(detected.switch_machines.is_empty());
        assert!(detected.if_ladder_machines.is_empty());
    }
}
