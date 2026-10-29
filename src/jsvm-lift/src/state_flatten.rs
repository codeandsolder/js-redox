use crate::numeric::{eval_js_bitwise_i64, exact_i64, exact_u64, js_int32_from_i64};
use crate::{
    ast_utils::{expr_ident, numeric_u64, target_ident},
    source_text::preview,
};
use jsvm_safe_core::eval_static_primitive as eval_static;
use oxc_ast::{
    ast::{
        Argument, BindingPattern, Expression, ForStatement, Function, FunctionBody, Program,
        Statement, SwitchStatement, WhileStatement,
    },
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::scope::ScopeFlags;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

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

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct IfLadderTransitionCandidate {
    pub from_state: u64,
    pub target_state: Option<u64>,
    pub possible_target_states: Vec<u64>,
    pub target_expression: String,
    pub assignment_start: u32,
    pub assignment_end: u32,
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
    pub transitions: Vec<IfLadderTransitionCandidate>,
    pub preview: String,
}

#[derive(Debug, Default)]
pub struct DetectedStateMachines {
    pub switch_machines: Vec<StateMachineCandidate>,
    pub if_ladder_machines: Vec<IfLadderStateMachineCandidate>,
}

fn static_u64(expr: &Expression<'_>) -> Option<u64> {
    eval_static(expr).and_then(|value| exact_u64(value.number()?))
}

fn finite_static_state_targets(expr: &Expression<'_>) -> Option<BTreeSet<u64>> {
    if let Some(value) = static_u64(expr) {
        return Some(BTreeSet::from([value]));
    }
    match expr {
        Expression::ParenthesizedExpression(paren) => {
            finite_static_state_targets(&paren.expression)
        }
        Expression::SequenceExpression(sequence) => {
            finite_static_state_targets(sequence.expressions.last()?)
        }
        Expression::ConditionalExpression(conditional) => {
            let mut targets = finite_static_state_targets(&conditional.consequent)?;
            targets.extend(finite_static_state_targets(&conditional.alternate)?);
            Some(targets)
        }
        _ => None,
    }
}

fn assignment_state_init(
    assignment: &oxc_ast::ast::AssignmentExpression<'_>,
) -> Option<(String, u64)> {
    if !assignment.operator.is_assign() {
        return None;
    }
    let state_var = target_ident(&assignment.left)?.to_string();
    Some((state_var, static_u64(&assignment.right)?))
}

fn for_state_init(for_stmt: &ForStatement<'_>) -> Option<(String, u64)> {
    let init = for_stmt.init.as_ref()?;
    match init {
        oxc_ast::ast::ForStatementInit::VariableDeclaration(decl) => {
            for declarator in &decl.declarations {
                let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &declarator.id else {
                    continue;
                };
                let value = declarator.init.as_ref().and_then(static_u64)?;
                return Some((id.name.to_string(), value));
            }
            None
        }
        oxc_ast::ast::ForStatementInit::AssignmentExpression(assignment) => {
            assignment_state_init(assignment)
        }
        oxc_ast::ast::ForStatementInit::SequenceExpression(sequence) => sequence
            .expressions
            .iter()
            .rev()
            .find_map(|expr| match expr {
                Expression::AssignmentExpression(assignment) => assignment_state_init(assignment),
                Expression::ParenthesizedExpression(paren) => match &paren.expression {
                    Expression::AssignmentExpression(assignment) => {
                        assignment_state_init(assignment)
                    }
                    _ => None,
                },
                _ => None,
            }),
        _ => None,
    }
}

fn assignment_state_value(
    assignment: &oxc_ast::ast::AssignmentExpression<'_>,
    state_var: &str,
) -> Option<u64> {
    if !assignment.operator.is_assign() || target_ident(&assignment.left) != Some(state_var) {
        return None;
    }
    static_u64(&assignment.right)
}

fn statement_state_init(statement: &Statement<'_>, state_var: &str) -> Option<u64> {
    match statement {
        Statement::ExpressionStatement(statement) => match &statement.expression {
            Expression::AssignmentExpression(assignment) => {
                assignment_state_value(assignment, state_var)
            }
            Expression::SequenceExpression(sequence) => {
                sequence
                    .expressions
                    .iter()
                    .rev()
                    .find_map(|expression| match expression {
                        Expression::AssignmentExpression(assignment) => {
                            assignment_state_value(assignment, state_var)
                        }
                        Expression::ParenthesizedExpression(parenthesized) => {
                            match &parenthesized.expression {
                                Expression::AssignmentExpression(assignment) => {
                                    assignment_state_value(assignment, state_var)
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    })
            }
            Expression::ParenthesizedExpression(parenthesized) => {
                let Expression::AssignmentExpression(assignment) = &parenthesized.expression else {
                    return None;
                };
                assignment_state_value(assignment, state_var)
            }
            _ => None,
        },
        Statement::VariableDeclaration(declaration) => {
            declaration.declarations.iter().find_map(|declarator| {
                let oxc_ast::ast::BindingPattern::BindingIdentifier(identifier) = &declarator.id
                else {
                    return None;
                };
                if identifier.name != state_var {
                    return None;
                }
                declarator.init.as_ref().and_then(static_u64)
            })
        }
        _ => None,
    }
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

fn state_exit(expr: &Expression<'_>) -> Option<(String, u64)> {
    let Expression::BinaryExpression(binary) = expr else {
        return None;
    };
    if !matches!(binary.operator.as_str(), "!=" | "!==") {
        return None;
    }
    if let (Some(state_var), Some(exit_state)) =
        (expr_ident(&binary.left), numeric_u64(&binary.right))
    {
        return Some((state_var.to_string(), exit_state));
    }
    if let (Some(exit_state), Some(state_var)) =
        (numeric_u64(&binary.left), expr_ident(&binary.right))
    {
        return Some((state_var.to_string(), exit_state));
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

struct BranchAssignmentCollector<'s> {
    source: &'s str,
    state_var: &'s str,
    from_state: u64,
    transitions: Vec<IfLadderTransitionCandidate>,
}

impl<'a> Visit<'a> for BranchAssignmentCollector<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        let AstKind::AssignmentExpression(assign) = kind else {
            return;
        };
        if !assign.operator.is_assign() || target_ident(&assign.left) != Some(self.state_var) {
            return;
        }
        let possible_target_states = finite_static_state_targets(&assign.right)
            .map(|targets| targets.into_iter().collect::<Vec<_>>())
            .unwrap_or_default();
        let target_state = (possible_target_states.len() == 1).then(|| possible_target_states[0]);
        self.transitions.push(IfLadderTransitionCandidate {
            from_state: self.from_state,
            target_state,
            possible_target_states,
            target_expression: slice(self.source, assign.right.span()),
            assignment_start: assign.span.start,
            assignment_end: assign.span.end,
        });
    }

    fn visit_function(&mut self, _it: &Function<'a>, _flags: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
}

fn collect_branch_statement_transitions(
    source: &str,
    statement: &Statement<'_>,
    state_var: &str,
    from_state: u64,
    transitions: &mut Vec<IfLadderTransitionCandidate>,
) {
    let mut collector = BranchAssignmentCollector {
        source,
        state_var,
        from_state,
        transitions: Vec::new(),
    };
    collector.visit_statement(statement);
    transitions.extend(collector.transitions);
}

fn collect_branch_expression_transitions(
    source: &str,
    expression: &Expression<'_>,
    state_var: &str,
    from_state: u64,
    transitions: &mut Vec<IfLadderTransitionCandidate>,
) {
    let mut collector = BranchAssignmentCollector {
        source,
        state_var,
        from_state,
        transitions: Vec::new(),
    };
    collector.visit_expression(expression);
    transitions.extend(collector.transitions);
}

struct BranchTransitionVisitor<'s> {
    source: &'s str,
    state_var: &'s str,
    transitions: Vec<IfLadderTransitionCandidate>,
}

impl<'a> Visit<'a> for BranchTransitionVisitor<'_> {
    fn visit_if_statement(&mut self, statement: &oxc_ast::ast::IfStatement<'a>) {
        if let Expression::BinaryExpression(binary) = &statement.test {
            if let Some(from_state) = binary_state_comparison_literal(binary, self.state_var) {
                collect_branch_statement_transitions(
                    self.source,
                    &statement.consequent,
                    self.state_var,
                    from_state,
                    &mut self.transitions,
                );
            }
        }
        walk::walk_if_statement(self, statement);
    }

    fn visit_conditional_expression(
        &mut self,
        expression: &oxc_ast::ast::ConditionalExpression<'a>,
    ) {
        if let Expression::BinaryExpression(binary) = &expression.test {
            if let Some(from_state) = binary_state_comparison_literal(binary, self.state_var) {
                collect_branch_expression_transitions(
                    self.source,
                    &expression.consequent,
                    self.state_var,
                    from_state,
                    &mut self.transitions,
                );
            }
        }
        walk::walk_conditional_expression(self, expression);
    }

    fn visit_function(&mut self, _it: &Function<'a>, _flags: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
}

fn collect_branch_ladder_transitions(
    source: &str,
    statement: &Statement<'_>,
    state_var: &str,
) -> Vec<IfLadderTransitionCandidate> {
    let mut visitor = BranchTransitionVisitor {
        source,
        state_var,
        transitions: Vec::new(),
    };
    visitor.visit_statement(statement);
    visitor.transitions
}

struct BranchStateForSpan<'s> {
    state_var: &'s str,
    target: Span,
    best: Option<(u32, u64)>,
}

impl BranchStateForSpan<'_> {
    fn consider(&mut self, state: u64, span: Span) {
        if span.start <= self.target.start && self.target.end <= span.end {
            let width = span.end.saturating_sub(span.start);
            if self.best.is_none_or(|(best_width, _)| width < best_width) {
                self.best = Some((width, state));
            }
        }
    }
}

impl<'a> Visit<'a> for BranchStateForSpan<'_> {
    fn visit_if_statement(&mut self, statement: &oxc_ast::ast::IfStatement<'a>) {
        if let Expression::BinaryExpression(binary) = &statement.test {
            if let Some(state) = binary_state_comparison_literal(binary, self.state_var) {
                self.consider(state, statement.consequent.span());
            }
        }
        walk::walk_if_statement(self, statement);
    }

    fn visit_conditional_expression(
        &mut self,
        expression: &oxc_ast::ast::ConditionalExpression<'a>,
    ) {
        if let Expression::BinaryExpression(binary) = &expression.test {
            if let Some(state) = binary_state_comparison_literal(binary, self.state_var) {
                self.consider(state, expression.consequent.span());
            }
        }
        walk::walk_conditional_expression(self, expression);
    }

    fn visit_function(&mut self, _it: &Function<'a>, _flags: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
}

fn branch_state_for_span(statement: &Statement<'_>, state_var: &str, target: Span) -> Option<u64> {
    let mut visitor = BranchStateForSpan {
        state_var,
        target,
        best: None,
    };
    visitor.visit_statement(statement);
    visitor.best.map(|(_, state)| state)
}

/// Prove that, if an event inside a recognized flattened if-ladder executes,
/// no listed barrier can have executed earlier on any statically known path
/// from the machine's initial state.
///
/// Finite transition sets are treated as nondeterministic edges. An unresolved
/// transition on any reachable prefix fails closed. Paths that exit without
/// reaching the event are irrelevant. Barriers in the event's own state are
/// ordered by source evaluation position; callers decide what constitutes a
/// barrier.
fn prove_machine_event_before_barriers(
    machine: &IfLadderStateMachineCandidate,
    body: &Statement<'_>,
    event: Span,
    barriers: &[Span],
) -> bool {
    let Some(event_state) = branch_state_for_span(body, &machine.state_var, event) else {
        return false;
    };

    let mut barrier_states: HashMap<u64, Vec<Span>> = HashMap::new();
    for barrier in barriers {
        if barrier.start < machine.start || barrier.end > machine.end {
            continue;
        }
        let Some(state) = branch_state_for_span(body, &machine.state_var, *barrier) else {
            return false;
        };
        barrier_states.entry(state).or_default().push(*barrier);
    }

    let mut edges: HashMap<u64, BTreeSet<u64>> = HashMap::new();
    let mut unresolved = BTreeSet::new();
    for transition in &machine.transitions {
        if transition.possible_target_states.is_empty() {
            unresolved.insert(transition.from_state);
            continue;
        }
        edges
            .entry(transition.from_state)
            .or_default()
            .extend(transition.possible_target_states.iter().copied());
    }

    let mut queue = VecDeque::from([(machine.init_state, false)]);
    let mut seen = BTreeSet::new();
    let mut reached_unsafe = false;
    while let Some((state, already_crossed_barrier)) = queue.pop_front() {
        if !seen.insert((state, already_crossed_barrier)) {
            continue;
        }

        let barriers_here = barrier_states.get(&state);
        if state == event_state {
            let crossed_before_event = already_crossed_barrier
                || barriers_here
                    .is_some_and(|spans| spans.iter().any(|barrier| barrier.start < event.start));
            reached_unsafe |= crossed_before_event;
            continue;
        }

        let crossed_barrier =
            already_crossed_barrier || barriers_here.is_some_and(|spans| !spans.is_empty());
        if unresolved.contains(&state) {
            return false;
        }
        if let Some(targets) = edges.get(&state) {
            queue.extend(targets.iter().map(|target| (*target, crossed_barrier)));
        }
    }

    !reached_unsafe
}

fn prove_machine_event_unreachable_with_integer_bindings(
    machine: &IfLadderStateMachineCandidate,
    body: &Statement<'_>,
    event: Span,
    bindings: &BTreeMap<String, i64>,
) -> bool {
    let Some(event_state) = branch_state_for_span(body, &machine.state_var, event) else {
        return false;
    };
    let Ok(init_state) = i64::try_from(machine.init_state) else {
        return false;
    };
    let mut env = bindings
        .iter()
        .map(|(name, value)| (name.clone(), Scalar::Int(*value)))
        .collect::<HashMap<_, _>>();
    env.insert(machine.state_var.clone(), Scalar::Int(init_state));
    let mut seen = BTreeSet::new();

    for _ in 0..256 {
        let Some(Scalar::Int(state_i64)) = env.get(&machine.state_var).copied() else {
            return false;
        };
        let Ok(state) = u64::try_from(state_i64) else {
            return false;
        };
        if state == event_state {
            return false;
        }
        if state == machine.exit_state {
            return true;
        }
        if !seen.insert(state) {
            return false;
        }

        let before = env.get(&machine.state_var).copied();
        let mut semantic = Vec::new();
        let mut ambiguous_envs = Vec::new();
        match exec_statement(
            body,
            "",
            &machine.state_var,
            &mut env,
            &mut semantic,
            &mut ambiguous_envs,
        ) {
            ExecStatus::Return | ExecStatus::Throw => return true,
            ExecStatus::Break | ExecStatus::Normal => {}
        }
        if env.get(&machine.state_var).copied() == before {
            return false;
        }
    }
    false
}

/// Prove that an event in a detected flattened if-ladder is unreachable when
/// selected scalar identifiers have exact integer values at machine entry.
///
/// This executes only the already-supported scalar/control subset and fails
/// closed on unsupported semantics, repeated states, or paths that do not
/// deterministically reach a return/throw/exit without the event state.
pub fn prove_detected_if_ladder_event_unreachable_with_integer_bindings(
    program: &Program<'_>,
    machine: &IfLadderStateMachineCandidate,
    event: Span,
    bindings: &BTreeMap<String, i64>,
) -> bool {
    struct Harness<'m, 'b> {
        machine: &'m IfLadderStateMachineCandidate,
        event: Span,
        bindings: &'b BTreeMap<String, i64>,
        result: Option<bool>,
    }

    impl<'a> Visit<'a> for Harness<'_, '_> {
        fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
            if self.result.is_some() {
                return;
            }
            if statement.span.start == self.machine.start && statement.span.end == self.machine.end
            {
                self.result = Some(prove_machine_event_unreachable_with_integer_bindings(
                    self.machine,
                    &statement.body,
                    self.event,
                    self.bindings,
                ));
                return;
            }
            walk::walk_for_statement(self, statement);
        }

        fn visit_while_statement(&mut self, statement: &WhileStatement<'a>) {
            if self.result.is_some() {
                return;
            }
            if statement.span.start == self.machine.start && statement.span.end == self.machine.end
            {
                self.result = Some(prove_machine_event_unreachable_with_integer_bindings(
                    self.machine,
                    &statement.body,
                    self.event,
                    self.bindings,
                ));
                return;
            }
            walk::walk_while_statement(self, statement);
        }
    }

    let mut harness = Harness {
        machine,
        event,
        bindings,
        result: None,
    };
    harness.visit_program(program);
    harness.result.unwrap_or(false)
}

/// Prove a flattened if-ladder event unreachable for one exact function when
/// selected formal parameters have exact integer values at call time.
///
/// Parameter bindings are keyed by formal-parameter index, so callers can join
/// against symbol-resolved direct-call proofs without relying on source names.
#[must_use]
fn exact_integer_parameter_env(
    function: &Function<'_>,
    scoping: &Scoping,
    parameter_bindings: &BTreeMap<usize, i64>,
) -> Option<HashMap<String, Scalar>> {
    let mut env = HashMap::new();
    for (index, value) in parameter_bindings {
        let parameter = function.params.items.get(*index)?;
        let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
            return None;
        };
        let symbol = identifier.symbol_id.get()?;
        if scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .any(|reference_id| scoping.get_reference(*reference_id).is_write())
        {
            return None;
        }
        env.insert(identifier.name.to_string(), Scalar::Int(*value));
    }

    #[derive(Default)]
    struct DynamicScalarProbe {
        dynamic_scope: bool,
        arguments_object: bool,
    }
    impl<'a> Visit<'a> for DynamicScalarProbe {
        fn visit_with_statement(&mut self, _statement: &oxc_ast::ast::WithStatement<'a>) {
            self.dynamic_scope = true;
        }
        fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
            if matches!(&call.callee, Expression::Identifier(id) if id.name.as_str() == "eval") {
                self.dynamic_scope = true;
            }
            walk::walk_call_expression(self, call);
        }
        fn visit_identifier_reference(
            &mut self,
            identifier: &oxc_ast::ast::IdentifierReference<'a>,
        ) {
            if identifier.name.as_str() == "arguments" {
                self.arguments_object = true;
            }
        }
        fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
        }
    }
    let mut probe = DynamicScalarProbe::default();
    probe.visit_function_body(function.body.as_deref()?);
    (!probe.dynamic_scope && !probe.arguments_object).then_some(env)
}

fn exact_call_parameter_env(
    function: &Function<'_>,
    scoping: &Scoping,
    parameter_bindings: &BTreeMap<usize, i64>,
    provided_argument_count: usize,
) -> Option<HashMap<String, Scalar>> {
    if function.params.rest.is_some() {
        return None;
    }
    let mut env = exact_integer_parameter_env(function, scoping, parameter_bindings)?;
    for (index, parameter) in function.params.items.iter().enumerate() {
        if index < provided_argument_count || parameter_bindings.contains_key(&index) {
            continue;
        }
        let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
            // A missing argument can trigger defaults/destructuring semantics.
            return None;
        };
        env.insert(identifier.name.to_string(), Scalar::Undefined);
    }
    Some(env)
}

fn branch_state_variable_for_span(
    block: &oxc_ast::ast::BlockStatement<'_>,
    target: Span,
) -> Option<(String, u64)> {
    struct Probe {
        target: Span,
        best: Option<(u32, String, u64)>,
    }
    impl Probe {
        fn consider(&mut self, binary: &oxc_ast::ast::BinaryExpression<'_>, span: Span) {
            if !(span.start <= self.target.start && self.target.end <= span.end)
                || !matches!(binary.operator.as_str(), "==" | "===")
            {
                return;
            }
            let pair = if let (Some(name), Some(value)) =
                (expr_ident(&binary.left), numeric_u64(&binary.right))
            {
                Some((name.to_string(), value))
            } else if let (Some(value), Some(name)) =
                (numeric_u64(&binary.left), expr_ident(&binary.right))
            {
                Some((name.to_string(), value))
            } else {
                None
            };
            let Some((name, value)) = pair else {
                return;
            };
            let width = span.end.saturating_sub(span.start);
            if self.best.as_ref().is_none_or(|(best, _, _)| width < *best) {
                self.best = Some((width, name, value));
            }
        }
    }
    impl<'a> Visit<'a> for Probe {
        fn visit_if_statement(&mut self, statement: &oxc_ast::ast::IfStatement<'a>) {
            if let Expression::BinaryExpression(binary) = &statement.test {
                self.consider(binary, statement.consequent.span());
            }
            walk::walk_if_statement(self, statement);
        }
        fn visit_conditional_expression(
            &mut self,
            expression: &oxc_ast::ast::ConditionalExpression<'a>,
        ) {
            if let Expression::BinaryExpression(binary) = &expression.test {
                self.consider(binary, expression.consequent.span());
            }
            walk::walk_conditional_expression(self, expression);
        }
        fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
        }
    }
    let mut probe = Probe { target, best: None };
    probe.visit_block_statement(block);
    probe.best.map(|(_, name, value)| (name, value))
}

fn control_test_is_effect_free(expression: &Expression<'_>) -> bool {
    match expression {
        Expression::NumericLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::StringLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::Identifier(_) => true,
        Expression::ParenthesizedExpression(parenthesized) => {
            control_test_is_effect_free(&parenthesized.expression)
        }
        Expression::SequenceExpression(sequence) => {
            sequence.expressions.iter().all(control_test_is_effect_free)
        }
        Expression::UnaryExpression(unary) if unary.operator.as_str() != "delete" => {
            control_test_is_effect_free(&unary.argument)
        }
        Expression::BinaryExpression(binary) => {
            control_test_is_effect_free(&binary.left) && control_test_is_effect_free(&binary.right)
        }
        Expression::LogicalExpression(logical) => {
            control_test_is_effect_free(&logical.left)
                && control_test_is_effect_free(&logical.right)
        }
        Expression::ConditionalExpression(conditional) => {
            control_test_is_effect_free(&conditional.test)
                && control_test_is_effect_free(&conditional.consequent)
                && control_test_is_effect_free(&conditional.alternate)
        }
        Expression::ArrayExpression(array) => array.elements.iter().all(|element| match element {
            oxc_ast::ast::ArrayExpressionElement::Elision(_) => true,
            oxc_ast::ast::ArrayExpressionElement::SpreadElement(_) => false,
            element => element
                .as_expression()
                .is_some_and(control_test_is_effect_free),
        }),
        _ => false,
    }
}

fn execute_scalar_prefix_to_while(
    statements: &[Statement<'_>],
    source: &str,
    target_while_start: u32,
    env: &mut HashMap<String, Scalar>,
) -> Option<()> {
    for statement in statements {
        if statement.span().start == target_while_start
            && matches!(statement, Statement::WhileStatement(_))
        {
            return Some(());
        }
        if statement.span().start < target_while_start && target_while_start < statement.span().end
        {
            let Statement::BlockStatement(block) = statement else {
                return None;
            };
            return execute_scalar_prefix_to_while(&block.body, source, target_while_start, env);
        }
        if statement.span().end > target_while_start {
            return None;
        }
        let mut semantic = Vec::new();
        let mut ambiguous_envs = Vec::new();
        if exec_statement(
            statement,
            source,
            "",
            env,
            &mut semantic,
            &mut ambiguous_envs,
        ) != ExecStatus::Normal
            || !semantic.is_empty()
        {
            return None;
        }
    }
    None
}

/// Prove an event unreachable inside a protected flattened state loop of the
/// form `while (...) try { if (state == ...) ... } catch (...) { ... }` for a
/// concrete direct call.
///
/// The proof deliberately over-approximates the loop condition: it only needs
/// the condition to be effect-free, then assumes the body may execute. Missing
/// plain formal parameters are exact `undefined` values. Unsupported control,
/// non-terminal ambiguous effects, dynamic scalar state, and recoverable
/// exception paths all fail closed.
#[must_use]
pub fn prove_function_protected_if_ladder_event_unreachable_with_call_arguments(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    function_start: u32,
    function_end: u32,
    event: Span,
    provided_argument_count: usize,
    parameter_bindings: &BTreeMap<usize, i64>,
) -> bool {
    struct Harness<'s, 'b> {
        source: &'s str,
        scoping: &'b Scoping,
        function_start: u32,
        function_end: u32,
        event: Span,
        provided_argument_count: usize,
        parameter_bindings: &'b BTreeMap<usize, i64>,
        result: Option<bool>,
    }

    impl<'a> Visit<'a> for Harness<'_, '_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if self.result.is_some() {
                return;
            }
            if function.span.start != self.function_start || function.span.end != self.function_end
            {
                walk::walk_function(self, function, flags);
                return;
            }
            let Some(body) = function.body.as_deref() else {
                self.result = Some(false);
                return;
            };
            let Some(mut env) = exact_call_parameter_env(
                function,
                self.scoping,
                self.parameter_bindings,
                self.provided_argument_count,
            ) else {
                self.result = Some(false);
                return;
            };

            struct LoopProbe {
                event: Span,
                loops: Vec<Span>,
            }
            impl<'a> Visit<'a> for LoopProbe {
                fn visit_while_statement(&mut self, statement: &WhileStatement<'a>) {
                    if statement.span.start <= self.event.start
                        && self.event.end <= statement.span.end
                    {
                        self.loops.push(statement.span);
                    }
                    walk::walk_while_statement(self, statement);
                }
                fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                fn visit_arrow_function_expression(
                    &mut self,
                    _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                }
            }
            let mut loops = LoopProbe {
                event: self.event,
                loops: Vec::new(),
            };
            loops.visit_function_body(body);
            let [loop_span] = loops.loops.as_slice() else {
                self.result = Some(false);
                return;
            };
            if execute_scalar_prefix_to_while(
                &body.statements,
                self.source,
                loop_span.start,
                &mut env,
            )
            .is_none()
            {
                self.result = Some(false);
                return;
            }

            struct Runner<'s> {
                source: &'s str,
                event: Span,
                target: Span,
                env: HashMap<String, Scalar>,
                result: Option<bool>,
            }
            impl<'a> Visit<'a> for Runner<'_> {
                fn visit_while_statement(&mut self, while_statement: &WhileStatement<'a>) {
                    if self.result.is_some() {
                        return;
                    }
                    if while_statement.span != self.target {
                        walk::walk_while_statement(self, while_statement);
                        return;
                    }
                    if !control_test_is_effect_free(&while_statement.test) {
                        self.result = Some(false);
                        return;
                    }
                    let Statement::TryStatement(try_statement) = &while_statement.body else {
                        self.result = Some(false);
                        return;
                    };
                    let (Some(handler), None) = (&try_statement.handler, &try_statement.finalizer)
                    else {
                        self.result = Some(false);
                        return;
                    };
                    let Some((state_var, event_state)) =
                        branch_state_variable_for_span(&try_statement.block, self.event)
                    else {
                        self.result = Some(false);
                        return;
                    };

                    struct NestedStateReferenceProbe<'s> {
                        state_var: &'s str,
                        nested_depth: usize,
                        found: bool,
                    }
                    impl<'a> Visit<'a> for NestedStateReferenceProbe<'_> {
                        fn visit_identifier_reference(
                            &mut self,
                            identifier: &oxc_ast::ast::IdentifierReference<'a>,
                        ) {
                            if self.nested_depth > 0 && identifier.name.as_str() == self.state_var {
                                self.found = true;
                            }
                        }
                        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
                            self.nested_depth += 1;
                            walk::walk_function(self, function, flags);
                            self.nested_depth -= 1;
                        }
                        fn visit_arrow_function_expression(
                            &mut self,
                            function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                        ) {
                            self.nested_depth += 1;
                            walk::walk_arrow_function_expression(self, function);
                            self.nested_depth -= 1;
                        }
                    }
                    let mut nested_state = NestedStateReferenceProbe {
                        state_var: &state_var,
                        nested_depth: 0,
                        found: false,
                    };
                    nested_state.visit_while_statement(while_statement);
                    if nested_state.found {
                        self.result = Some(false);
                        return;
                    }

                    let mut evidence = IfLadderEvidenceVisitor {
                        state_var: &state_var,
                        evidence: IfLadderEvidence::default(),
                    };
                    evidence.visit_block_statement(&try_statement.block);
                    if evidence.evidence.compared_states.len() < 4
                        || evidence.evidence.state_assignments < 4
                    {
                        self.result = Some(false);
                        return;
                    }

                    for _ in 0..256 {
                        let Some(Scalar::Int(state)) = self.env.get(&state_var).copied() else {
                            self.result = Some(false);
                            return;
                        };
                        if u64::try_from(state).ok() == Some(event_state) {
                            self.result = Some(false);
                            return;
                        }

                        let mut semantic = Vec::new();
                        let mut ambiguous_envs = Vec::new();
                        match exec_statements(
                            &try_statement.block.body,
                            self.source,
                            &state_var,
                            &mut self.env,
                            &mut semantic,
                            &mut ambiguous_envs,
                        ) {
                            ExecStatus::Return | ExecStatus::Break => {
                                self.result = Some(true);
                                return;
                            }
                            ExecStatus::Throw => {
                                let mut catch_semantic = Vec::new();
                                let mut catch_ambiguous_envs = Vec::new();
                                match exec_statements(
                                    &handler.body.body,
                                    self.source,
                                    &state_var,
                                    &mut self.env,
                                    &mut catch_semantic,
                                    &mut catch_ambiguous_envs,
                                ) {
                                    ExecStatus::Return | ExecStatus::Throw | ExecStatus::Break => {
                                        self.result = Some(true);
                                        return;
                                    }
                                    ExecStatus::Normal => {
                                        if !catch_semantic.is_empty() {
                                            self.result = Some(false);
                                            return;
                                        }
                                    }
                                }
                            }
                            ExecStatus::Normal => {
                                for snapshot in ambiguous_envs {
                                    let mut catch_env = snapshot;
                                    let mut catch_semantic = Vec::new();
                                    let mut catch_ambiguous_envs = Vec::new();
                                    let catch_status = exec_statements(
                                        &handler.body.body,
                                        self.source,
                                        &state_var,
                                        &mut catch_env,
                                        &mut catch_semantic,
                                        &mut catch_ambiguous_envs,
                                    );
                                    if !matches!(
                                        catch_status,
                                        ExecStatus::Return | ExecStatus::Throw | ExecStatus::Break
                                    ) {
                                        self.result = Some(false);
                                        return;
                                    }
                                }
                            }
                        }
                    }
                    self.result = Some(false);
                }
                fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                fn visit_arrow_function_expression(
                    &mut self,
                    _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                }
            }

            let mut runner = Runner {
                source: self.source,
                event: self.event,
                target: *loop_span,
                env,
                result: None,
            };
            runner.visit_function_body(body);
            self.result = Some(runner.result.unwrap_or(false));
        }
    }

    let mut harness = Harness {
        source,
        scoping,
        function_start,
        function_end,
        event,
        provided_argument_count,
        parameter_bindings,
        result: None,
    };
    harness.visit_program(program);
    harness.result.unwrap_or(false)
}

/// Prove that an event is excluded by an enclosing exact structured branch
/// (`if`, conditional expression, or the RHS of `&&`/`||`) for exact integer
/// formal-parameter values.
///
/// Only the scalar evaluator's side-effect-free subset participates. Unknown
/// tests, targets not contained by a recognized branch, and dynamic scalar
/// bindings fail closed.
#[must_use]
pub fn prove_function_structured_branch_event_unreachable_with_integer_parameters(
    program: &Program<'_>,
    scoping: &Scoping,
    function_start: u32,
    function_end: u32,
    event: Span,
    parameter_bindings: &BTreeMap<usize, i64>,
) -> bool {
    struct FunctionHarness<'b> {
        scoping: &'b Scoping,
        function_start: u32,
        function_end: u32,
        event: Span,
        parameter_bindings: &'b BTreeMap<usize, i64>,
        result: Option<bool>,
    }

    impl<'a> Visit<'a> for FunctionHarness<'_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if self.result.is_some() {
                return;
            }
            if function.span.start != self.function_start || function.span.end != self.function_end
            {
                walk::walk_function(self, function, flags);
                return;
            }
            let Some(env) =
                exact_integer_parameter_env(function, self.scoping, self.parameter_bindings)
            else {
                self.result = Some(false);
                return;
            };
            let Some(body) = function.body.as_deref() else {
                self.result = Some(false);
                return;
            };

            struct BranchProbe<'e> {
                env: &'e HashMap<String, Scalar>,
                event: Span,
                excluded: bool,
            }
            impl BranchProbe<'_> {
                fn contains(span: Span, event: Span) -> bool {
                    span.start <= event.start && event.end <= span.end
                }
            }
            impl<'a> Visit<'a> for BranchProbe<'_> {
                fn visit_if_statement(&mut self, statement: &oxc_ast::ast::IfStatement<'a>) {
                    if self.excluded {
                        return;
                    }
                    let in_consequent = Self::contains(statement.consequent.span(), self.event);
                    let in_alternate = statement
                        .alternate
                        .as_ref()
                        .is_some_and(|alternate| Self::contains(alternate.span(), self.event));
                    if in_consequent || in_alternate {
                        if let Some(test) = eval_expr(&statement.test, self.env) {
                            if (in_consequent && !test.truthy()) || (in_alternate && test.truthy())
                            {
                                self.excluded = true;
                                return;
                            }
                        }
                    }
                    walk::walk_if_statement(self, statement);
                }

                fn visit_conditional_expression(
                    &mut self,
                    expression: &oxc_ast::ast::ConditionalExpression<'a>,
                ) {
                    if self.excluded {
                        return;
                    }
                    let in_consequent = Self::contains(expression.consequent.span(), self.event);
                    let in_alternate = Self::contains(expression.alternate.span(), self.event);
                    if in_consequent || in_alternate {
                        if let Some(test) = eval_expr(&expression.test, self.env) {
                            if (in_consequent && !test.truthy()) || (in_alternate && test.truthy())
                            {
                                self.excluded = true;
                                return;
                            }
                        }
                    }
                    walk::walk_conditional_expression(self, expression);
                }

                fn visit_logical_expression(
                    &mut self,
                    expression: &oxc_ast::ast::LogicalExpression<'a>,
                ) {
                    if self.excluded {
                        return;
                    }
                    if Self::contains(expression.right.span(), self.event) {
                        if let Some(lhs) = eval_expr(&expression.left, self.env) {
                            let skips_right = match expression.operator.as_str() {
                                "&&" => !lhs.truthy(),
                                "||" => lhs.truthy(),
                                _ => false,
                            };
                            if skips_right {
                                self.excluded = true;
                                return;
                            }
                        }
                    }
                    walk::walk_logical_expression(self, expression);
                }

                fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                fn visit_arrow_function_expression(
                    &mut self,
                    _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                }
            }

            let mut probe = BranchProbe {
                env: &env,
                event: self.event,
                excluded: false,
            };
            probe.visit_function_body(body);
            self.result = Some(probe.excluded);
        }
    }

    let mut harness = FunctionHarness {
        scoping,
        function_start,
        function_end,
        event,
        parameter_bindings,
        result: None,
    };
    harness.visit_program(program);
    harness.result.unwrap_or(false)
}

/// Prove that an event inside a structured `switch` cannot execute for exact
/// integer formal-parameter values. The proof accepts only scalar-pure case
/// selection and a selected case that either lies after the target or ends in
/// an unconditional top-level break/return/throw before any later target case.
#[must_use]
pub fn prove_function_switch_event_unreachable_with_integer_parameters(
    program: &Program<'_>,
    scoping: &Scoping,
    function_start: u32,
    function_end: u32,
    event: Span,
    parameter_bindings: &BTreeMap<usize, i64>,
) -> bool {
    struct FunctionHarness<'b> {
        scoping: &'b Scoping,
        function_start: u32,
        function_end: u32,
        event: Span,
        parameter_bindings: &'b BTreeMap<usize, i64>,
        result: Option<bool>,
    }

    impl<'a> Visit<'a> for FunctionHarness<'_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if self.result.is_some() {
                return;
            }
            if function.span.start != self.function_start || function.span.end != self.function_end
            {
                walk::walk_function(self, function, flags);
                return;
            }
            let Some(env) =
                exact_integer_parameter_env(function, self.scoping, self.parameter_bindings)
            else {
                self.result = Some(false);
                return;
            };
            let Some(body) = function.body.as_deref() else {
                self.result = Some(false);
                return;
            };

            struct SwitchProbe<'e> {
                env: &'e HashMap<String, Scalar>,
                event: Span,
                proofs: Vec<bool>,
            }
            impl<'a> Visit<'a> for SwitchProbe<'_> {
                fn visit_switch_statement(&mut self, switch: &SwitchStatement<'a>) {
                    if !(switch.span.start <= self.event.start && self.event.end <= switch.span.end)
                    {
                        walk::walk_switch_statement(self, switch);
                        return;
                    }
                    let target = switch.cases.iter().position(|case| {
                        case.span.start <= self.event.start && self.event.end <= case.span.end
                    });
                    let Some(target) = target else {
                        walk::walk_switch_statement(self, switch);
                        return;
                    };
                    let Some(discriminant) = eval_expr(&switch.discriminant, self.env) else {
                        self.proofs.push(false);
                        return;
                    };
                    let mut default = None;
                    let mut selected = None;
                    for (index, case) in switch.cases.iter().enumerate() {
                        let Some(test) = case.test.as_ref() else {
                            default = Some(index);
                            continue;
                        };
                        let Some(value) = eval_expr(test, self.env) else {
                            self.proofs.push(false);
                            return;
                        };
                        if value == discriminant {
                            selected = Some(index);
                            break;
                        }
                    }
                    let selected = selected.or(default);
                    let proof = match selected {
                        None => true,
                        Some(selected) if selected > target => true,
                        Some(selected) if selected == target => false,
                        Some(selected) => {
                            switch.cases[selected]
                                .consequent
                                .last()
                                .is_some_and(|statement| {
                                    matches!(
                                        statement,
                                        Statement::BreakStatement(_)
                                            | Statement::ReturnStatement(_)
                                            | Statement::ThrowStatement(_)
                                    )
                                })
                        }
                    };
                    self.proofs.push(proof);
                }
                fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                fn visit_arrow_function_expression(
                    &mut self,
                    _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                }
            }
            let mut probe = SwitchProbe {
                env: &env,
                event: self.event,
                proofs: Vec::new(),
            };
            probe.visit_function_body(body);
            self.result = Some(probe.proofs.into_iter().any(|proof| proof));
        }
    }

    let mut harness = FunctionHarness {
        scoping,
        function_start,
        function_end,
        event,
        parameter_bindings,
        result: None,
    };
    harness.visit_program(program);
    harness.result.unwrap_or(false)
}

pub fn prove_function_if_ladder_event_unreachable_with_integer_parameters(
    source: &str,
    program: &Program<'_>,
    scoping: &Scoping,
    function_start: u32,
    function_end: u32,
    event: Span,
    parameter_bindings: &BTreeMap<usize, i64>,
) -> bool {
    struct FunctionHarness<'s, 'b> {
        source: &'s str,
        function_start: u32,
        function_end: u32,
        event: Span,
        parameter_bindings: &'b BTreeMap<usize, i64>,
        scoping: &'b Scoping,
        result: Option<bool>,
    }

    impl<'a> Visit<'a> for FunctionHarness<'_, '_> {
        fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
            if self.result.is_some() {
                return;
            }
            if function.span.start != self.function_start || function.span.end != self.function_end
            {
                walk::walk_function(self, function, flags);
                return;
            }
            let Some(body) = function.body.as_deref() else {
                self.result = Some(false);
                return;
            };
            let mut bindings = BTreeMap::new();
            for (index, value) in self.parameter_bindings {
                let Some(parameter) = function.params.items.get(*index) else {
                    self.result = Some(false);
                    return;
                };
                let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                    self.result = Some(false);
                    return;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    self.result = Some(false);
                    return;
                };
                if self
                    .scoping
                    .get_resolved_reference_ids(symbol)
                    .iter()
                    .any(|reference_id| self.scoping.get_reference(*reference_id).is_write())
                {
                    self.result = Some(false);
                    return;
                }
                bindings.insert(identifier.name.to_string(), *value);
            }

            #[derive(Default)]
            struct ScalarControlSafetyProbe<'n> {
                state_var: &'n str,
                dynamic_scope: bool,
                arguments_object: bool,
                nested_state_reference: bool,
                nested_depth: usize,
            }
            impl<'a> Visit<'a> for ScalarControlSafetyProbe<'_> {
                fn visit_with_statement(&mut self, _statement: &oxc_ast::ast::WithStatement<'a>) {
                    self.dynamic_scope = true;
                }
                fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
                    if matches!(&call.callee, Expression::Identifier(id) if id.name.as_str() == "eval")
                    {
                        self.dynamic_scope = true;
                    }
                    walk::walk_call_expression(self, call);
                }
                fn visit_identifier_reference(
                    &mut self,
                    identifier: &oxc_ast::ast::IdentifierReference<'a>,
                ) {
                    if identifier.name.as_str() == "arguments" && self.nested_depth == 0 {
                        self.arguments_object = true;
                    }
                    if identifier.name.as_str() == self.state_var && self.nested_depth > 0 {
                        self.nested_state_reference = true;
                    }
                }
                fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
                    self.nested_depth += 1;
                    walk::walk_function(self, function, flags);
                    self.nested_depth -= 1;
                }
                fn visit_arrow_function_expression(
                    &mut self,
                    function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                    self.nested_depth += 1;
                    walk::walk_arrow_function_expression(self, function);
                    self.nested_depth -= 1;
                }
            }
            // Unknown calls may mutate arbitrary objects or throw, but they
            // cannot rewrite these lexical scalar controls unless the function
            // itself opens one of the dynamic/aliasing routes below.
            struct StateVarCollector<'s> {
                source: &'s str,
                event: Span,
                vars: Vec<String>,
            }
            impl<'a> Visit<'a> for StateVarCollector<'_> {
                fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
                    let detected = detect_for_state_machines(self.source, "bound-call", statement);
                    self.vars.extend(
                        detected
                            .if_ladder_machines
                            .into_iter()
                            .filter(|machine| {
                                machine.start <= self.event.start && self.event.end <= machine.end
                            })
                            .map(|machine| machine.state_var),
                    );
                    walk::walk_for_statement(self, statement);
                }
                fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                fn visit_arrow_function_expression(
                    &mut self,
                    _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                }
            }
            let mut state_vars = StateVarCollector {
                source: self.source,
                event: self.event,
                vars: Vec::new(),
            };
            state_vars.visit_function_body(body);
            let [state_var] = state_vars.vars.as_slice() else {
                self.result = Some(false);
                return;
            };
            let state_var = state_var.clone();
            let mut safety = ScalarControlSafetyProbe {
                state_var: &state_var,
                ..ScalarControlSafetyProbe::default()
            };
            safety.visit_function_body(body);
            if safety.dynamic_scope || safety.arguments_object || safety.nested_state_reference {
                self.result = Some(false);
                return;
            }

            struct MachineCollector<'s, 'b> {
                source: &'s str,
                event: Span,
                bindings: &'b BTreeMap<String, i64>,
                matches: usize,
                result: bool,
            }
            impl<'a> Visit<'a> for MachineCollector<'_, '_> {
                fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
                    let detected = detect_for_state_machines(self.source, "bound-call", statement);
                    for machine in detected.if_ladder_machines {
                        if machine.start <= self.event.start && self.event.end <= machine.end {
                            self.matches += 1;
                            self.result = prove_machine_event_unreachable_with_integer_bindings(
                                &machine,
                                &statement.body,
                                self.event,
                                self.bindings,
                            );
                        }
                    }
                    walk::walk_for_statement(self, statement);
                }
                fn visit_function(&mut self, _function: &Function<'a>, _flags: ScopeFlags) {}
                fn visit_arrow_function_expression(
                    &mut self,
                    _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
                ) {
                }
            }
            let mut collector = MachineCollector {
                source: self.source,
                event: self.event,
                bindings: &bindings,
                matches: 0,
                result: false,
            };
            collector.visit_function_body(body);
            self.result = Some(collector.matches == 1 && collector.result);
        }
    }

    let mut harness = FunctionHarness {
        source,
        function_start,
        function_end,
        event,
        parameter_bindings,
        scoping,
        result: None,
    };
    harness.visit_program(program);
    harness.result.unwrap_or(false)
}

pub fn prove_detected_if_ladder_event_before_barriers(
    program: &Program<'_>,
    machine: &IfLadderStateMachineCandidate,
    event: Span,
    barriers: &[Span],
) -> bool {
    struct Harness<'m, 'b> {
        machine: &'m IfLadderStateMachineCandidate,
        event: Span,
        barriers: &'b [Span],
        result: Option<bool>,
    }

    impl<'a> Visit<'a> for Harness<'_, '_> {
        fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
            if self.result.is_some() {
                return;
            }
            if statement.span.start == self.machine.start && statement.span.end == self.machine.end
            {
                self.result = Some(prove_machine_event_before_barriers(
                    self.machine,
                    &statement.body,
                    self.event,
                    self.barriers,
                ));
                return;
            }
            walk::walk_for_statement(self, statement);
        }

        fn visit_while_statement(&mut self, statement: &WhileStatement<'a>) {
            if self.result.is_some() {
                return;
            }
            if statement.span.start == self.machine.start && statement.span.end == self.machine.end
            {
                self.result = Some(prove_machine_event_before_barriers(
                    self.machine,
                    &statement.body,
                    self.event,
                    self.barriers,
                ));
                return;
            }
            walk::walk_while_statement(self, statement);
        }
    }

    let mut harness = Harness {
        machine,
        event,
        barriers,
        result: None,
    };
    harness.visit_program(program);
    harness.result.unwrap_or(false)
}

pub fn prove_if_ladder_event_before_barriers(
    source: &str,
    for_stmt: &ForStatement<'_>,
    event: Span,
    barriers: &[Span],
) -> bool {
    let detected = detect_for_state_machines(source, "pre-escape-proof", for_stmt);
    let [machine] = detected.if_ladder_machines.as_slice() else {
        return false;
    };
    prove_machine_event_before_barriers(machine, &for_stmt.body, event, barriers)
}

pub fn prove_while_if_ladder_event_before_barriers(
    source: &str,
    init_statement: &Statement<'_>,
    while_statement: &WhileStatement<'_>,
    event: Span,
    barriers: &[Span],
) -> bool {
    let Some(machine) =
        detect_while_state_machine(source, "pre-escape-proof", init_statement, while_statement)
    else {
        return false;
    };
    prove_machine_event_before_barriers(&machine, &while_statement.body, event, barriers)
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
                if static_u64(&assign.right).is_some() {
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

fn detect_if_ladder_candidate(
    source: &str,
    function_id: &str,
    start: u32,
    end: u32,
    body: &Statement<'_>,
    state_var: String,
    init_state: u64,
    exit_state: u64,
) -> Option<IfLadderStateMachineCandidate> {
    let mut visitor = IfLadderEvidenceVisitor {
        state_var: &state_var,
        evidence: IfLadderEvidence::default(),
    };
    visitor.visit_statement(body);
    let evidence = visitor.evidence;
    if evidence.compared_states.len() < 4 || evidence.state_assignments < 4 {
        return None;
    }
    let mut transitions = collect_branch_ladder_transitions(source, body, &state_var);
    transitions.sort_by(|a, b| {
        (a.from_state, a.assignment_start, a.assignment_end).cmp(&(
            b.from_state,
            b.assignment_start,
            b.assignment_end,
        ))
    });
    transitions.dedup();
    Some(IfLadderStateMachineCandidate {
        function_id: function_id.to_string(),
        start,
        end,
        state_var,
        init_state,
        exit_state,
        compared_states: evidence.compared_states.into_iter().collect(),
        state_assignments: evidence.state_assignments,
        constant_state_assignments: evidence.constant_state_assignments,
        dynamic_state_assignments: evidence.dynamic_state_assignments,
        transitions,
        preview: preview(source, start, end, 180),
    })
}

#[must_use]
pub fn detect_while_state_machine(
    source: &str,
    function_id: &str,
    init_statement: &Statement<'_>,
    while_statement: &WhileStatement<'_>,
) -> Option<IfLadderStateMachineCandidate> {
    let (state_var, exit_state) = state_exit(&while_statement.test)?;
    let init_state = statement_state_init(init_statement, &state_var)?;
    detect_if_ladder_candidate(
        source,
        function_id,
        while_statement.span.start,
        while_statement.span.end,
        &while_statement.body,
        state_var,
        init_state,
        exit_state,
    )
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
            if let Some(machine) = detect_if_ladder_candidate(
                source,
                function_id,
                for_stmt.span.start,
                for_stmt.span.end,
                &for_stmt.body,
                state_var,
                init_state,
                exit_state,
            ) {
                detected.if_ladder_machines.push(machine);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
        Expression::NumericLiteral(n) => exact_i64(n.value).map(Scalar::Int),
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
                "~" => Some(Scalar::Int(i64::from(!js_int32_from_i64(v.int()?)))),
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
                "&" | "|" | "^" | "<<" | ">>" | ">>>" => {
                    eval_js_bitwise_i64(op, lhs.int()?, rhs.int()?).map(Scalar::Int)
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

fn expression_definitely_throws(expr: &Expression<'_>, env: &HashMap<String, Scalar>) -> bool {
    match expr {
        Expression::ParenthesizedExpression(parenthesized) => {
            expression_definitely_throws(&parenthesized.expression, env)
        }
        Expression::SequenceExpression(sequence) => sequence
            .expressions
            .iter()
            .any(|expression| expression_definitely_throws(expression, env)),
        Expression::StaticMemberExpression(member) => {
            expression_definitely_throws(&member.object, env)
                || matches!(eval_expr(&member.object, env), Some(Scalar::Undefined))
        }
        Expression::ComputedMemberExpression(member) => {
            expression_definitely_throws(&member.object, env)
                || matches!(eval_expr(&member.object, env), Some(Scalar::Undefined))
                || expression_definitely_throws(&member.expression, env)
        }
        Expression::UnaryExpression(unary) => expression_definitely_throws(&unary.argument, env),
        Expression::BinaryExpression(binary) => {
            expression_definitely_throws(&binary.left, env)
                || expression_definitely_throws(&binary.right, env)
        }
        Expression::LogicalExpression(logical) => {
            if expression_definitely_throws(&logical.left, env) {
                return true;
            }
            let Some(lhs) = eval_expr(&logical.left, env) else {
                return false;
            };
            match logical.operator.as_str() {
                "&&" if lhs.truthy() => expression_definitely_throws(&logical.right, env),
                "||" if !lhs.truthy() => expression_definitely_throws(&logical.right, env),
                "&&" | "||" => false,
                _ => false,
            }
        }
        Expression::ConditionalExpression(conditional) => {
            if expression_definitely_throws(&conditional.test, env) {
                return true;
            }
            let Some(test) = eval_expr(&conditional.test, env) else {
                return false;
            };
            if test.truthy() {
                expression_definitely_throws(&conditional.consequent, env)
            } else {
                expression_definitely_throws(&conditional.alternate, env)
            }
        }
        Expression::AssignmentExpression(assignment) => {
            expression_definitely_throws(&assignment.right, env)
        }
        Expression::CallExpression(call) => {
            expression_definitely_throws(&call.callee, env)
                || call
                    .arguments
                    .iter()
                    .filter_map(Argument::as_expression)
                    .any(|argument| expression_definitely_throws(argument, env))
        }
        _ => false,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExecStatus {
    Normal,
    Break,
    Return,
    Throw,
}

fn record_ambiguous_effect(
    source: &str,
    span: Span,
    env: &HashMap<String, Scalar>,
    semantic: &mut Vec<String>,
    ambiguous_envs: &mut Vec<HashMap<String, Scalar>>,
) {
    ambiguous_envs.push(env.clone());
    semantic.push(slice(source, span));
}

fn exec_control_expr(
    expr: &Expression<'_>,
    source: &str,
    state_var: &str,
    env: &mut HashMap<String, Scalar>,
    semantic: &mut Vec<String>,
    ambiguous_envs: &mut Vec<HashMap<String, Scalar>>,
) -> ExecStatus {
    match expr {
        Expression::ParenthesizedExpression(parenthesized) => exec_control_expr(
            &parenthesized.expression,
            source,
            state_var,
            env,
            semantic,
            ambiguous_envs,
        ),
        Expression::SequenceExpression(sequence) => {
            for expression in &sequence.expressions {
                let status =
                    exec_control_expr(expression, source, state_var, env, semantic, ambiguous_envs);
                if status != ExecStatus::Normal {
                    return status;
                }
            }
            ExecStatus::Normal
        }
        Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
            if let Some(target) = assignment.left.get_identifier_name() {
                if let Some(value) = eval_expr(&assignment.right, env) {
                    env.insert(target.to_string(), value);
                } else if expression_definitely_throws(&assignment.right, env) {
                    return ExecStatus::Throw;
                } else {
                    record_ambiguous_effect(source, assignment.span, env, semantic, ambiguous_envs);
                    env.remove(target);
                }
                ExecStatus::Normal
            } else if expression_definitely_throws(&assignment.right, env) {
                ExecStatus::Throw
            } else {
                record_ambiguous_effect(source, assignment.span, env, semantic, ambiguous_envs);
                ExecStatus::Normal
            }
        }
        Expression::ConditionalExpression(conditional) => {
            if expression_definitely_throws(&conditional.test, env) {
                return ExecStatus::Throw;
            }
            if let Some(test) = eval_expr(&conditional.test, env) {
                let branch = if test.truthy() {
                    &conditional.consequent
                } else {
                    &conditional.alternate
                };
                exec_control_expr(branch, source, state_var, env, semantic, ambiguous_envs)
            } else {
                record_ambiguous_effect(source, conditional.span, env, semantic, ambiguous_envs);
                ExecStatus::Normal
            }
        }
        Expression::LogicalExpression(logical) => {
            if expression_definitely_throws(&logical.left, env) {
                return ExecStatus::Throw;
            }
            if let Some(lhs) = eval_expr(&logical.left, env) {
                match logical.operator.as_str() {
                    "&&" if lhs.truthy() => exec_control_expr(
                        &logical.right,
                        source,
                        state_var,
                        env,
                        semantic,
                        ambiguous_envs,
                    ),
                    "||" if !lhs.truthy() => exec_control_expr(
                        &logical.right,
                        source,
                        state_var,
                        env,
                        semantic,
                        ambiguous_envs,
                    ),
                    "&&" | "||" => ExecStatus::Normal,
                    _ => {
                        record_ambiguous_effect(
                            source,
                            logical.span,
                            env,
                            semantic,
                            ambiguous_envs,
                        );
                        ExecStatus::Normal
                    }
                }
            } else {
                record_ambiguous_effect(source, logical.span, env, semantic, ambiguous_envs);
                ExecStatus::Normal
            }
        }
        _ if expression_definitely_throws(expr, env) => ExecStatus::Throw,
        _ => {
            record_ambiguous_effect(source, expr.span(), env, semantic, ambiguous_envs);
            ExecStatus::Normal
        }
    }
}

fn exec_statements(
    statements: &[Statement<'_>],
    source: &str,
    state_var: &str,
    env: &mut HashMap<String, Scalar>,
    semantic: &mut Vec<String>,
    ambiguous_envs: &mut Vec<HashMap<String, Scalar>>,
) -> ExecStatus {
    for stmt in statements {
        let status = exec_statement(stmt, source, state_var, env, semantic, ambiguous_envs);
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
    ambiguous_envs: &mut Vec<HashMap<String, Scalar>>,
) -> ExecStatus {
    exec_statements(
        &body.statements,
        source,
        state_var,
        env,
        semantic,
        ambiguous_envs,
    )
}

fn expression_function_body<'a>(expr: &'a Expression<'a>) -> Option<&'a FunctionBody<'a>> {
    match expr {
        Expression::FunctionExpression(fun) => fun.body.as_deref(),
        Expression::ArrowFunctionExpression(fun) => match &fun.body {
            oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => Some(&**body),
            _ => None,
        },
        Expression::ParenthesizedExpression(paren) => expression_function_body(&paren.expression),
        _ => None,
    }
}

fn argument_function_body<'a>(arg: &'a Argument<'a>) -> Option<&'a FunctionBody<'a>> {
    match arg {
        Argument::FunctionExpression(fun) => fun.body.as_deref(),
        Argument::ArrowFunctionExpression(fun) => match &fun.body {
            oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => Some(&**body),
            _ => None,
        },
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
    ambiguous_envs: &mut Vec<HashMap<String, Scalar>>,
) -> ExecStatus {
    match stmt {
        Statement::BlockStatement(b) => {
            exec_statements(&b.body, source, state_var, env, semantic, ambiguous_envs)
        }
        Statement::ExpressionStatement(e) => {
            if let Expression::CallExpression(call) = &e.expression {
                if let Some(body) = call.arguments.first().and_then(argument_function_body) {
                    return exec_function_body(
                        body,
                        source,
                        state_var,
                        env,
                        semantic,
                        ambiguous_envs,
                    );
                }
            }
            exec_control_expr(
                &e.expression,
                source,
                state_var,
                env,
                semantic,
                ambiguous_envs,
            )
        }
        Statement::IfStatement(i) => {
            if expression_definitely_throws(&i.test, env) {
                return ExecStatus::Throw;
            }
            let Some(test) = eval_expr(&i.test, env) else {
                record_ambiguous_effect(source, i.span, env, semantic, ambiguous_envs);
                return ExecStatus::Normal;
            };
            if test.truthy() {
                exec_statement(
                    &i.consequent,
                    source,
                    state_var,
                    env,
                    semantic,
                    ambiguous_envs,
                )
            } else if let Some(alt) = &i.alternate {
                exec_statement(alt, source, state_var, env, semantic, ambiguous_envs)
            } else {
                ExecStatus::Normal
            }
        }
        Statement::TryStatement(t) => {
            record_ambiguous_effect(source, t.span, env, semantic, ambiguous_envs);
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
            record_ambiguous_effect(source, stmt.span(), env, semantic, ambiguous_envs);
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
        let Some(mut env) = self
            .bindings
            .iter()
            .map(|(name, mask)| {
                i64::try_from(opcode & mask)
                    .ok()
                    .map(|value| (name.clone(), Scalar::Int(value)))
            })
            .collect::<Option<HashMap<_, _>>>()
        else {
            return OpcodeHandler {
                opcode,
                observed: observed_opcodes.contains(&opcode),
                path: Vec::new(),
                terminal: "integer-overflow".to_string(),
                semantic: Vec::new(),
            };
        };
        let mut state = self.machine.init_state;
        let mut path = Vec::new();
        let mut semantic = Vec::new();
        let mut terminal = "step-limit".to_string();

        for _ in 0..128 {
            path.push(state);
            let Ok(state_i64) = i64::try_from(state) else {
                terminal = "integer-overflow".to_string();
                break;
            };
            env.insert(self.machine.state_var.clone(), Scalar::Int(state_i64));

            if let (Some(shift), Some(selector)) =
                (self.machine.shift, self.machine.selector_var.as_ref())
            {
                let selected = (state >> shift) & self.machine.mask;
                let Ok(selected) = i64::try_from(selected) else {
                    terminal = "integer-overflow".to_string();
                    break;
                };
                env.insert(selector.clone(), Scalar::Int(selected));
            }

            let low = state & self.machine.mask;
            let Some(statements) = case_map.get(&low) else {
                terminal = format!("missing-case-{low}");
                break;
            };
            let mut ambiguous_envs = Vec::new();
            match exec_statements(
                statements,
                self.source,
                &self.machine.state_var,
                &mut env,
                &mut semantic,
                &mut ambiguous_envs,
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
                    let Ok(next) = u64::try_from(next) else {
                        terminal = "integer-overflow".to_string();
                        break;
                    };
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

    fn eval_integer_expression(source: &str) -> Option<i64> {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        if !parsed.is_clean() {
            return None;
        }
        let Statement::ExpressionStatement(statement) = parsed.program.body.first()? else {
            return None;
        };
        let Scalar::Int(value) = eval_expr(&statement.expression, &HashMap::new())? else {
            return None;
        };
        Some(value)
    }

    #[test]
    fn evaluator_uses_javascript_32_bit_bitwise_semantics() {
        assert_eq!(eval_integer_expression("-1 >>> 0;"), Some(4_294_967_295));
        assert_eq!(
            eval_integer_expression("0x80000000 >> 0;"),
            Some(-2_147_483_648)
        );
        assert_eq!(eval_integer_expression("1 << 33;"), Some(2));
        assert_eq!(
            eval_integer_expression("0xffffffff & 0x80000000;"),
            Some(-2_147_483_648)
        );
        assert_eq!(eval_integer_expression("~0;"), Some(-1));
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
    fn detects_assignment_initialized_if_ladder_and_lifts_transitions() {
        let detected = detect(
            r"
            function flattened(input) {
                let state;
                for (state = 4; state !== 90;) {
                    if (state === 4) { state = 1 + 6; }
                    else if (state === 7) { state = input ? 12 : 13; }
                    else if (state === 12) { state = 20; }
                    else if (state === 13) { state = 20; }
                    else if (state === 20) { state = 90; }
                }
            }
            ",
        );

        assert_eq!(detected.if_ladder_machines.len(), 1);
        let machine = &detected.if_ladder_machines[0];
        assert_eq!(machine.state_var, "state");
        assert_eq!(machine.init_state, 4);
        assert_eq!(machine.exit_state, 90);
        assert_eq!(machine.constant_state_assignments, 4);
        assert_eq!(machine.dynamic_state_assignments, 1);
        assert!(machine.transitions.iter().any(|transition| {
            transition.from_state == 4 && transition.target_state == Some(7)
        }));
        assert!(machine.transitions.iter().any(|transition| {
            transition.from_state == 7
                && transition.target_state.is_none()
                && transition.possible_target_states == vec![12, 13]
                && transition.target_expression.contains("input ? 12 : 13")
        }));
        assert!(machine.transitions.iter().any(|transition| {
            transition.from_state == 20 && transition.target_state == Some(90)
        }));
    }

    #[test]
    fn lifts_nested_conditional_expression_ladder_transitions() {
        let detected = detect(
            r"
            function flattened(input) {
                let state;
                for (state = 4; state !== 90;)
                    state === 4 ? state = input ? 7 : 8
                    : state === 7 ? state = 20
                    : state === 8 ? state = 20
                    : state === 20 ? state = 90
                    : state = 90;
            }
            ",
        );
        assert_eq!(detected.if_ladder_machines.len(), 1);
        let machine = &detected.if_ladder_machines[0];
        assert!(machine.transitions.iter().any(|transition| {
            transition.from_state == 4 && transition.possible_target_states == vec![7, 8]
        }));
        assert!(machine.transitions.iter().any(|transition| {
            transition.from_state == 7 && transition.target_state == Some(20)
        }));
        assert!(machine.transitions.iter().any(|transition| {
            transition.from_state == 20 && transition.target_state == Some(90)
        }));
    }

    #[test]
    fn detects_sequence_initialized_state_machine_using_last_numeric_assignment() {
        let detected = detect(
            r"
            function flattened() {
                let noise, state;
                for (noise = call(), state = 3; state != 8;) {
                    if (state == 3) state = 4;
                    else if (state == 4) state = 5;
                    else if (state == 5) state = 6;
                    else if (state == 6) state = 8;
                }
            }
            ",
        );
        assert_eq!(detected.if_ladder_machines.len(), 1);
        assert_eq!(detected.if_ladder_machines[0].init_state, 3);
    }

    fn prove_order(source: &str, event_text: &str, barrier_texts: &[&str]) -> bool {
        struct Harness<'s> {
            source: &'s str,
            event: Span,
            barriers: Vec<Span>,
            result: Option<bool>,
        }
        impl<'a> Visit<'a> for Harness<'_> {
            fn visit_for_statement(&mut self, statement: &ForStatement<'a>) {
                if statement.span.start <= self.event.start && self.event.end <= statement.span.end
                {
                    self.result = Some(prove_if_ladder_event_before_barriers(
                        self.source,
                        statement,
                        self.event,
                        &self.barriers,
                    ));
                    return;
                }
                walk::walk_for_statement(self, statement);
            }
        }

        let event_start = source.find(event_text).expect("event text") as u32;
        let event = Span::new(event_start, event_start + event_text.len() as u32);
        let barriers = barrier_texts
            .iter()
            .map(|text| {
                let start = source.find(text).expect("barrier text") as u32;
                Span::new(start, start + text.len() as u32)
            })
            .collect();
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let mut harness = Harness {
            source,
            event,
            barriers,
            result: None,
        };
        harness.visit_program(&parsed.program);
        harness.result.unwrap_or(false)
    }

    #[test]
    fn proves_if_ladder_event_before_later_barrier_state() {
        let source = r#"
            function flattened() {
                for (let state = 0; state !== 99;) {
                    if (state === 0) { state = 1; }
                    else if (state === 1) { target(); state = 2; }
                    else if (state === 2) { barrier(); state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(prove_order(source, "target()", &["barrier()"]))
    }

    #[test]
    fn rejects_if_ladder_barrier_on_path_before_event() {
        let source = r#"
            function flattened() {
                for (let state = 0; state !== 99;) {
                    if (state === 0) { barrier(); state = 1; }
                    else if (state === 1) { target(); state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(!prove_order(source, "target()", &["barrier()"]))
    }

    #[test]
    fn orders_barriers_within_target_state() {
        let before = r#"
            function flattened() {
                for (let state = 0; state !== 99;) {
                    if (state === 0) { barrier(); target(); state = 99; }
                    else if (state === 1) { state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(!prove_order(before, "target()", &["barrier()"]));

        let after = before.replace("barrier(); target();", "target(); barrier();");
        assert!(prove_order(&after, "target()", &["barrier()"]));
    }

    #[test]
    fn allows_known_alternate_path_that_exits_without_event() {
        let source = r#"
            function flattened(flag) {
                for (let state = 0; state !== 99;) {
                    if (state === 0) { state = flag ? 1 : 3; }
                    else if (state === 1) { target(); state = 99; }
                    else if (state === 2) { barrier(); state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(prove_order(source, "target()", &["barrier()"]))
    }

    #[test]
    fn rejects_reachable_unresolved_transition_before_event() {
        let source = r#"
            function flattened(next) {
                for (let state = 0; state !== 99;) {
                    if (state === 0) { state = next; }
                    else if (state === 1) { target(); state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(!prove_order(source, "target()", &[]))
    }

    fn prove_while_order(source: &str, event_text: &str, barrier_texts: &[&str]) -> bool {
        struct Harness<'s> {
            source: &'s str,
            event: Span,
            barriers: Vec<Span>,
            result: Option<bool>,
        }
        impl Harness<'_> {
            fn inspect_statements<'a>(&mut self, statements: &[Statement<'a>]) {
                for pair in statements.windows(2) {
                    let [init, Statement::WhileStatement(while_statement)] = pair else {
                        continue;
                    };
                    if while_statement.span.start <= self.event.start
                        && self.event.end <= while_statement.span.end
                    {
                        self.result = Some(prove_while_if_ladder_event_before_barriers(
                            self.source,
                            init,
                            while_statement,
                            self.event,
                            &self.barriers,
                        ));
                        return;
                    }
                }
            }
        }
        impl<'a> Visit<'a> for Harness<'_> {
            fn visit_function_body(&mut self, body: &FunctionBody<'a>) {
                self.inspect_statements(&body.statements);
                if self.result.is_none() {
                    walk::walk_function_body(self, body);
                }
            }

            fn visit_block_statement(&mut self, block: &oxc_ast::ast::BlockStatement<'a>) {
                self.inspect_statements(&block.body);
                if self.result.is_none() {
                    walk::walk_block_statement(self, block);
                }
            }
        }

        let event_start = source.find(event_text).expect("event text") as u32;
        let event = Span::new(event_start, event_start + event_text.len() as u32);
        let barriers = barrier_texts
            .iter()
            .map(|text| {
                let start = source.find(text).expect("barrier text") as u32;
                Span::new(start, start + text.len() as u32)
            })
            .collect();
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let mut harness = Harness {
            source,
            event,
            barriers,
            result: None,
        };
        harness.visit_program(&parsed.program);
        harness.result.unwrap_or(false)
    }

    #[test]
    fn proves_while_if_ladder_event_before_later_same_state_barrier() {
        let source = r#"
            function flattened() {
                let state;
                state = 0;
                while (state !== 99) {
                    if (state === 0) { target(); barrier(); state = 99; }
                    else if (state === 1) { state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(prove_while_order(source, "target()", &["barrier()"]));
    }

    #[test]
    fn proves_order_from_pre_detected_while_machine() {
        let source = r#"
            function flattened() {
                let state = 0;
                while (state !== 99) {
                    if (state === 0) { target(); barrier(); state = 99; }
                    else if (state === 1) { state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        struct Finder<'m> {
            source: &'m str,
            machine: Option<IfLadderStateMachineCandidate>,
        }
        impl<'a> Visit<'a> for Finder<'_> {
            fn visit_function_body(&mut self, body: &FunctionBody<'a>) {
                for pair in body.statements.windows(2) {
                    let [init, Statement::WhileStatement(statement)] = pair else {
                        continue;
                    };
                    if let Some(machine) =
                        detect_while_state_machine(self.source, "test", init, statement)
                    {
                        self.machine = Some(machine);
                        return;
                    }
                }
                walk::walk_function_body(self, body);
            }
        }
        let mut finder = Finder {
            source,
            machine: None,
        };
        finder.visit_program(&parsed.program);
        let machine = finder.machine.expect("machine");
        let event_start = source.find("target()").expect("event") as u32;
        let barrier_start = source.find("barrier()").expect("barrier") as u32;
        assert!(prove_detected_if_ladder_event_before_barriers(
            &parsed.program,
            &machine,
            Span::new(event_start, event_start + 8),
            &[Span::new(barrier_start, barrier_start + 9)],
        ));
    }

    #[test]
    fn proves_selector_specialized_branch_unreachable() {
        let source = r#"function f(Q) {
            for (H = 28; H != 74;) {
                if (H == 55) { sink(); H = 62; }
                else if (H == 56) H = (Q & 62) == Q ? 55 : 62;
                else if (H == 62) H = 12;
                else if (H == 12) H = 41;
                else if (H == 41) H = 89;
                else if (H == 89) return;
                else if (H == 28) H = 56;
            }
        }"#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let mut harness = DetectorHarness::default();
        harness.source = source;
        harness.visit_program(&parsed.program);
        let machine = harness.detected.if_ladder_machines.first().unwrap();
        let start = u32::try_from(source.find("sink()").unwrap()).unwrap();
        let event = Span::new(start, start + 6);
        let safe = BTreeMap::from([("Q".to_string(), 47)]);
        let unsafe_binding = BTreeMap::from([("Q".to_string(), 46)]);
        assert!(
            prove_detected_if_ladder_event_unreachable_with_integer_bindings(
                &parsed.program,
                machine,
                event,
                &safe,
            )
        );
        assert!(
            !prove_detected_if_ladder_event_unreachable_with_integer_bindings(
                &parsed.program,
                machine,
                event,
                &unsafe_binding,
            )
        );
    }

    #[test]
    fn proves_switch_event_unreachable_by_parameter_index() {
        let source = r#"const x = function(J, Q, Y) {
            switch (!(Q == 410 || Q == 387)) {
                case true:
                    J.T[Q] = Y;
                    break;
                case false:
                    sink(Y);
                    break;
            }
        };"#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = oxc_semantic::SemanticBuilder::new().build(&parsed.program);
        struct FunctionSpan {
            span: Option<Span>,
        }
        impl<'a> Visit<'a> for FunctionSpan {
            fn visit_function(&mut self, function: &Function<'a>, _flags: ScopeFlags) {
                self.span = Some(function.span);
            }
        }
        let mut function = FunctionSpan { span: None };
        function.visit_program(&parsed.program);
        let function = function.span.unwrap();
        let start = u32::try_from(source.find("sink(Y)").unwrap()).unwrap();
        let event = Span::new(start, start + 7);
        assert!(
            prove_function_switch_event_unreachable_with_integer_parameters(
                &parsed.program,
                semantic.semantic.scoping(),
                function.start,
                function.end,
                event,
                &BTreeMap::from([(1, 333)]),
            )
        );
        assert!(
            !prove_function_switch_event_unreachable_with_integer_parameters(
                &parsed.program,
                semantic.semantic.scoping(),
                function.start,
                function.end,
                event,
                &BTreeMap::from([(1, 410)]),
            )
        );
    }

    #[test]
    fn proves_structured_short_circuit_event_unreachable() {
        let source = r#"
            const f = function(selector) {
                selector == 449 && target();
            };
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = oxc_semantic::SemanticBuilder::new().build(&parsed.program);
        struct FunctionSpan(Option<Span>);
        impl<'a> Visit<'a> for FunctionSpan {
            fn visit_function(&mut self, function: &Function<'a>, _flags: ScopeFlags) {
                self.0 = Some(function.span);
            }
        }
        let mut function = FunctionSpan(None);
        function.visit_program(&parsed.program);
        let function = function.0.unwrap();
        let start = u32::try_from(source.find("target()").unwrap()).unwrap();
        let event = Span::new(start, start + 8);
        assert!(
            prove_function_structured_branch_event_unreachable_with_integer_parameters(
                &parsed.program,
                semantic.semantic.scoping(),
                function.start,
                function.end,
                event,
                &BTreeMap::from([(0, 410)]),
            )
        );
        assert!(
            !prove_function_structured_branch_event_unreachable_with_integer_parameters(
                &parsed.program,
                semantic.semantic.scoping(),
                function.start,
                function.end,
                event,
                &BTreeMap::from([(0, 449)]),
            )
        );
    }

    #[test]
    fn proves_selector_specialization_by_parameter_index() {
        let source = r#"const g = function(J, Q) {
            for (H = 28; H != 74;) {
                if (H == 55) { sink(J); H = 62; }
                else if (H == 56) H = (Q & 62) == Q ? 55 : 62;
                else if (H == 62) H = 12;
                else if (H == 12) H = 41;
                else if (H == 41) H = 89;
                else if (H == 89) return;
                else if (H == 28) H = 56;
            }
        };"#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = oxc_semantic::SemanticBuilder::new().build(&parsed.program);
        struct FunctionSpan {
            span: Option<Span>,
        }
        impl<'a> Visit<'a> for FunctionSpan {
            fn visit_function(&mut self, function: &Function<'a>, _flags: ScopeFlags) {
                self.span = Some(function.span);
            }
        }
        let mut function = FunctionSpan { span: None };
        function.visit_program(&parsed.program);
        let function = function.span.unwrap();
        let start = u32::try_from(source.find("sink(J)").unwrap()).unwrap();
        let event = Span::new(start, start + 7);
        assert!(
            prove_function_if_ladder_event_unreachable_with_integer_parameters(
                source,
                &parsed.program,
                semantic.semantic.scoping(),
                function.start,
                function.end,
                event,
                &BTreeMap::from([(1, 47)]),
            )
        );
        assert!(
            !prove_function_if_ladder_event_unreachable_with_integer_parameters(
                source,
                &parsed.program,
                semantic.semantic.scoping(),
                function.start,
                function.end,
                event,
                &BTreeMap::from([(1, 46)]),
            )
        );
    }

    fn protected_call_proof(source: &str, provided: usize) -> bool {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        let semantic = oxc_semantic::SemanticBuilder::new().build(&parsed.program);
        struct FunctionSpan {
            span: Option<Span>,
        }
        impl<'a> Visit<'a> for FunctionSpan {
            fn visit_function(&mut self, function: &Function<'a>, _flags: ScopeFlags) {
                self.span = Some(function.span);
            }
        }
        let mut function = FunctionSpan { span: None };
        function.visit_program(&parsed.program);
        let function = function.span.unwrap();
        let start = u32::try_from(source.find("target()").unwrap()).unwrap();
        prove_function_protected_if_ladder_event_unreachable_with_call_arguments(
            source,
            &parsed.program,
            semantic.semantic.scoping(),
            function.start,
            function.end,
            Span::new(start, start + 8),
            provided,
            &BTreeMap::new(),
        )
    }

    #[test]
    fn protected_ladder_proves_omitted_plain_parameter_exception_terminal() {
        let source = r#"
            const y = function(J, Q, Y, L, v, U, H, S, q, R, l, u, r, n) {
                r = 57;
                {
                    u = 46;
                    while (![""] == 0) try {
                        if (r == 57) r = 25;
                        else if (r == 25) r = H.K.length ? 92 : 30;
                        else if (r == 92) u = 92, target(), r = 90;
                        else if (r == 90) u = 46, r = 30;
                        else if (r == 30) return;
                    } catch (m) {
                        if (u == 46) throw m;
                        u == 92 && (n = m, r = 28);
                    }
                }
            };
        "#;
        assert!(protected_call_proof(source, 4));
    }

    #[test]
    fn protected_ladder_fails_closed_for_supplied_unknown_parameter() {
        let source = r#"
            const y = function(J, Q, Y, L, v, U, H, S, q, R, l, u, r, n) {
                r = 57;
                {
                    u = 46;
                    while (true) try {
                        if (r == 57) r = 25;
                        else if (r == 25) r = H.K.length ? 92 : 30;
                        else if (r == 92) u = 92, target(), r = 90;
                        else if (r == 90) u = 46, r = 30;
                        else if (r == 30) return;
                    } catch (m) {
                        if (u == 46) throw m;
                        u == 92 && (n = m, r = 28);
                    }
                }
            };
        "#;
        assert!(!protected_call_proof(source, 7));
    }

    #[test]
    fn protected_ladder_rejects_nested_state_capture() {
        let source = r#"
            const y = function(J, Q, Y, L, v, U, H, S, q, R, l, u, r, n) {
                r = 57;
                while (true) try {
                    if (r == 57) { unknown(function() { r = 92; }); r = 30; }
                    else if (r == 25) r = 30;
                    else if (r == 92) target(), r = 30;
                    else if (r == 90) r = 30;
                    else if (r == 30) return;
                } catch (m) { throw m; }
            };
        "#;
        assert!(!protected_call_proof(source, 4));
    }

    #[test]
    fn protected_ladder_rejects_recoverable_exception_path_to_event() {
        let source = r#"
            const y = function(J, Q, Y, L, v, U, H, S, q, R, l, u, r, n) {
                r = 57;
                {
                    u = 46;
                    while (true) try {
                        if (r == 57) r = 25;
                        else if (r == 25) r = H.K.length ? 92 : 30;
                        else if (r == 92) target(), r = 30;
                        else if (r == 90) r = 30;
                        else if (r == 30) return;
                    } catch (m) {
                        if (u == 46) r = 92;
                    }
                }
            };
        "#;
        assert!(!protected_call_proof(source, 4));
    }

    #[test]
    fn while_detector_matches_condition_state_in_mixed_sequence_init() {
        let source = r#"
            function flattened() {
                let state, noise;
                noise = 7, state = 0, noise = 9;
                while (99 !== state) {
                    if (state === 0) { target(); state = 99; }
                    else if (state === 1) { state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(prove_while_order(source, "target()", &[]));
    }

    #[test]
    fn while_detector_matches_condition_state_in_multi_declarator_init() {
        let source = r#"
            function flattened() {
                let noise = 7, state = 0, tail = 9;
                while (state !== 99) {
                    if (state === 0) { target(); state = 99; }
                    else if (state === 1) { state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(prove_while_order(source, "target()", &[]));
    }

    #[test]
    fn rejects_while_if_ladder_barrier_before_event() {
        let source = r#"
            function flattened() {
                let state;
                state = 0;
                while (state !== 99) {
                    if (state === 0) { barrier(); target(); state = 99; }
                    else if (state === 1) { state = 99; }
                    else if (state === 2) { state = 99; }
                    else if (state === 3) { state = 99; }
                }
            }
        "#;
        assert!(!prove_while_order(source, "target()", &["barrier()"]));
    }

    #[test]
    fn ignores_ordinary_counted_loop() {
        let detected = detect("for (let i = 0; i < 10; i += 1) { work(i); }");
        assert!(detected.switch_machines.is_empty());
        assert!(detected.if_ladder_machines.is_empty());
    }
}
