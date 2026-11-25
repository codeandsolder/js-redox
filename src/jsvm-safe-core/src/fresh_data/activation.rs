//! Local invocation proofs share the ordinary statement/heap interpreter.
//! The call itself remains in the output; only reaching facts cross its exit.
use super::{Analyzer, Environment, Evaluation, Fact, Value};
use oxc_ast::ast::{
    ArrowFunctionBody, ArrowFunctionExpression, BindingPattern, CallExpression, Expression,
    FormalParameters, Function, FunctionBody, FunctionType, Program, Statement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::collections::HashMap;
use work_budget::{BudgetExceeded, WorkBudget};

struct ReturnSummary {
    value: Option<Fact>,
    environment: Environment,
}

/// Every return from this activation contributes to one normal-call exit.
/// Throw paths do not reach the caller's normal continuation.
pub(super) struct ReturnFrame {
    summary: Option<ReturnSummary>,
    unproved: bool,
    disposal_floor: usize,
}

impl ReturnFrame {
    const fn new(disposal_floor: usize) -> Self {
        Self {
            summary: None,
            unproved: false,
            disposal_floor,
        }
    }

    pub(super) const fn empty_like(&self) -> Self {
        Self::new(self.disposal_floor)
    }

    fn record(
        &mut self,
        value: Option<Fact>,
        environment: Environment,
        budget: &WorkBudget,
    ) -> Result<(), BudgetExceeded> {
        budget.consume(1)?;
        if let Some(previous) = &mut self.summary {
            previous.value = match (&previous.value, value) {
                (Some(left), Some(right)) => left.join(&right, budget)?,
                _ => None,
            };
            previous.environment.join_returns(&environment, budget)?;
        } else {
            self.summary = Some(ReturnSummary { value, environment });
        }
        Ok(())
    }

    pub(super) fn merge(&mut self, other: Self, budget: &WorkBudget) -> Result<(), BudgetExceeded> {
        self.unproved |= other.unproved;
        if let Some(summary) = other.summary {
            self.record(summary.value, summary.environment, budget)?;
        }
        Ok(())
    }
}

#[derive(Default)]
struct ReturnProbe(bool);

impl<'a> Visit<'a> for ReturnProbe {
    fn visit_return_statement(&mut self, _: &oxc_ast::ast::ReturnStatement<'a>) {
        self.0 = true;
    }

    fn visit_function(&mut self, _: &Function<'a>, _: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _: &ArrowFunctionExpression<'a>) {}
    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {}
}

/// References to arena-owned declaration nodes, indexed by semantic
/// identity rather than spelling. The binding proof is checked at each call.
#[derive(Clone, Copy)]
enum CallableNode<'a> {
    Ordinary(&'a Function<'a>),
    Arrow(&'a ArrowFunctionExpression<'a>),
}

pub(super) struct CallableIndex<'a> {
    declarations: HashMap<SymbolId, &'a Function<'a>>,
    nodes: HashMap<ScopeId, CallableNode<'a>>,
}

struct CallableCollector<'c, 'a> {
    functions: CallableIndex<'a>,
    budget: &'c WorkBudget,
    failure: Option<BudgetExceeded>,
}

impl<'a> Visit<'a> for CallableCollector<'_, 'a> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if self.failure.is_some() {
            return;
        }
        if let Err(error) = self.budget.consume(1) {
            self.failure = Some(error);
            return;
        }
        let function = self.alloc(function);
        if let Some(scope) = function.scope_id.get() {
            self.functions
                .nodes
                .insert(scope, CallableNode::Ordinary(function));
        }
        if function.r#type == FunctionType::FunctionDeclaration {
            if let Some(symbol) = function.id.as_ref().and_then(|id| id.symbol_id.get()) {
                self.functions.declarations.insert(symbol, function);
            }
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_arrow_function_expression(&mut self, function: &ArrowFunctionExpression<'a>) {
        if self.failure.is_some() {
            return;
        }
        if let Err(error) = self.budget.consume(1) {
            self.failure = Some(error);
            return;
        }
        let function = self.alloc(function);
        if let Some(scope) = function.scope_id.get() {
            self.functions
                .nodes
                .insert(scope, CallableNode::Arrow(function));
        }
        walk::walk_arrow_function_expression(self, function);
    }
}

impl<'a> CallableIndex<'a> {
    pub(super) fn collect(
        program: &Program<'a>,
        budget: &WorkBudget,
    ) -> Result<Self, BudgetExceeded> {
        let mut collector = CallableCollector {
            functions: Self {
                declarations: HashMap::new(),
                nodes: HashMap::new(),
            },
            budget,
            failure: None,
        };
        collector.visit_program(program);
        collector.failure.map_or(Ok(collector.functions), Err)
    }

    fn get(&self, symbol: SymbolId) -> Option<&'a Function<'a>> {
        self.declarations.get(&symbol).copied()
    }
}

enum Body<'a> {
    Statements(&'a FunctionBody<'a>),
    Expression(&'a Expression<'a>),
}

struct Activation<'a> {
    scope: ScopeId,
    params: &'a FormalParameters<'a>,
    body: Body<'a>,
    reflective: bool,
    publish_context: bool,
    self_binding: Option<SymbolId>,
}

impl<'a> Activation<'a> {
    fn from_node(node: CallableNode<'a>, scoping: &Scoping, publish_context: bool) -> Option<Self> {
        let activation = match node {
            CallableNode::Ordinary(function) => Self::ordinary(function, scoping, publish_context)?,
            CallableNode::Arrow(function) if !function.r#async => Self {
                scope: function.scope_id.get()?,
                params: &function.params,
                body: match &function.body {
                    ArrowFunctionBody::FunctionBody(body) => Body::Statements(body),
                    expression => Body::Expression(expression.as_expression()?),
                },
                reflective: false,
                publish_context,
                self_binding: None,
            },
            _ => return None,
        };
        if activation.params.rest.is_some()
            || activation.params.items.iter().any(|parameter| {
                parameter.initializer.is_some()
                    || !matches!(parameter.pattern, BindingPattern::BindingIdentifier(_))
            })
        {
            return None;
        }
        Some(activation)
    }

    fn ordinary(
        function: &'a Function<'a>,
        scoping: &Scoping,
        publish_context: bool,
    ) -> Option<Self> {
        if function.r#async || function.generator {
            return None;
        }
        let scope = function.scope_id.get()?;
        Some(Self {
            scope,
            params: &function.params,
            body: Body::Statements(function.body.as_ref()?),
            // Named declarations can be called at other sites. Their
            // context-specific observations are never published, so
            // reflection is an ordinary effect barrier, not a reason to
            // discard an otherwise proved normal return summary.
            reflective: publish_context && !scoping.scope_flags(scope).is_strict_mode(),
            publish_context,
            self_binding: (function.r#type == FunctionType::FunctionExpression)
                .then(|| function.id.as_ref().and_then(|id| id.symbol_id.get()))
                .flatten(),
        })
    }
}

impl<'ast> Analyzer<'_, 'ast> {
    pub(super) fn record_return(&mut self, value: Option<Fact>, environment: &Environment) {
        let Some(frame) = &self.return_frame else {
            return;
        };
        let mut after = environment.clone();
        // The caller's resources remain live. Only resources in this
        // activation's scopes are unwound on its return.
        if self.pending_disposals > frame.disposal_floor {
            self.invalidate(&mut after);
        }
        if let Some(frame) = &mut self.return_frame {
            let result = frame.record(value, after, self.budget);
            self.heap_result(result);
        }
    }

    fn unproved_returns(&mut self, visit: impl FnOnce(&mut ReturnProbe)) {
        if let Some(frame) = &mut self.return_frame {
            let mut probe = ReturnProbe::default();
            visit(&mut probe);
            frame.unproved |= probe.0;
        }
    }

    pub(super) fn unproved_statement_returns(&mut self, statement: &Statement<'_>) {
        self.unproved_returns(|probe| probe.visit_statement(statement));
    }

    fn initialize_activation(
        &mut self,
        activation: &Activation<'_>,
        arguments: Vec<Option<Fact>>,
        environment: &mut Environment,
    ) -> Option<()> {
        self.heap_result(environment.retire_activation(
            self.scoping,
            activation.scope,
            self.budget,
        ))?;
        let cells = self.scoping.get_bindings(activation.scope).len();
        self.heap_result(
            self.budget
                .consume(u64::try_from(cells).unwrap_or(u64::MAX)),
        )?;
        for (name, &symbol) in self.scoping.get_bindings(activation.scope) {
            let flags = self.scoping.symbol_flags(symbol);
            if flags.is_function_scoped_declaration()
                && !flags.is_function()
                && name.as_str() != "arguments"
                && !self
                    .bindings
                    .is_mapped_arguments_exposed(self.scoping, symbol)
            {
                self.heap_result(environment.insert(
                    symbol,
                    Fact::Primitive(Value::Undefined),
                    self.budget,
                ))?;
            }
        }
        if let Some(symbol) = activation.self_binding {
            self.heap_result(environment.remove(symbol, self.budget))?;
        }
        let mut arguments = arguments.into_iter();
        for parameter in &activation.params.items {
            let BindingPattern::BindingIdentifier(identifier) = &parameter.pattern else {
                return None;
            };
            let symbol = identifier.symbol_id.get()?;
            let value = arguments
                .next()
                .unwrap_or(Some(Fact::Primitive(Value::Undefined)));
            // A hoisted function declaration can override a formal binding.
            // A mapped arguments object may write it through an alias.
            if self.scoping.symbol_flags(symbol).is_function()
                || self
                    .bindings
                    .is_mapped_arguments_exposed(self.scoping, symbol)
            {
                continue;
            }
            if let Some(value) = value {
                self.heap_result(environment.insert(symbol, value, self.budget))?;
            } else {
                self.heap_result(environment.remove(symbol, self.budget))?;
            }
        }
        Some(())
    }

    fn execute_activation(
        &mut self,
        activation: &Activation<'_>,
        arguments: Vec<Option<Fact>>,
        environment: &mut Environment,
    ) -> Option<ReturnSummary> {
        self.initialize_activation(activation, arguments, environment)?;
        match activation.body {
            Body::Expression(expression) => {
                let result = self.expression(expression, environment);
                self.record_return(result.fact, environment);
            }
            Body::Statements(body) => {
                if self.statements(&body.statements, environment) {
                    self.record_return(Some(Fact::Primitive(Value::Undefined)), environment);
                }
            }
        }
        let frame = self.return_frame.take()?;
        if frame.unproved {
            return None;
        }
        let mut summary = frame.summary?;
        self.heap_result(summary.environment.retire_activation(
            self.scoping,
            activation.scope,
            self.budget,
        ))?;
        Some(summary)
    }

    /// Enter a fresh local activation. Semantic `SymbolId` values identify cells
    /// only within one live instance of a lexical scope, so an overlapping
    /// recursive activation must remain opaque until instance-indexed cells
    /// are available. Bound native recursion independently of loop fuel.
    fn can_enter(&self, scope: ScopeId) -> bool {
        const MAX_ACTIVATION_DEPTH: usize = 64;
        self.activation_scopes.len() < MAX_ACTIVATION_DEPTH
            && !self
                .scope_instances
                .scopes()
                .any(|active| active == scope || self.scoping.scope_is_descendant_of(active, scope))
    }

    fn direct_activation<'a>(
        &self,
        call: &'a CallExpression<'a>,
    ) -> Option<(Activation<'a>, Option<SymbolId>)>
    where
        'ast: 'a,
    {
        let (node, symbol, publish) = match call.callee.without_parentheses() {
            Expression::Identifier(identifier) => {
                let symbol = self
                    .bindings
                    .resolved_symbol(self.scoping, identifier.reference_id.get()?)?;
                let function = self.callables.get(symbol)?;
                self.bindings.hoisted_callable_at(
                    self.scoping,
                    &call.callee,
                    function.scope_id.get()?,
                )?;
                (CallableNode::Ordinary(function), Some(symbol), false)
            }
            Expression::FunctionExpression(function) if function.id.is_none() => {
                (CallableNode::Ordinary(function), None, true)
            }
            Expression::ArrowFunctionExpression(function) => {
                (CallableNode::Arrow(function), None, true)
            }
            _ => return None,
        };
        Some((Activation::from_node(node, self.scoping, publish)?, symbol))
    }

    /// Resolve an already evaluated callable value using its creation
    /// environment, not its current storage location or source spelling.
    fn captured_activation(
        &mut self,
        fact: &Fact,
        environment: &Environment,
    ) -> Option<Activation<'ast>> {
        let origin = environment.callable_origin(fact)?;
        if !self.heap_result(self.scope_instances.matches(&origin, self.budget))? {
            return None;
        }
        let node = *self.callables.nodes.get(&origin.scope)?;
        Activation::from_node(node, self.scoping, false)
    }

    /// Evaluate local calls with fresh activation cells. Resolve the callee
    /// exactly once before evaluating the arguments, even when no summary
    /// can be established.
    pub(super) fn local_call(
        &mut self,
        call: &CallExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        if call.optional {
            self.unobserved(call.span);
            return self.barrier(environment);
        }
        if call
            .arguments
            .iter()
            .any(|argument| argument.as_expression().is_none())
        {
            self.expression(&call.callee, environment);
            self.arguments(&call.arguments, environment);
            return self.barrier(environment);
        }
        let direct = self.direct_activation(call);
        let resolved = if let Some(direct) = direct {
            Some(direct)
        } else {
            let callee = self.expression(&call.callee, environment);
            callee
                .fact
                .as_ref()
                .and_then(|fact| self.captured_activation(fact, environment))
                .map(|activation| (activation, None))
        };
        let Some((activation, named)) = resolved else {
            self.arguments(&call.arguments, environment);
            return self.barrier(environment);
        };
        if !self.can_enter(activation.scope)
            || (activation.reflective && self.bindings.implicit_arguments_exposed(activation.scope))
        {
            self.arguments(&call.arguments, environment);
            return self.barrier(environment);
        }

        // Resolve the callee first, then evaluate each argument exactly once.
        // The scalar fast path and full heap path use these same values.
        let mut arguments = Vec::with_capacity(call.arguments.len());
        let mut inert = true;
        for argument in &call.arguments {
            let Some(expression) = argument.as_expression() else {
                self.unobserved(call.span);
                return self.barrier(environment);
            };
            let result = self.expression(expression, environment);
            inert &= result.inert;
            arguments.push(result.fact);
        }
        if let Some(symbol) = named {
            if let Some(function) = self.pure_functions.get(&symbol) {
                let values = arguments.iter().map(|fact| match fact {
                    Some(Fact::Primitive(value)) => Some(value),
                    _ => None,
                });
                if let Some(value) = function.evaluate(values, self.budget) {
                    return Evaluation::primitive(value, inert);
                }
                if !self.checkpoint() {
                    return self.barrier(environment);
                }
            }
        }
        let before_effect = self.opaque_generation;
        let mut candidate = environment.clone();
        candidate.enter_activation(self.next_allocation);
        let previous_reads = std::mem::take(&mut self.reads);
        let previous_lists = std::mem::take(&mut self.visited_lists);
        let previous_frame = self
            .return_frame
            .replace(ReturnFrame::new(self.pending_disposals));
        let disposes = self.enter_resource_scope(Some(activation.scope));
        self.activation_scopes.push(activation.scope);
        let ticket = self.scope_instances.enter(activation.scope);
        let summary = self.execute_activation(&activation, arguments, &mut candidate);
        self.scope_instances.leave(ticket);
        self.activation_scopes.pop();
        self.leave_resource_scope(disposes, &mut candidate);
        self.return_frame = previous_frame;
        let observations = std::mem::replace(&mut self.reads, previous_reads);
        let visited = std::mem::replace(&mut self.visited_lists, previous_lists);
        if let Some(mut summary) =
            summary.filter(|_| !activation.reflective || self.opaque_generation == before_effect)
        {
            summary.environment.leave_activation(environment);
            *environment = summary.environment;
            if activation.publish_context {
                self.reads.merge(observations);
                self.visited_lists.extend(visited);
            }
            // Do not erase the invocation, even when its result is known.
            return Evaluation {
                fact: summary.value,
                inert: false,
            };
        }
        if self.loop_fuel.is_some() {
            // Earlier iterations may already have observed this same body.
            // A failed activation cannot be omitted from their agreement.
            self.loop_failed = true;
        }
        self.barrier(environment)
    }

    pub(super) fn merge_loop_returns(&mut self, frame: Option<ReturnFrame>) {
        if let (Some(current), Some(frame)) = (&mut self.return_frame, frame) {
            let result = current.merge(frame, self.budget);
            self.heap_result(result);
        }
    }

    pub(super) fn unproved_loop_returns(&mut self, statement: &oxc_ast::ast::ForStatement<'_>) {
        self.unproved_returns(|probe| walk::walk_for_statement(probe, statement));
    }
}
