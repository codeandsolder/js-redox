//! Local invocation proofs share the ordinary statement/heap interpreter.
//! The call itself remains in the output; only reaching facts cross its exit.
use super::{
    arguments::ArgumentsSpec, cells::CellId, scope_instances::ClosureOrigin, Analyzer, Environment,
    Evaluation, Fact, Value,
};
use oxc_ast::ast::{
    ArrowFunctionBody, ArrowFunctionExpression, CallExpression, Expression, FormalParameters,
    Function, FunctionBody, FunctionType, Program, ThisExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::{collections::HashMap, rc::Rc};
use work_budget::{BudgetExceeded, WorkBudget};

const MAX_ACTIVATIONS: usize = 256;

struct ReturnSummary {
    value: Option<Fact>,
    environment: Environment,
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
    this_owners: HashMap<u32, ScopeId>,
}

struct CallableCollector<'c, 'a> {
    functions: CallableIndex<'a>,
    this_owner: Option<ScopeId>,
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
        let previous = std::mem::replace(&mut self.this_owner, function.scope_id.get());
        walk::walk_function(self, function, flags);
        self.this_owner = previous;
    }

    fn visit_this_expression(&mut self, expression: &ThisExpression) {
        if self.failure.is_some() {
            return;
        }
        if let Err(error) = self.budget.consume(1) {
            self.failure = Some(error);
            return;
        }
        if let Some(owner) = self.this_owner {
            self.functions
                .this_owners
                .insert(expression.span.start, owner);
        }
    }

    fn visit_class(&mut self, class: &oxc_ast::ast::Class<'a>) {
        // Field initializers and static blocks have their own this binding.
        // A nested ordinary method establishes its own owner normally.
        // Class evaluation itself is outside the current heap interpreter.
        let previous = self.this_owner.take();
        walk::walk_class(self, class);
        self.this_owner = previous;
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
                this_owners: HashMap::new(),
            },
            this_owner: None,
            budget,
            failure: None,
        };
        collector.visit_program(program);
        collector.failure.map_or(Ok(collector.functions), Err)
    }

    pub(super) fn this_owner(&self, expression: &ThisExpression) -> Option<ScopeId> {
        self.this_owners.get(&expression.span.start).copied()
    }

    fn get(&self, symbol: SymbolId) -> Option<&'a Function<'a>> {
        self.declarations.get(&symbol).copied()
    }
}

enum Body<'a> {
    Statements(&'a FunctionBody<'a>),
    Expression(&'a Expression<'a>),
}

#[derive(Clone, Copy)]
enum ThisMode {
    Lexical,
    Strict,
    Sloppy,
}

impl ThisMode {
    fn binding(self, receiver: Option<Fact>) -> Option<Fact> {
        match self {
            Self::Lexical => None,
            Self::Strict => receiver,
            // Non-null objects are passed unchanged. Boxing primitive
            // receivers and the realm's global object remain unproved.
            Self::Sloppy => receiver.filter(|fact| matches!(fact, Fact::Objects(_))),
        }
    }
}

enum CallTargets<'a> {
    Single(Activation<'a>),
    Alternatives(Vec<Activation<'a>>),
}

struct Activation<'a> {
    scope: ScopeId,
    params: &'a FormalParameters<'a>,
    body: Body<'a>,
    reflective: bool,
    publish_context: bool,
    self_binding: Option<SymbolId>,
    this_mode: ThisMode,
    capture: Option<(ClosureOrigin, Fact)>,
}

impl<'a> Activation<'a> {
    fn from_node(node: CallableNode<'a>, scoping: &Scoping, publish_context: bool) -> Option<Self> {
        match node {
            CallableNode::Ordinary(function) => Self::ordinary(function, scoping, publish_context),
            CallableNode::Arrow(function) if !function.r#async => Some(Self {
                scope: function.scope_id.get()?,
                params: &function.params,
                body: match &function.body {
                    ArrowFunctionBody::FunctionBody(body) => Body::Statements(body),
                    expression => Body::Expression(expression.as_expression()?),
                },
                reflective: false,
                publish_context,
                self_binding: None,
                this_mode: ThisMode::Lexical,
                capture: None,
            }),
            CallableNode::Arrow(_) => None,
        }
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
            this_mode: if scoping.scope_flags(scope).is_strict_mode() {
                ThisMode::Strict
            } else {
                ThisMode::Sloppy
            },
            publish_context,
            self_binding: (function.r#type == FunctionType::FunctionExpression)
                .then(|| function.id.as_ref().and_then(|id| id.symbol_id.get()))
                .flatten(),
            capture: None,
        })
    }
}

impl<'ast> Analyzer<'_, 'ast> {
    /// Install actual declaration objects on entry to their lexical owner.
    /// Never reconstruct an allocation after an opaque effect: a previously
    /// evaluated reference may still denote the same function object.
    pub(super) fn initialize_hoisted_callables(
        &mut self,
        scope: ScopeId,
        environment: &mut Environment,
    ) -> Option<()> {
        for &symbol in self.scoping.get_bindings(scope).values() {
            self.heap_result(self.budget.consume(1))?;
            let Some(function) = self.callables.get(symbol) else {
                continue;
            };
            let Some(function_scope) = function.scope_id.get() else {
                continue;
            };
            if !self
                .bindings
                .inert_function_declaration(self.scoping, function)
                || !self.bindings.instantiated_function_declaration(
                    self.scoping,
                    symbol,
                    function_scope,
                )
            {
                continue;
            }
            let value = self
                .allocate_callable(function.scope_id.get(), environment)
                .fact?;
            self.heap_result(environment.insert(self.cell_id(symbol)?, value, self.budget))?;
        }
        Some(())
    }

    fn initialize_activation(
        &mut self,
        activation: &Activation<'_>,
        arguments: Vec<Option<Fact>>,
        receiver: Option<Fact>,
        environment: &mut Environment,
    ) -> Option<()> {
        if let Some(receiver) = activation.this_mode.binding(receiver) {
            let instance = self.scope_instances.get(activation.scope, || true)?;
            self.heap_result(environment.insert(
                CellId::receiver(instance),
                receiver,
                self.budget,
            ))?;
        }
        if let Some(symbol) = activation.self_binding {
            let cell = self.cell_id(symbol)?;
            if let Some((_, function)) = &activation.capture {
                let value = self.heap_result(function.copy(self.budget))?;
                self.heap_result(environment.insert(cell, value, self.budget))?;
            }
        }
        if !matches!(activation.this_mode, ThisMode::Lexical) {
            self.initialize_arguments_object(
                ArgumentsSpec {
                    scope: activation.scope,
                    params: activation.params,
                    strict: matches!(activation.this_mode, ThisMode::Strict),
                    callee: activation.capture.as_ref().map(|(_, fact)| fact),
                },
                &arguments,
                environment,
            )?;
        }
        self.initialize_parameters(activation.params, arguments, environment)?;
        self.initialize_body_environment(activation.scope, activation.params, environment)?;
        self.initialize_hoisted_callables(activation.scope, environment)
    }

    fn execute_activation(
        &mut self,
        activation: &Activation<'_>,
        arguments: Vec<Option<Fact>>,
        receiver: Option<Fact>,
        environment: &mut Environment,
    ) -> Option<super::flow::Flow> {
        use super::flow::{CompletionValue, Flow, Transfer};
        self.initialize_activation(activation, arguments, receiver, environment)?;
        match activation.body {
            Body::Expression(expression) => {
                let result = self.expression(expression, environment);
                Some(Flow::abrupt(
                    Transfer::Return,
                    CompletionValue::value(result.fact),
                    environment,
                ))
            }
            Body::Statements(body) => self.statements(&body.statements, environment),
        }
    }

    fn summarize_activation(
        &mut self,
        mut flow: super::flow::Flow,
        environment: &Environment,
    ) -> Option<ReturnSummary> {
        use super::flow::{CompletionValue, Transfer};
        if flow.unproved {
            return None;
        }
        let mut returned = flow.abrupt.remove(&Transfer::Return);
        // A function with no explicit return returns undefined regardless
        // of the last normal statement's completion value.
        if flow.normal.is_some() {
            let path = super::flow::Path {
                value: CompletionValue::undefined(),
                environment: environment.clone(),
            };
            self.heap_result(super::flow::Path::accumulate(
                &mut returned,
                path,
                self.budget,
            ))?;
        }
        if flow.abrupt.keys().any(|kind| *kind != Transfer::Throw) {
            return None;
        }
        let returned = returned?;
        Some(ReturnSummary {
            value: self.heap_result(returned.value.into_fact(self.budget))?,
            environment: returned.environment,
        })
    }

    /// Distinct environment instances have distinct cell identities.
    /// Bound both native stack depth and the total speculative call tree.
    const fn can_enter(&self) -> bool {
        const MAX_ACTIVATION_DEPTH: usize = 32;
        self.activation_depth < MAX_ACTIVATION_DEPTH
            && (self.activation_depth == 0 || self.activation_fuel > 0)
    }

    fn direct_activation<'a>(
        &self,
        call: &'a CallExpression<'a>,
        environment: &Environment,
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
            Expression::FunctionExpression(function)
                if function.id.is_none()
                    && !self
                        .bindings
                        .implicit_arguments_exposed(function.scope_id.get()?) =>
            {
                (CallableNode::Ordinary(function), None, true)
            }
            Expression::ArrowFunctionExpression(function) => {
                (CallableNode::Arrow(function), None, true)
            }
            _ => return None,
        };
        let mut activation = Activation::from_node(node, self.scoping, publish)?;
        // Preserve a declaration's actual identity when the current
        // reaching cell establishes it; never invent it after a barrier.
        if let Some(symbol) = symbol {
            if let Some(Fact::Objects(locations)) =
                self.cell_id(symbol).and_then(|cell| environment.get(cell))
            {
                if let [id] = locations.as_ref() {
                    if let Some(origin) = environment.callable_origin(*id) {
                        if origin.scope == activation.scope {
                            activation.capture =
                                Some((origin, Fact::Objects(Rc::clone(locations))));
                        }
                    }
                }
            }
        }
        Some((activation, symbol))
    }

    /// Resolve every possible call target before argument evaluation.
    /// Each allocation captures its own lexical instance chain. A missing
    /// origin or unsupported target makes the whole call opaque.
    fn captured_activations(
        &mut self,
        fact: &Fact,
        environment: &Environment,
    ) -> Option<CallTargets<'ast>> {
        let Fact::Objects(locations) = fact else {
            return None;
        };
        self.heap_result(super::heap::charge(self.budget, locations.len()))?;
        if locations.len() > MAX_ACTIVATIONS {
            return None;
        }
        let resolve = |id| {
            let origin = environment.callable_origin(id)?;
            let node = *self.callables.nodes.get(&origin.scope)?;
            let mut activation = Activation::from_node(node, self.scoping, false)?;
            activation.capture = Some((origin, Fact::Objects(Rc::from([id]))));
            Some(activation)
        };
        if let [id] = locations.as_ref() {
            return resolve(*id).map(CallTargets::Single);
        }
        locations
            .iter()
            .copied()
            .map(resolve)
            .collect::<Option<Vec<_>>>()
            .map(CallTargets::Alternatives)
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
        let mut receiver = Some(Fact::Primitive(Value::Undefined));
        let resolved = self
            .direct_activation(call, environment)
            .map(|(activation, named)| (CallTargets::Single(activation), named))
            .or_else(|| {
                let (callee, this_arg) = self.evaluate_callee(&call.callee, environment);
                receiver = this_arg;
                callee
                    .fact
                    .as_ref()
                    .and_then(|fact| self.captured_activations(fact, environment))
                    .map(|activations| (activations, None))
            });
        self.invoke_resolved_call(call, resolved, receiver, environment)
    }

    /// Used by optional chains once a preceding member/call evaluation
    /// has established the actual callee and its reference receiver.
    pub(super) fn invoke_captured_call(
        &mut self,
        call: &CallExpression<'_>,
        callee: Option<&Fact>,
        receiver: Option<Fact>,
        environment: &mut Environment,
    ) -> Evaluation {
        let resolved = callee
            .and_then(|fact| self.captured_activations(fact, environment))
            .map(|activations| (activations, None));
        self.invoke_resolved_call(call, resolved, receiver, environment)
    }

    fn invoke_resolved_call(
        &mut self,
        call: &CallExpression<'_>,
        resolved: Option<(CallTargets<'_>, Option<SymbolId>)>,
        receiver: Option<Fact>,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some((activations, named)) = resolved else {
            self.arguments(&call.arguments, environment);
            return self.barrier(environment);
        };
        if call
            .arguments
            .iter()
            .any(|argument| argument.as_expression().is_none())
            || !self.can_enter()
            || matches!(&activations, CallTargets::Single(activation) if activation.reflective && self.bindings.implicit_arguments_exposed(activation.scope))
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
        if self.activation_depth == 0 {
            self.activation_fuel = MAX_ACTIVATIONS;
        }
        match activations {
            CallTargets::Single(activation) => {
                self.run_activation(&activation, arguments, receiver, environment)
            }
            CallTargets::Alternatives(activations) => {
                self.run_alternatives(activations, &arguments, receiver.as_ref(), environment)
            }
        }
    }

    /// All candidate calls start after the same argument evaluation.
    /// Allocation identities born in one alternative cannot be present
    /// in another; pre-fork identities must agree across every outcome.
    fn run_alternatives(
        &mut self,
        activations: Vec<Activation<'_>>,
        arguments: &[Option<Fact>],
        receiver: Option<&Fact>,
        environment: &mut Environment,
    ) -> Evaluation {
        if activations.is_empty() || activations.len() > self.activation_fuel {
            return self.barrier(environment);
        }
        let base = environment.clone();
        let first_new = self.next_identity;
        let mut result = None::<Evaluation>;
        for activation in activations {
            let charge = arguments
                .iter()
                .flatten()
                .chain(receiver)
                .try_for_each(|fact| super::heap::charge(self.budget, fact.clone_weight()));
            if self.heap_result(charge).is_none() {
                return self.barrier(environment);
            }
            let mut alternative = base.clone();
            let next = self.run_activation(
                &activation,
                arguments.to_vec(),
                receiver.cloned(),
                &mut alternative,
            );
            if let Some(previous) = &mut result {
                if !self.join_heap(environment, &alternative, first_new) {
                    return self.barrier(environment);
                }
                previous.fact = match (previous.fact.as_ref(), next.fact.as_ref()) {
                    (Some(left), Some(right)) => {
                        self.heap_result(left.join(right, self.budget)).flatten()
                    }
                    _ => None,
                };
            } else {
                *environment = alternative;
                result = Some(next);
            }
        }
        result.unwrap_or_default()
    }

    fn run_activation(
        &mut self,
        activation: &Activation<'_>,
        arguments: Vec<Option<Fact>>,
        receiver: Option<Fact>,
        environment: &mut Environment,
    ) -> Evaluation {
        if !self.can_enter()
            || self.activation_fuel == 0
            || self.heap_result(self.budget.consume(1)).is_none()
        {
            return self.barrier(environment);
        }
        self.activation_fuel -= 1;
        let before_effect = self.opaque_generation;
        let mut candidate = environment.clone();
        candidate.enter_activation(self.next_identity);
        let selected = activation.capture.as_ref().map_or_else(
            || Ok(Vec::new()),
            |(origin, _)| self.scope_instances.select(origin, self.budget),
        );
        let Some(selected) = self.heap_result(selected) else {
            return self.barrier(environment);
        };
        let previous_reads = std::mem::take(&mut self.reads);
        let previous_lists = std::mem::take(&mut self.visited_lists);
        let disposes = self.bindings.scope_may_dispose(activation.scope);
        self.activation_depth += 1;
        let ticket = self.enter_empty_instance(activation.scope, &mut candidate);
        let flow = if ticket.is_some() {
            self.execute_activation(activation, arguments, receiver, &mut candidate)
        } else {
            None
        };
        let summary = flow.and_then(|mut flow| {
            self.dispose_paths(disposes, &mut flow, &mut candidate);
            self.summarize_activation(flow, &candidate)
        });
        self.leave_instance(ticket, &mut candidate);
        self.activation_depth -= 1;
        for ticket in selected.into_iter().rev() {
            let _ = self.scope_instances.leave(&ticket);
        }
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
}
