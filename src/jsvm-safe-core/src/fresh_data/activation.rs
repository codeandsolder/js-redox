//! Immediate invocation proofs share the ordinary statement/heap interpreter.
//! The call itself remains in the output; only reaching facts cross its exit.
use super::{Analyzer, Environment, Evaluation, Fact, Value};
use oxc_ast::ast::{
    ArrowFunctionBody, ArrowFunctionExpression, BindingPattern, CallExpression, Expression,
    FormalParameters, Function, FunctionBody, Statement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::scope::{ScopeFlags, ScopeId};
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

enum Body<'a> {
    Statements(&'a FunctionBody<'a>),
    Expression(&'a Expression<'a>),
}

struct Activation<'a> {
    scope: ScopeId,
    params: &'a FormalParameters<'a>,
    body: Body<'a>,
    reflective: bool,
}

impl<'a> Activation<'a> {
    fn new(call: &'a CallExpression<'a>, scoping: &Scoping) -> Option<Self> {
        if call.optional
            || call
                .arguments
                .iter()
                .any(|arg| arg.as_expression().is_none())
        {
            return None;
        }
        let activation = match call.callee.without_parentheses() {
            Expression::FunctionExpression(function)
                if !function.r#async && !function.generator && function.id.is_none() =>
            {
                let scope = function.scope_id.get()?;
                Self {
                    scope,
                    params: &function.params,
                    body: Body::Statements(function.body.as_ref()?),
                    reflective: !scoping.scope_flags(scope).is_strict_mode(),
                }
            }
            Expression::ArrowFunctionExpression(function) if !function.r#async => Self {
                scope: function.scope_id.get()?,
                params: &function.params,
                body: match &function.body {
                    ArrowFunctionBody::FunctionBody(body) => Body::Statements(body),
                    expression => Body::Expression(expression.as_expression()?),
                },
                reflective: false,
            },
            _ => return None,
        };
        // Parameter instantiation for a simple list uses one declarative
        // environment. Defaults/rest/destructuring require an additional
        // parameter-expression and iterator proof, not a value substitution.
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
}

impl Analyzer<'_> {
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

    /// Evaluate a source-local, immediate function expression or arrow with
    /// fresh activation cells. Legacy sloppy caller reflection may expose
    /// the function object via unknown reentrant code. Such a call cannot
    /// publish context-specialized body observations.
    pub(super) fn immediate_call(
        &mut self,
        call: &CallExpression<'_>,
        environment: &mut Environment,
    ) -> Option<Evaluation> {
        let activation = Activation::new(call, self.scoping)?;
        if activation.reflective && self.bindings.implicit_arguments_exposed(activation.scope) {
            // Even returning the implicit arguments object without an
            // opaque call can expose arguments.callee for later invocation.
            return None;
        }
        let arguments = call
            .arguments
            .iter()
            .map(|argument| {
                argument
                    .as_expression()
                    .map(|expression| self.expression(expression, environment).fact)
            })
            .collect::<Option<Vec<_>>>()?;
        let before_effect = self.opaque_generation;
        let mut candidate = environment.clone();
        candidate.enter_activation(self.next_allocation);
        let previous_reads = std::mem::take(&mut self.reads);
        let previous_lists = std::mem::take(&mut self.visited_lists);
        let previous_frame = self
            .return_frame
            .replace(ReturnFrame::new(self.pending_disposals));
        let disposes = self.enter_resource_scope(Some(activation.scope));
        let summary = self.execute_activation(&activation, arguments, &mut candidate);
        self.leave_resource_scope(disposes, &mut candidate);
        self.return_frame = previous_frame;
        let observations = std::mem::replace(&mut self.reads, previous_reads);
        let visited = std::mem::replace(&mut self.visited_lists, previous_lists);
        if let Some(mut summary) =
            summary.filter(|_| !activation.reflective || self.opaque_generation == before_effect)
        {
            summary.environment.leave_activation(environment);
            *environment = summary.environment;
            self.reads.merge(observations);
            self.visited_lists.extend(visited);
            // Do not erase the invocation, even when its result is known.
            return Some(Evaluation {
                fact: summary.value,
                inert: false,
            });
        }
        if self.loop_fuel.is_some() {
            // Earlier iterations may already have observed this same body.
            // A failed activation cannot be omitted from their agreement.
            self.loop_failed = true;
        }
        Some(self.barrier(environment))
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
