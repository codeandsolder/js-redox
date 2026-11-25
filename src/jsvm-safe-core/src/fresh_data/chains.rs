//! Ordered optional-chain evaluation. Short circuit is a control result,
//! not an undefined value that later links are allowed to dereference.
use super::{Analyzer, Environment, Evaluation, Fact, Reference, Value};
use oxc_ast::ast::{CallExpression, ChainElement, ChainExpression, Expression, MemberExpression};
use oxc_span::GetSpan;

enum ChainState {
    Reached {
        value: Evaluation,
        receiver: Option<Fact>,
    },
    ShortCircuited {
        inert: bool,
    },
}

impl ChainState {
    fn value(self) -> (Evaluation, Option<Fact>) {
        match self {
            Self::Reached { value, receiver } => (value, receiver),
            Self::ShortCircuited { inert } => (
                Evaluation::primitive(Value::Undefined, inert),
                Some(Fact::Primitive(Value::Undefined)),
            ),
        }
    }

    fn ordinary(value: Evaluation) -> Self {
        Self::Reached {
            value,
            receiver: Some(Fact::Primitive(Value::Undefined)),
        }
    }
}

#[derive(Clone, Copy)]
enum Terminal {
    Value,
    Delete,
}

fn nullish(value: &Evaluation) -> Option<bool> {
    value
        .fact
        .as_ref()
        .map(|fact| matches!(fact, Fact::Primitive(Value::Null | Value::Undefined)))
}

impl Analyzer<'_, '_> {
    /// Parentheses terminate the short circuit but preserve a member
    /// reference on the reached path, including when used as a callee.
    pub(super) fn chain_expression(
        &mut self,
        chain: &ChainExpression<'_>,
        environment: &mut Environment,
    ) -> (Evaluation, Option<Fact>) {
        self.evaluate_chain(chain, Terminal::Value, environment)
    }

    pub(super) fn delete_chain(
        &mut self,
        chain: &ChainExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        self.evaluate_chain(chain, Terminal::Delete, environment).0
    }

    fn evaluate_chain(
        &mut self,
        chain: &ChainExpression<'_>,
        terminal: Terminal,
        environment: &mut Environment,
    ) -> (Evaluation, Option<Fact>) {
        let result = match &chain.expression {
            ChainElement::CallExpression(call) => {
                self.chain_call(call, environment)
                    .map(|state| match (terminal, state) {
                        (Terminal::Delete, ChainState::Reached { value, .. }) => {
                            ChainState::ordinary(Evaluation::primitive(
                                Value::Bool(true),
                                value.inert,
                            ))
                        }
                        (_, state) => state,
                    })
            }
            element => element
                .as_member_expression()
                .and_then(|member| self.chain_member(member, terminal, environment)),
        };
        match result {
            Some(ChainState::ShortCircuited { inert }) if matches!(terminal, Terminal::Delete) => {
                (Evaluation::primitive(Value::Bool(true), inert), None)
            }
            Some(state) => state.value(),
            None => {
                self.unobserved(chain.span);
                (self.barrier(environment), None)
            }
        }
    }

    fn chain_operand(
        &mut self,
        expression: &Expression<'_>,
        environment: &mut Environment,
    ) -> Option<ChainState> {
        self.heap_result(self.budget.consume(1))?;
        if let Some(member) = expression.as_member_expression() {
            self.chain_member(member, Terminal::Value, environment)
        } else if let Expression::CallExpression(call) = expression {
            self.chain_call(call, environment)
        } else {
            // A grouped nested chain is an ordinary value/reference here.
            // Only a contiguous member/call chain propagates short circuit.
            let (value, receiver) = self.evaluate_callee(expression, environment);
            Some(ChainState::Reached { value, receiver })
        }
    }

    fn chain_member(
        &mut self,
        member: &MemberExpression<'_>,
        terminal: Terminal,
        environment: &mut Environment,
    ) -> Option<ChainState> {
        let state = self.chain_operand(member.object(), environment)?;
        let object = match state {
            ChainState::Reached { value, .. } => value,
            state => {
                self.unobserved(member.span());
                return Some(state);
            }
        };
        if member.optional() && nullish(&object)? {
            self.unobserved(member.span());
            return Some(ChainState::ShortCircuited {
                inert: object.inert,
            });
        }
        let key = self.member_key(member, environment)?;
        if matches!(terminal, Terminal::Delete) {
            let key = key.primitive_value()?.js_string();
            let Fact::Objects(locations) = object.fact? else {
                return None;
            };
            return Some(ChainState::ordinary(self.delete_reference(
                &locations,
                &key,
                environment,
            )));
        }
        let receiver = object
            .fact
            .as_ref()
            .map(|fact| fact.copy(self.budget))
            .transpose();
        let receiver = self.heap_result(receiver)?;
        // Do not publish rewrites of individual chain links: the outer
        // chain can short circuit and the original reference matters.
        let value = self.member(object, &key, environment);
        Some(ChainState::Reached { value, receiver })
    }

    fn chain_call(
        &mut self,
        call: &CallExpression<'_>,
        environment: &mut Environment,
    ) -> Option<ChainState> {
        let state = self.chain_operand(&call.callee, environment)?;
        let (value, receiver) = match state {
            ChainState::Reached { value, receiver } => (value, receiver),
            state => {
                self.unobserved(call.span);
                return Some(state);
            }
        };
        if call.optional && nullish(&value)? {
            self.unobserved(call.span);
            return Some(ChainState::ShortCircuited { inert: value.inert });
        }
        let result = self.invoke_captured_call(call, value.fact.as_ref(), receiver, environment);
        Some(ChainState::ordinary(result))
    }
}
