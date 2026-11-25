//! Specialize selector calls only when the original activation's result is
//! established. The selected return expression is evaluated in semantic
//! parameter cells, never copied into a potentially shadowing caller scope.
use crate::{
    binding_facts::BindingFacts, expression_integer, known_bool, pure_function::PureFunction,
};
use oxc_ast::ast::{BindingPattern, Expression, Function, FunctionType, Statement};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::{
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::collections::{HashMap, HashSet};

struct SelectorProof<'c> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    stable_var_numbers: &'c HashMap<SymbolId, i64>,
    selector: SymbolId,
}

enum Flow<'a, 'ast> {
    Continue,
    Return(&'a Expression<'ast>),
}

impl SelectorProof<'_> {
    fn symbol(&self, expression: &Expression<'_>) -> Option<SymbolId> {
        let Expression::Identifier(identifier) = expression.without_parentheses() else {
            return None;
        };
        self.facts
            .resolved_symbol(self.scoping, identifier.reference_id.get()?)
    }

    fn comparison(&self, binary: &oxc_ast::ast::BinaryExpression<'_>, value: i64) -> Option<bool> {
        let other = if self.symbol(&binary.left) == Some(self.selector) {
            &binary.right
        } else if self.symbol(&binary.right) == Some(self.selector) {
            &binary.left
        } else {
            return None;
        };
        let equal = if let Some(number) = expression_integer(other) {
            number == value
        } else {
            let number = *self.stable_var_numbers.get(&self.symbol(other)?)?;
            // A stable declarative var may contain either undefined or its
            // exact numeric initializer. Both compare unequal to a different
            // number, but equality to the initializer requires ordering proof.
            if number == value {
                return None;
            }
            false
        };
        Some(if matches!(binary.operator.as_str(), "==" | "===") {
            equal
        } else {
            !equal
        })
    }

    fn test(&self, expression: &Expression<'_>, value: i64) -> Option<bool> {
        match expression.without_parentheses() {
            Expression::UnaryExpression(unary) if unary.operator.as_str() == "!" => {
                self.test(&unary.argument, value).map(|result| !result)
            }
            Expression::LogicalExpression(logical) => {
                // A later known operand must not justify discarding an
                // unknown/effectful earlier operand.
                let left = self.test(&logical.left, value)?;
                match (logical.operator.as_str(), left) {
                    ("&&", false) => Some(false),
                    ("||", true) => Some(true),
                    ("&&" | "||", _) => self.test(&logical.right, value),
                    _ => None,
                }
            }
            Expression::BinaryExpression(binary)
                if matches!(binary.operator.as_str(), "==" | "===" | "!=" | "!==") =>
            {
                self.comparison(binary, value)
                    .or_else(|| known_bool(expression))
            }
            _ => known_bool(expression),
        }
    }

    fn returned<'a, 'ast>(
        &self,
        expression: &'a Expression<'ast>,
        value: i64,
    ) -> Option<&'a Expression<'ast>> {
        if let Expression::ConditionalExpression(conditional) = expression.without_parentheses() {
            let test = self.test(&conditional.test, value)?;
            self.returned(
                if test {
                    &conditional.consequent
                } else {
                    &conditional.alternate
                },
                value,
            )
        } else {
            Some(expression)
        }
    }

    fn statement<'a, 'ast>(
        &self,
        statement: &'a Statement<'ast>,
        value: i64,
    ) -> Option<Flow<'a, 'ast>> {
        match statement {
            Statement::BlockStatement(block) => self.statements(&block.body, value),
            Statement::IfStatement(branch) => {
                if self.test(&branch.test, value)? {
                    self.statement(&branch.consequent, value)
                } else if let Some(alternate) = &branch.alternate {
                    self.statement(alternate, value)
                } else {
                    Some(Flow::Continue)
                }
            }
            Statement::ReturnStatement(ret) => {
                Some(Flow::Return(self.returned(ret.argument.as_ref()?, value)?))
            }
            Statement::EmptyStatement(_) => Some(Flow::Continue),
            _ => None,
        }
    }

    fn statements<'a, 'ast>(
        &self,
        statements: &'a [Statement<'ast>],
        value: i64,
    ) -> Option<Flow<'a, 'ast>> {
        for statement in statements {
            match self.statement(statement, value)? {
                Flow::Continue => {}
                returned @ Flow::Return(_) => return Some(returned),
            }
        }
        Some(Flow::Continue)
    }
}

struct LiteralCollector<'c> {
    proof: &'c SelectorProof<'c>,
    values: HashSet<i64>,
}

impl<'a> Visit<'a> for LiteralCollector<'_> {
    fn visit_function(&mut self, _: &Function<'a>, _: ScopeFlags) {}
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}

    fn visit_binary_expression(&mut self, binary: &oxc_ast::ast::BinaryExpression<'a>) {
        if matches!(binary.operator.as_str(), "==" | "===" | "!=" | "!==") {
            let literal = if self.proof.symbol(&binary.left) == Some(self.proof.selector) {
                expression_integer(&binary.right)
            } else if self.proof.symbol(&binary.right) == Some(self.proof.selector) {
                expression_integer(&binary.left)
            } else {
                None
            };
            if let Some(literal) = literal {
                self.values.insert(literal);
            }
        }
        walk::walk_binary_expression(self, binary);
    }
}

#[derive(Debug)]
pub struct SelectorDispatcher {
    pub(super) selector_index: usize,
    pub(super) scope: ScopeId,
    pub(super) returns: HashMap<i64, PureFunction>,
}

struct DispatcherCollector<'c> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    stable_var_numbers: &'c HashMap<SymbolId, i64>,
    dispatchers: HashMap<SymbolId, SelectorDispatcher>,
}

impl DispatcherCollector<'_> {
    fn prove(&self, function: &Function<'_>) -> Option<(SymbolId, SelectorDispatcher)> {
        if function.r#type != FunctionType::FunctionDeclaration
            || function.r#async
            || function.generator
            || function.params.rest.is_some()
        {
            return None;
        }
        let symbol = function.id.as_ref()?.symbol_id.get()?;
        let scope = function.scope_id.get()?;
        if !self
            .facts
            .hoisted_callable_declaration(self.scoping, symbol, scope)
        {
            return None;
        }
        let params = function
            .params
            .items
            .iter()
            .map(|parameter| {
                if parameter.initializer.is_some() {
                    return None;
                }
                let BindingPattern::BindingIdentifier(id) = &parameter.pattern else {
                    return None;
                };
                let symbol = id.symbol_id.get()?;
                // Duplicate formal declarations have ordinary parameter
                // initialization semantics, but a body declaration can install
                // a different value even before its textual statement executes.
                self.scoping
                    .symbol_redeclarations(symbol)
                    .iter()
                    .all(|decl| {
                        function.params.span.start <= decl.span.start
                            && decl.span.end <= function.params.span.end
                    })
                    .then_some(symbol)
            })
            .collect::<Option<Vec<_>>>()?;
        let selector = *params.first()?;
        let selector_index = params.iter().rposition(|&param| param == selector)?;
        let body = function.body.as_ref()?;
        let proof = SelectorProof {
            scoping: self.scoping,
            facts: self.facts,
            stable_var_numbers: self.stable_var_numbers,
            selector,
        };
        let mut literals = LiteralCollector {
            proof: &proof,
            values: HashSet::new(),
        };
        for statement in &body.statements {
            literals.visit_statement(statement);
        }
        let returns = literals
            .values
            .into_iter()
            .filter_map(|value| {
                let Flow::Return(expression) = proof.statements(&body.statements, value)? else {
                    return None;
                };
                let projection =
                    PureFunction::return_projection(function, expression, self.scoping)?;
                Some((value, projection))
            })
            .collect::<HashMap<_, _>>();
        (!returns.is_empty()).then_some((
            symbol,
            SelectorDispatcher {
                selector_index,
                scope,
                returns,
            },
        ))
    }
}

impl<'a> Visit<'a> for DispatcherCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some((symbol, dispatcher)) = self.prove(function) {
            self.dispatchers.insert(symbol, dispatcher);
        }
        walk::walk_function(self, function, flags);
    }
}

pub fn collect_selector_dispatchers(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> HashMap<SymbolId, SelectorDispatcher> {
    let mut collector = DispatcherCollector {
        scoping,
        facts,
        stable_var_numbers,
        dispatchers: HashMap::new(),
    };
    collector.visit_program(program);
    collector.dispatchers
}
