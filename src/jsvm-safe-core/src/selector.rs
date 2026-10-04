//! Proof of selector-style dispatcher functions used by control-flow obfuscators.
//!
//! This is intentionally project-specific proof logic: it proves a narrow
//! function/branch shape and records only selector values whose return path is
//! statically unique. Generic JavaScript coercion/evaluation remains delegated
//! to the shared value evaluator.

use super::*;

fn selector_identifier_symbol(expr: &Expression<'_>, scoping: &Scoping) -> Option<SymbolId> {
    match expr {
        Expression::Identifier(_) => symbol_of(scoping, expr),
        Expression::ParenthesizedExpression(parenthesized) => {
            selector_identifier_symbol(&parenthesized.expression, scoping)
        }
        _ => None,
    }
}

fn selector_test_value(
    expr: &Expression<'_>,
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<bool> {
    match expr {
        Expression::ParenthesizedExpression(parenthesized) => selector_test_value(
            &parenthesized.expression,
            selector_symbol,
            selector_value,
            scoping,
            stable_var_numbers,
        ),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "!" => {
            selector_test_value(
                &unary.argument,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )
            .map(|value| !value)
        }
        Expression::LogicalExpression(logical) => {
            let left = selector_test_value(
                &logical.left,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            );
            let right = selector_test_value(
                &logical.right,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            );
            match logical.operator.as_str() {
                "&&" => match (left, right) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), Some(true)) => Some(true),
                    _ => None,
                },
                "||" => match (left, right) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                },
                _ => None,
            }
        }
        Expression::BinaryExpression(binary)
            if matches!(binary.operator.as_str(), "==" | "===" | "!=" | "!==") =>
        {
            let left_symbol = selector_identifier_symbol(&binary.left, scoping);
            let right_symbol = selector_identifier_symbol(&binary.right, scoping);

            let other = if left_symbol == Some(selector_symbol) {
                Some(&binary.right)
            } else if right_symbol == Some(selector_symbol) {
                Some(&binary.left)
            } else {
                None
            }?;

            let equal = if let Some(number) = expression_integer(other) {
                selector_value == number
            } else {
                let symbol = selector_identifier_symbol(other, scoping)?;
                let initialized_value = *stable_var_numbers.get(&symbol)?;
                if selector_value == initialized_value {
                    // A var binding is undefined before its initializer executes
                    // and has the proven number afterward. Equality to that exact
                    // number therefore depends on runtime ordering.
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
        _ => known_bool(expr),
    }
}

#[derive(Debug, Clone, Copy)]
enum SelectorFlow {
    Continue,
    Return(Span),
}

fn selector_return_expression(
    expr: &Expression<'_>,
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<Span> {
    match expr {
        Expression::ConditionalExpression(conditional) => {
            let test = selector_test_value(
                &conditional.test,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )?;
            selector_return_expression(
                if test {
                    &conditional.consequent
                } else {
                    &conditional.alternate
                },
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )
        }
        _ => Some(expr.span()),
    }
}

fn selector_statement_flow(
    statement: &Statement<'_>,
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<SelectorFlow> {
    match statement {
        Statement::BlockStatement(block) => selector_statements_flow(
            &block.body,
            selector_symbol,
            selector_value,
            scoping,
            stable_var_numbers,
        ),
        Statement::IfStatement(branch) => {
            let test = selector_test_value(
                &branch.test,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )?;
            if test {
                selector_statement_flow(
                    &branch.consequent,
                    selector_symbol,
                    selector_value,
                    scoping,
                    stable_var_numbers,
                )
            } else if let Some(alternate) = &branch.alternate {
                selector_statement_flow(
                    alternate,
                    selector_symbol,
                    selector_value,
                    scoping,
                    stable_var_numbers,
                )
            } else {
                Some(SelectorFlow::Continue)
            }
        }
        Statement::ReturnStatement(ret) => {
            let expression = ret.argument.as_ref()?;
            let span = selector_return_expression(
                expression,
                selector_symbol,
                selector_value,
                scoping,
                stable_var_numbers,
            )?;
            Some(SelectorFlow::Return(span))
        }
        Statement::EmptyStatement(_) => Some(SelectorFlow::Continue),
        _ => None,
    }
}

fn selector_statements_flow(
    statements: &[Statement<'_>],
    selector_symbol: SymbolId,
    selector_value: i64,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> Option<SelectorFlow> {
    for statement in statements {
        match selector_statement_flow(
            statement,
            selector_symbol,
            selector_value,
            scoping,
            stable_var_numbers,
        )? {
            SelectorFlow::Continue => {}
            returned @ SelectorFlow::Return(_) => return Some(returned),
        }
    }
    Some(SelectorFlow::Continue)
}

#[derive(Default)]
struct SelectorLiteralCollector<'c> {
    scoping: Option<&'c Scoping>,
    selector_symbol: Option<SymbolId>,
    values: HashSet<i64>,
}

impl<'a> Visit<'a> for SelectorLiteralCollector<'_> {
    fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {
        // Do not collect selector tests from nested functions.
    }

    fn visit_binary_expression(&mut self, binary: &oxc_ast::ast::BinaryExpression<'a>) {
        if matches!(binary.operator.as_str(), "==" | "===" | "!=" | "!==") {
            let Some(scoping) = self.scoping else {
                return;
            };
            let Some(selector_symbol) = self.selector_symbol else {
                return;
            };
            let left_symbol = selector_identifier_symbol(&binary.left, scoping);
            let right_symbol = selector_identifier_symbol(&binary.right, scoping);
            let literal = if left_symbol == Some(selector_symbol) {
                expression_integer(&binary.right)
            } else if right_symbol == Some(selector_symbol) {
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

#[derive(Debug, Clone)]
pub(super) struct SelectorDispatcher {
    pub(super) params: Vec<String>,
    pub(super) param_symbols: Vec<SymbolId>,
    pub(super) returns: HashMap<i64, Span>,
}

struct SelectorDispatcherCollector<'c> {
    scoping: &'c Scoping,
    stable_var_numbers: &'c HashMap<SymbolId, i64>,
    dispatchers: HashMap<SymbolId, SelectorDispatcher>,
}

impl<'a> Visit<'a> for SelectorDispatcherCollector<'_> {
    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if !function.r#async && !function.generator && function.params.rest.is_none() {
            if let (Some(id), Some(body)) = (&function.id, &function.body) {
                if let Some(function_symbol) = id.symbol_id.get() {
                    let binding_is_stable = self
                        .scoping
                        .get_resolved_reference_ids(function_symbol)
                        .iter()
                        .all(|reference_id| {
                            let reference = self.scoping.get_reference(*reference_id);
                            !reference.is_write() && !reference.flags().is_member_write_target()
                        });

                    let params = function
                        .params
                        .items
                        .iter()
                        .map(|param| {
                            if param.initializer.is_some() {
                                return None;
                            }
                            match &param.pattern {
                                BindingPattern::BindingIdentifier(id) => {
                                    Some((id.name.to_string(), id.symbol_id.get()?))
                                }
                                _ => None,
                            }
                        })
                        .collect::<Option<Vec<_>>>();

                    if binding_is_stable && body.directives.is_empty() {
                        if let Some(params) = params {
                            if let Some((_, selector_symbol)) = params.first() {
                                let mut literals = SelectorLiteralCollector {
                                    scoping: Some(self.scoping),
                                    selector_symbol: Some(*selector_symbol),
                                    values: HashSet::new(),
                                };
                                for statement in &body.statements {
                                    literals.visit_statement(statement);
                                }

                                let mut returns = HashMap::new();
                                for value in literals.values {
                                    if let Some(SelectorFlow::Return(span)) =
                                        selector_statements_flow(
                                            &body.statements,
                                            *selector_symbol,
                                            value,
                                            self.scoping,
                                            self.stable_var_numbers,
                                        )
                                    {
                                        returns.insert(value, span);
                                    }
                                }

                                if !returns.is_empty() {
                                    self.dispatchers.insert(
                                        function_symbol,
                                        SelectorDispatcher {
                                            params: params
                                                .iter()
                                                .map(|(name, _)| name.clone())
                                                .collect(),
                                            param_symbols: params
                                                .into_iter()
                                                .map(|(_, symbol)| symbol)
                                                .collect(),
                                            returns,
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_function(self, function, flags);
    }
}

pub(super) fn collect_selector_dispatchers(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    stable_var_numbers: &HashMap<SymbolId, i64>,
) -> HashMap<SymbolId, SelectorDispatcher> {
    let mut collector = SelectorDispatcherCollector {
        scoping,
        stable_var_numbers,
        dispatchers: HashMap::new(),
    };
    collector.visit_program(program);
    collector.dispatchers
}
