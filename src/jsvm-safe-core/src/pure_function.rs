use crate::value_eval::{
    eval_binary, eval_logical_left, eval_unary_value, string_literal_value, template_element_value,
    LogicalStep, Value,
};
use oxc_ast::ast::{BindingPattern, Expression, Statement, VariableDeclarationKind};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::Span;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::HashMap;

#[derive(Debug, Clone)]
enum PureExpr {
    Value(Value),
    Param(usize),
    AssignParam {
        index: usize,
        value: Box<Self>,
    },
    Unary {
        operator: String,
        argument: Box<Self>,
    },
    Binary {
        operator: String,
        left: Box<Self>,
        right: Box<Self>,
    },
    Logical {
        operator: String,
        left: Box<Self>,
        right: Box<Self>,
    },
    Conditional {
        test: Box<Self>,
        consequent: Box<Self>,
        alternate: Box<Self>,
    },
}

impl PureExpr {
    fn is_effect_free(&self) -> bool {
        match self {
            Self::Value(_) | Self::Param(_) => true,
            Self::AssignParam { .. } => false,
            Self::Unary { argument, .. } => argument.is_effect_free(),
            Self::Binary { left, right, .. } | Self::Logical { left, right, .. } => {
                left.is_effect_free() && right.is_effect_free()
            }
            Self::Conditional {
                test,
                consequent,
                alternate,
            } => test.is_effect_free() && consequent.is_effect_free() && alternate.is_effect_free(),
        }
    }

    fn eval(&self, params: &mut [Value]) -> Option<Value> {
        match self {
            Self::Value(value) => Some(value.clone()),
            Self::Param(index) => params.get(*index).cloned(),
            Self::AssignParam { index, value } => {
                let value = value.eval(params)?;
                *params.get_mut(*index)? = value.clone();
                Some(value)
            }
            Self::Unary { operator, argument } => {
                eval_unary_value(operator, argument.eval(params)?)
            }
            Self::Binary {
                operator,
                left,
                right,
            } => {
                let left = left.eval(params)?;
                let right = right.eval(params)?;
                eval_binary(operator, left, right)
            }
            Self::Logical {
                operator,
                left,
                right,
            } => match eval_logical_left(operator, left.eval(params)?)? {
                LogicalStep::Value(value) => Some(value),
                LogicalStep::EvaluateRight => right.eval(params),
            },
            Self::Conditional {
                test,
                consequent,
                alternate,
            } => {
                if test.eval(params)?.truthy() {
                    consequent.eval(params)
                } else {
                    alternate.eval(params)
                }
            }
        }
    }
}

fn compile_pure_expr(
    expr: &Expression<'_>,
    params: &HashMap<String, usize>,
    locals: &HashMap<String, PureExpr>,
) -> Option<PureExpr> {
    match expr {
        Expression::Identifier(id) => locals
            .get(id.name.as_str())
            .cloned()
            .or_else(|| params.get(id.name.as_str()).copied().map(PureExpr::Param)),
        Expression::StringLiteral(v) => {
            string_literal_value(v).map(|value| PureExpr::Value(Value::String(value)))
        }
        Expression::NumericLiteral(v) => Some(PureExpr::Value(Value::Number(v.value))),
        Expression::BooleanLiteral(v) => Some(PureExpr::Value(Value::Bool(v.value))),
        Expression::NullLiteral(_) => Some(PureExpr::Value(Value::Null)),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .and_then(template_element_value)
            .map(|value| PureExpr::Value(Value::String(value))),
        Expression::ParenthesizedExpression(v) => compile_pure_expr(&v.expression, params, locals),
        Expression::AssignmentExpression(v) if v.operator.as_str() == "=" => {
            let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) = &v.left else {
                return None;
            };
            Some(PureExpr::AssignParam {
                index: *params.get(target.name.as_str())?,
                value: Box::new(compile_pure_expr(&v.right, params, locals)?),
            })
        }
        Expression::UnaryExpression(v)
            if matches!(
                v.operator.as_str(),
                "!" | "+" | "-" | "~" | "void" | "typeof"
            ) =>
        {
            Some(PureExpr::Unary {
                operator: v.operator.as_str().to_string(),
                argument: Box::new(compile_pure_expr(&v.argument, params, locals)?),
            })
        }
        Expression::BinaryExpression(v)
            if matches!(
                v.operator.as_str(),
                "+" | "-"
                    | "*"
                    | "/"
                    | "%"
                    | "**"
                    | "<<"
                    | ">>"
                    | ">>>"
                    | "|"
                    | "^"
                    | "&"
                    | "==="
                    | "!=="
                    | "=="
                    | "!="
                    | "<"
                    | "<="
                    | ">"
                    | ">="
            ) =>
        {
            Some(PureExpr::Binary {
                operator: v.operator.as_str().to_string(),
                left: Box::new(compile_pure_expr(&v.left, params, locals)?),
                right: Box::new(compile_pure_expr(&v.right, params, locals)?),
            })
        }
        Expression::LogicalExpression(v) => Some(PureExpr::Logical {
            operator: v.operator.as_str().to_string(),
            left: Box::new(compile_pure_expr(&v.left, params, locals)?),
            right: Box::new(compile_pure_expr(&v.right, params, locals)?),
        }),
        Expression::ConditionalExpression(v) => Some(PureExpr::Conditional {
            test: Box::new(compile_pure_expr(&v.test, params, locals)?),
            consequent: Box::new(compile_pure_expr(&v.consequent, params, locals)?),
            alternate: Box::new(compile_pure_expr(&v.alternate, params, locals)?),
        }),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct PureFunction {
    param_count: usize,
    expression: PureExpr,
    declaration_span: Option<Span>,
}

impl PureFunction {
    pub(super) fn evaluate(&self, args: &[Value]) -> Option<Value> {
        let mut params = vec![Value::Undefined; self.param_count];
        for (target, value) in params.iter_mut().zip(args.iter().cloned()) {
            *target = value;
        }
        self.expression.eval(&mut params)
    }

    pub(super) const fn declaration_span(&self) -> Option<Span> {
        self.declaration_span
    }
}

struct PureFunctionCollector<'c> {
    scoping: &'c Scoping,
    functions: HashMap<SymbolId, PureFunction>,
}

impl<'a> Visit<'a> for PureFunctionCollector<'_> {
    fn visit_function(&mut self, f: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if !f.r#async && !f.generator && f.params.rest.is_none() {
            if let (Some(id), Some(body)) = (&f.id, &f.body) {
                if let Some(symbol) = id.symbol_id.get() {
                    let immutable =
                        self.scoping.get_resolved_reference_ids(symbol).iter().all(
                            |reference_id| !self.scoping.get_reference(*reference_id).is_write(),
                        );
                    if immutable {
                        let mut params = HashMap::new();
                        let mut valid_params = true;
                        for (index, parameter) in f.params.items.iter().enumerate() {
                            let BindingPattern::BindingIdentifier(parameter_id) =
                                &parameter.pattern
                            else {
                                valid_params = false;
                                break;
                            };
                            if parameter.initializer.is_some()
                                || params
                                    .insert(parameter_id.name.to_string(), index)
                                    .is_some()
                            {
                                valid_params = false;
                                break;
                            }
                        }
                        if valid_params {
                            let mut locals = HashMap::new();
                            let mut expression = None;
                            let mut valid_body = !body.statements.is_empty();
                            for (statement_index, statement) in body.statements.iter().enumerate() {
                                match statement {
                                    Statement::VariableDeclaration(declaration)
                                        if declaration.kind == VariableDeclarationKind::Var
                                            && statement_index + 1 < body.statements.len() =>
                                    {
                                        for declarator in &declaration.declarations {
                                            let BindingPattern::BindingIdentifier(identifier) =
                                                &declarator.id
                                            else {
                                                valid_body = false;
                                                break;
                                            };
                                            if params.contains_key(identifier.name.as_str())
                                                || locals.contains_key(identifier.name.as_str())
                                            {
                                                valid_body = false;
                                                break;
                                            }
                                            let Some(initializer) = &declarator.init else {
                                                valid_body = false;
                                                break;
                                            };
                                            let Some(compiled) =
                                                compile_pure_expr(initializer, &params, &locals)
                                            else {
                                                valid_body = false;
                                                break;
                                            };
                                            if !compiled.is_effect_free() {
                                                valid_body = false;
                                                break;
                                            }
                                            locals.insert(identifier.name.to_string(), compiled);
                                        }
                                        if !valid_body {
                                            break;
                                        }
                                    }
                                    Statement::ReturnStatement(ret)
                                        if statement_index + 1 == body.statements.len() =>
                                    {
                                        let Some(argument) = &ret.argument else {
                                            valid_body = false;
                                            break;
                                        };
                                        expression = compile_pure_expr(argument, &params, &locals);
                                        if expression.is_none() {
                                            valid_body = false;
                                        }
                                    }
                                    _ => {
                                        valid_body = false;
                                        break;
                                    }
                                }
                            }
                            if valid_body {
                                if let Some(expression) = expression {
                                    self.functions.insert(
                                        symbol,
                                        PureFunction {
                                            param_count: f.params.items.len(),
                                            expression,
                                            declaration_span: (f.r#type
                                                == oxc_ast::ast::FunctionType::FunctionDeclaration)
                                                .then_some(f.span),
                                        },
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_function(self, f, flags);
    }
}

pub fn collect_pure_functions(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, PureFunction> {
    let mut collector = PureFunctionCollector {
        scoping,
        functions: HashMap::new(),
    };
    collector.visit_program(program);
    collector.functions
}
