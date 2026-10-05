use crate::value_eval::{eval_binary, js_to_int32, Value};
use oxc_ast::ast::{BindingPattern, Expression, Statement};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::Span;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::HashMap;

#[derive(Debug, Clone)]
enum PureExpr {
    Value(Value),
    Param(usize),
    Unary {
        operator: String,
        argument: Box<PureExpr>,
    },
    Binary {
        operator: String,
        left: Box<PureExpr>,
        right: Box<PureExpr>,
    },
    Logical {
        operator: String,
        left: Box<PureExpr>,
        right: Box<PureExpr>,
    },
    Conditional {
        test: Box<PureExpr>,
        consequent: Box<PureExpr>,
        alternate: Box<PureExpr>,
    },
}

impl PureExpr {
    fn eval(&self, args: &[Value]) -> Option<Value> {
        match self {
            Self::Value(value) => Some(value.clone()),
            Self::Param(index) => args.get(*index).cloned(),
            Self::Unary { operator, argument } => {
                let value = argument.eval(args)?;
                match operator.as_str() {
                    "!" => Some(Value::Bool(!value.truthy())),
                    "+" => value.number().map(Value::Number),
                    "-" => value.number().map(|n| Value::Number(-n)),
                    "~" => value
                        .number()
                        .map(|n| Value::Number((!js_to_int32(n)) as f64)),
                    "void" => Some(Value::Undefined),
                    "typeof" => Some(Value::String(
                        match value {
                            Value::String(_) => "string",
                            Value::Number(_) => "number",
                            Value::Bool(_) => "boolean",
                            Value::Null => "object",
                            Value::Undefined => "undefined",
                        }
                        .to_string(),
                    )),
                    _ => None,
                }
            }
            Self::Binary {
                operator,
                left,
                right,
            } => eval_binary(operator, left.eval(args)?, right.eval(args)?),
            Self::Logical {
                operator,
                left,
                right,
            } => {
                let left = left.eval(args)?;
                match operator.as_str() {
                    "&&" => {
                        if left.truthy() {
                            right.eval(args)
                        } else {
                            Some(left)
                        }
                    }
                    "||" => {
                        if left.truthy() {
                            Some(left)
                        } else {
                            right.eval(args)
                        }
                    }
                    "??" => {
                        if matches!(left, Value::Null | Value::Undefined) {
                            right.eval(args)
                        } else {
                            Some(left)
                        }
                    }
                    _ => None,
                }
            }
            Self::Conditional {
                test,
                consequent,
                alternate,
            } => {
                if test.eval(args)?.truthy() {
                    consequent.eval(args)
                } else {
                    alternate.eval(args)
                }
            }
        }
    }
}

fn compile_pure_expr(expr: &Expression<'_>, params: &HashMap<String, usize>) -> Option<PureExpr> {
    match expr {
        Expression::Identifier(id) => params.get(id.name.as_str()).copied().map(PureExpr::Param),
        Expression::StringLiteral(v) => Some(PureExpr::Value(Value::String(v.value.to_string()))),
        Expression::NumericLiteral(v) => Some(PureExpr::Value(Value::Number(v.value))),
        Expression::BooleanLiteral(v) => Some(PureExpr::Value(Value::Bool(v.value))),
        Expression::NullLiteral(_) => Some(PureExpr::Value(Value::Null)),
        Expression::TemplateLiteral(v) if v.expressions.is_empty() => v.quasis.first().map(|q| {
            PureExpr::Value(Value::String(
                q.value.cooked.as_ref().unwrap_or(&q.value.raw).to_string(),
            ))
        }),
        Expression::ParenthesizedExpression(v) => compile_pure_expr(&v.expression, params),
        Expression::UnaryExpression(v)
            if matches!(
                v.operator.as_str(),
                "!" | "+" | "-" | "~" | "void" | "typeof"
            ) =>
        {
            Some(PureExpr::Unary {
                operator: v.operator.as_str().to_string(),
                argument: Box::new(compile_pure_expr(&v.argument, params)?),
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
                left: Box::new(compile_pure_expr(&v.left, params)?),
                right: Box::new(compile_pure_expr(&v.right, params)?),
            })
        }
        Expression::LogicalExpression(v) => Some(PureExpr::Logical {
            operator: v.operator.as_str().to_string(),
            left: Box::new(compile_pure_expr(&v.left, params)?),
            right: Box::new(compile_pure_expr(&v.right, params)?),
        }),
        Expression::ConditionalExpression(v) => Some(PureExpr::Conditional {
            test: Box::new(compile_pure_expr(&v.test, params)?),
            consequent: Box::new(compile_pure_expr(&v.consequent, params)?),
            alternate: Box::new(compile_pure_expr(&v.alternate, params)?),
        }),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub(super) struct PureFunction {
    arity: usize,
    expression: PureExpr,
    declaration_span: Option<Span>,
}

impl PureFunction {
    pub(super) fn evaluate(&self, args: &[Value]) -> Option<Value> {
        (args.len() == self.arity).then_some(())?;
        self.expression.eval(args)
    }

    pub(super) fn declaration_span(&self) -> Option<Span> {
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
                    if immutable && body.statements.len() == 1 {
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
                            if let Statement::ReturnStatement(ret) = &body.statements[0] {
                                if let Some(argument) = &ret.argument {
                                    if let Some(expression) = compile_pure_expr(argument, &params) {
                                        self.functions.insert(
                                            symbol,
                                            PureFunction {
                                                arity: f.params.items.len(),
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
        }
        walk::walk_function(self, f, flags);
    }
}

pub(super) fn collect_pure_functions(
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
