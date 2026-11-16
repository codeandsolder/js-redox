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
                eval_unary_value(operator, &argument.eval(params)?)
            }
            Self::Binary {
                operator,
                left,
                right,
            } => {
                let left = left.eval(params)?;
                let right = right.eval(params)?;
                eval_binary(operator, &left, &right)
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

/// Compile only simple positional bindings; unsupported parameters cannot
/// be modeled by the pure evaluator without additional call-time semantics.
fn pure_parameter_bindings(
    function: &oxc_ast::ast::Function<'_>,
) -> Option<HashMap<String, usize>> {
    if function.r#async || function.generator || function.params.rest.is_some() {
        return None;
    }
    let mut params = HashMap::new();
    for (index, parameter) in function.params.items.iter().enumerate() {
        let BindingPattern::BindingIdentifier(parameter_id) = &parameter.pattern else {
            return None;
        };
        if parameter.initializer.is_some()
            || params
                .insert(parameter_id.name.to_string(), index)
                .is_some()
        {
            return None;
        }
    }
    Some(params)
}

/// Evaluate local declarations in source order, admitting only effect-free
/// initializers before a final return. A rejected statement rejects the whole
/// candidate, not merely the affected local binding.
fn pure_function_body(
    statements: &[Statement<'_>],
    params: &HashMap<String, usize>,
) -> Option<PureExpr> {
    let mut locals = HashMap::new();
    let mut expression = None;
    if statements.is_empty() {
        return None;
    }
    for (index, statement) in statements.iter().enumerate() {
        match statement {
            Statement::VariableDeclaration(declaration)
                if declaration.kind == VariableDeclarationKind::Var
                    && index + 1 < statements.len() =>
            {
                for declarator in &declaration.declarations {
                    let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                        return None;
                    };
                    if params.contains_key(identifier.name.as_str())
                        || locals.contains_key(identifier.name.as_str())
                    {
                        return None;
                    }
                    let compiled = compile_pure_expr(declarator.init.as_ref()?, params, &locals)?;
                    if !compiled.is_effect_free() {
                        return None;
                    }
                    locals.insert(identifier.name.to_string(), compiled);
                }
            }
            Statement::ReturnStatement(ret) if index + 1 == statements.len() => {
                expression = Some(compile_pure_expr(ret.argument.as_ref()?, params, &locals)?);
            }
            _ => return None,
        }
    }
    expression
}

fn proven_pure_function(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> Option<(SymbolId, PureFunction)> {
    let id = function.id.as_ref()?;
    let body = function.body.as_ref()?;
    let symbol = id.symbol_id.get()?;
    if scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .any(|reference_id| scoping.get_reference(*reference_id).is_write())
    {
        return None;
    }
    let params = pure_parameter_bindings(function)?;
    let expression = pure_function_body(&body.statements, &params)?;
    Some((
        symbol,
        PureFunction {
            param_count: function.params.items.len(),
            expression,
            declaration_span: (function.r#type == oxc_ast::ast::FunctionType::FunctionDeclaration)
                .then_some(function.span),
        },
    ))
}

impl<'a> Visit<'a> for PureFunctionCollector<'_> {
    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        if let Some((symbol, pure)) = proven_pure_function(function, self.scoping) {
            self.functions.insert(symbol, pure);
        }
        walk::walk_function(self, function, flags);
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
