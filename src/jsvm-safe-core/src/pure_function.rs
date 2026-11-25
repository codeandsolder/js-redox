//! Compile source-local scalar helpers to exact declarative binding cells.
//!
//! A local initializer captures a value at its execution point; it is not
//! a macro for reevaluating its expression after a parameter has changed.
use crate::{
    binding_facts::BindingFacts,
    value_eval::{
        eval_binary, eval_logical_left, eval_unary_value, string_literal_value,
        template_element_value, LogicalStep, Value,
    },
};
use oxc_ast::ast::{
    BindingPattern, Expression, Function, FunctionType, IdentifierReference,
    SimpleAssignmentTarget, Statement, VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::Span;
use oxc_syntax::{
    operator::{AssignmentOperator, UpdateOperator},
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use std::collections::HashMap;
use work_budget::WorkBudget;

#[derive(Debug, Clone)]
enum PureExpr {
    Value(Value),
    Cell(usize),
    Assign {
        index: usize,
        operator: AssignmentOperator,
        value: Box<Self>,
    },
    Update {
        index: usize,
        operator: UpdateOperator,
        prefix: bool,
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
    Sequence(Vec<Self>),
}

#[derive(Debug, Clone, Copy)]
enum CellKind {
    Var,
    Let,
    Const,
    /// A var redeclaration of the implicit arguments object is initialized
    /// to that object, not undefined. A primitive initializer can replace it.
    Arguments,
}

struct Cell {
    value: Option<Value>,
    mutable: bool,
}

fn charge_value(value: &Value, budget: &WorkBudget) -> Option<()> {
    let units = match value {
        Value::String(text) => text.len().saturating_add(1),
        _ => 1,
    };
    budget
        .consume(u64::try_from(units).unwrap_or(u64::MAX))
        .ok()
}

impl CellKind {
    const fn create(self) -> Cell {
        Cell {
            value: match self {
                Self::Var => Some(Value::Undefined),
                Self::Let | Self::Const | Self::Arguments => None,
            },
            mutable: !matches!(self, Self::Const),
        }
    }
}

impl Cell {
    fn read(&self, budget: &WorkBudget) -> Option<Value> {
        let value = self.value.as_ref()?;
        charge_value(value, budget)?;
        Some(value.clone())
    }

    fn write(&mut self, value: Value, budget: &WorkBudget) -> Option<Value> {
        // Writes before lexical initialization and writes to immutable
        // bindings throw. The entire pure call proof must then fail.
        if !self.mutable || self.value.is_none() {
            return None;
        }
        charge_value(&value, budget)?;
        self.value = Some(value.clone());
        Some(value)
    }
}

impl PureExpr {
    fn eval(&self, cells: &mut [Cell], budget: &WorkBudget) -> Option<Value> {
        budget.consume(1).ok()?;
        match self {
            Self::Value(value) => {
                charge_value(value, budget)?;
                Some(value.clone())
            }
            Self::Cell(index) => cells.get(*index)?.read(budget),
            Self::Assign {
                index,
                operator,
                value,
            } => {
                let value = if *operator == AssignmentOperator::Assign {
                    value.eval(cells, budget)?
                } else {
                    let previous = cells.get(*index)?.read(budget)?;
                    if let Some(logical) = operator.to_logical_operator() {
                        match eval_logical_left(logical.as_str(), previous)? {
                            LogicalStep::Value(value) => return Some(value),
                            LogicalStep::EvaluateRight => value.eval(cells, budget)?,
                        }
                    } else {
                        let right = value.eval(cells, budget)?;
                        eval_binary(operator.to_binary_operator()?.as_str(), &previous, &right)?
                    }
                };
                cells.get_mut(*index)?.write(value, budget)
            }
            Self::Update {
                index,
                operator,
                prefix,
            } => {
                let cell = cells.get_mut(*index)?;
                let previous = cell.read(budget)?.number();
                let next = match operator {
                    UpdateOperator::Increment => previous + 1.0,
                    UpdateOperator::Decrement => previous - 1.0,
                };
                cell.write(Value::Number(next), budget)?;
                Some(Value::Number(if *prefix { next } else { previous }))
            }
            Self::Unary { operator, argument } => {
                eval_unary_value(operator, &argument.eval(cells, budget)?)
            }
            Self::Binary {
                operator,
                left,
                right,
            } => {
                let left = left.eval(cells, budget)?;
                let right = right.eval(cells, budget)?;
                eval_binary(operator, &left, &right)
            }
            Self::Logical {
                operator,
                left,
                right,
            } => match eval_logical_left(operator, left.eval(cells, budget)?)? {
                LogicalStep::Value(value) => Some(value),
                LogicalStep::EvaluateRight => right.eval(cells, budget),
            },
            Self::Conditional {
                test,
                consequent,
                alternate,
            } => {
                if test.eval(cells, budget)?.truthy() {
                    consequent.eval(cells, budget)
                } else {
                    alternate.eval(cells, budget)
                }
            }
            Self::Sequence(items) => {
                let mut result = Value::Undefined;
                for item in items {
                    result = item.eval(cells, budget)?;
                }
                Some(result)
            }
        }
    }
}

struct Compiler<'c> {
    scoping: &'c Scoping,
    indices: HashMap<SymbolId, usize>,
    cells: Vec<CellKind>,
}

impl Compiler<'_> {
    fn declare(&mut self, symbol: SymbolId, kind: CellKind) -> usize {
        *self.indices.entry(symbol).or_insert_with(|| {
            let index = self.cells.len();
            self.cells.push(kind);
            index
        })
    }

    fn reference(&self, identifier: &IdentifierReference<'_>) -> Option<usize> {
        let symbol = self
            .scoping
            .get_reference(identifier.reference_id.get()?)
            .symbol_id()?;
        self.indices.get(&symbol).copied()
    }

    fn compile(&self, expr: &Expression<'_>) -> Option<PureExpr> {
        match expr {
            Expression::Identifier(id) => self.reference(id).map(PureExpr::Cell),
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
            Expression::ParenthesizedExpression(v) => self.compile(&v.expression),
            Expression::AssignmentExpression(v) => {
                let SimpleAssignmentTarget::AssignmentTargetIdentifier(target) =
                    v.left.as_simple_assignment_target()?
                else {
                    return None;
                };
                Some(PureExpr::Assign {
                    index: self.reference(target)?,
                    operator: v.operator,
                    value: Box::new(self.compile(&v.right)?),
                })
            }
            Expression::UpdateExpression(v) => {
                let SimpleAssignmentTarget::AssignmentTargetIdentifier(target) = &v.argument else {
                    return None;
                };
                Some(PureExpr::Update {
                    index: self.reference(target)?,
                    operator: v.operator,
                    prefix: v.prefix,
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
                    argument: Box::new(self.compile(&v.argument)?),
                })
            }
            Expression::BinaryExpression(v) => Some(PureExpr::Binary {
                operator: v.operator.as_str().to_string(),
                left: Box::new(self.compile(&v.left)?),
                right: Box::new(self.compile(&v.right)?),
            }),
            Expression::LogicalExpression(v) => Some(PureExpr::Logical {
                operator: v.operator.as_str().to_string(),
                left: Box::new(self.compile(&v.left)?),
                right: Box::new(self.compile(&v.right)?),
            }),
            Expression::ConditionalExpression(v) => Some(PureExpr::Conditional {
                test: Box::new(self.compile(&v.test)?),
                consequent: Box::new(self.compile(&v.consequent)?),
                alternate: Box::new(self.compile(&v.alternate)?),
            }),
            Expression::SequenceExpression(v) => Some(PureExpr::Sequence(
                v.expressions
                    .iter()
                    .map(|expr| self.compile(expr))
                    .collect::<Option<_>>()?,
            )),
            _ => None,
        }
    }
}

#[derive(Debug)]
enum Step {
    Initialize { index: usize, value: PureExpr },
    Evaluate(PureExpr),
}

#[derive(Debug)]
pub struct PureFunction {
    parameters: Vec<usize>,
    cells: Vec<CellKind>,
    steps: Vec<Step>,
    expression: PureExpr,
    declaration_span: Span,
    scope: ScopeId,
}

impl PureFunction {
    pub(super) fn evaluate(&self, args: &[Value], budget: &WorkBudget) -> Option<Value> {
        budget
            .consume(u64::try_from(self.cells.len()).unwrap_or(u64::MAX))
            .ok()?;
        let mut cells = self
            .cells
            .iter()
            .map(|kind| kind.create())
            .collect::<Vec<_>>();
        for (position, &index) in self.parameters.iter().enumerate() {
            let value = args.get(position).unwrap_or(&Value::Undefined);
            charge_value(value, budget)?;
            cells.get_mut(index)?.value = Some(value.clone());
        }
        for step in &self.steps {
            match step {
                Step::Initialize { index, value } => {
                    let value = value.eval(&mut cells, budget)?;
                    cells.get_mut(*index)?.value = Some(value);
                }
                Step::Evaluate(expr) => {
                    expr.eval(&mut cells, budget)?;
                }
            }
        }
        self.expression.eval(&mut cells, budget)
    }

    pub(super) const fn declaration_span(&self) -> Span {
        self.declaration_span
    }

    pub(super) const fn scope(&self) -> ScopeId {
        self.scope
    }
}

struct PureFunctionCollector<'c> {
    scoping: &'c Scoping,
    facts: &'c BindingFacts,
    functions: HashMap<SymbolId, PureFunction>,
}

fn cell_kind(kind: VariableDeclarationKind, name: &str) -> Option<CellKind> {
    Some(match kind {
        VariableDeclarationKind::Var if name == "arguments" => CellKind::Arguments,
        VariableDeclarationKind::Var => CellKind::Var,
        VariableDeclarationKind::Let => CellKind::Let,
        VariableDeclarationKind::Const => CellKind::Const,
        _ => return None,
    })
}

fn declare_cells(
    function: &Function<'_>,
    statements: &[Statement<'_>],
    compiler: &mut Compiler<'_>,
) -> Option<Vec<usize>> {
    let mut parameters = Vec::new();
    for parameter in &function.params.items {
        let BindingPattern::BindingIdentifier(id) = &parameter.pattern else {
            return None;
        };
        if parameter.initializer.is_some() {
            return None;
        }
        parameters.push(compiler.declare(id.symbol_id.get()?, CellKind::Var));
    }
    for statement in statements {
        match statement {
            Statement::VariableDeclaration(declaration) => {
                for declarator in &declaration.declarations {
                    let BindingPattern::BindingIdentifier(id) = &declarator.id else {
                        return None;
                    };
                    compiler.declare(
                        id.symbol_id.get()?,
                        cell_kind(declaration.kind, id.name.as_str())?,
                    );
                }
            }
            Statement::ExpressionStatement(_)
            | Statement::ReturnStatement(_)
            | Statement::EmptyStatement(_) => {}
            // Hoisted declarations after a return may override parameter
            // or var cells. Do not discard unmodeled instantiation effects.
            _ => return None,
        }
    }
    Some(parameters)
}

fn compile_body(
    statements: &[Statement<'_>],
    compiler: &Compiler<'_>,
) -> Option<(Vec<Step>, PureExpr)> {
    let mut steps = Vec::new();
    for statement in statements {
        match statement {
            Statement::VariableDeclaration(declaration) => {
                for declarator in &declaration.declarations {
                    let BindingPattern::BindingIdentifier(id) = &declarator.id else {
                        return None;
                    };
                    if declaration.kind == VariableDeclarationKind::Var && declarator.init.is_none()
                    {
                        continue;
                    }
                    let value = if let Some(init) = &declarator.init {
                        compiler.compile(init)?
                    } else {
                        PureExpr::Value(Value::Undefined)
                    };
                    let index = *compiler.indices.get(&id.symbol_id.get()?)?;
                    steps.push(Step::Initialize { index, value });
                }
            }
            Statement::ExpressionStatement(statement) => {
                steps.push(Step::Evaluate(compiler.compile(&statement.expression)?));
            }
            Statement::ReturnStatement(ret) => {
                let result = if let Some(argument) = &ret.argument {
                    compiler.compile(argument)?
                } else {
                    PureExpr::Value(Value::Undefined)
                };
                return Some((steps, result));
            }
            Statement::EmptyStatement(_) => {}
            _ => return None,
        }
    }
    Some((steps, PureExpr::Value(Value::Undefined)))
}

fn proven_pure_function(
    function: &Function<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<(SymbolId, PureFunction)> {
    if function.r#type != FunctionType::FunctionDeclaration
        || function.r#async
        || function.generator
        || function.params.rest.is_some()
    {
        return None;
    }
    let symbol = function.id.as_ref()?.symbol_id.get()?;
    let scope = function.scope_id.get()?;
    if !facts.hoisted_callable_declaration(scoping, symbol, scope) {
        return None;
    }
    let body = function.body.as_ref()?;
    let mut compiler = Compiler {
        scoping,
        indices: HashMap::new(),
        cells: Vec::new(),
    };
    let parameters = declare_cells(function, &body.statements, &mut compiler)?;
    let (steps, expression) = compile_body(&body.statements, &compiler)?;
    Some((
        symbol,
        PureFunction {
            parameters,
            cells: compiler.cells,
            steps,
            expression,
            declaration_span: function.span,
            scope,
        },
    ))
}

impl<'a> Visit<'a> for PureFunctionCollector<'_> {
    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        if let Some((symbol, pure)) = proven_pure_function(function, self.scoping, self.facts) {
            self.functions.insert(symbol, pure);
        }
        walk::walk_function(self, function, flags);
    }
}

pub fn collect_pure_functions(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> HashMap<SymbolId, PureFunction> {
    let mut collector = PureFunctionCollector {
        scoping,
        facts,
        functions: HashMap::new(),
    };
    collector.visit_program(program);
    collector.functions
}
