//! Flow-local facts about freshly constructed own data properties.
//!
//! Whole-lifetime confinement is useful for captured objects, but it is not
//! required for reads before a possible escape. This analysis walks actual
//! evaluation prefixes. Unknown evaluation invalidates reaching facts;
//! branch joins keep only facts common to the reaching normal paths. Deferred
//! bodies and unsupported control regions are analyzed from an empty state.
use crate::binding_facts::BindingFacts;
use crate::value_eval::{
    eval, eval_binary, eval_logical_left, eval_unary_value, is_prototype_setter,
    literal_property_key, same_value, LogicalStep, Value,
};
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, Declaration, Expression,
    IdentifierReference, ObjectPropertyKind, Program, PropertyKind, Statement, VariableDeclaration,
    VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::symbol::SymbolId;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use work_budget::{BudgetExceeded, WorkBudget};

type OwnData = HashMap<String, Option<Value>>;
type Environment = HashMap<SymbolId, Fact>;

#[derive(Clone)]
enum Fact {
    Primitive(Value),
    Data(Rc<OwnData>),
}

impl Fact {
    fn join(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Primitive(a), Self::Primitive(b)) => same_primitive(a, b).then(|| self.clone()),
            (Self::Data(a), Self::Data(b)) if Rc::ptr_eq(a, b) => Some(self.clone()),
            (Self::Data(a), Self::Data(b)) => {
                // Neither identity nor non-shared properties are proven at
                // the join. Retain only own data guaranteed on both paths.
                // A differing value is still a non-effectful own-data read.
                let (smaller, larger) = if a.len() <= b.len() { (a, b) } else { (b, a) };
                let common = smaller
                    .iter()
                    .filter_map(|(key, left)| {
                        let right = larger.get(key)?;
                        let value = left
                            .as_ref()
                            .filter(|value| {
                                right
                                    .as_ref()
                                    .is_some_and(|other| same_primitive(value, other))
                            })
                            .cloned();
                        Some((key.clone(), value))
                    })
                    .collect();
                Some(Self::Data(Rc::new(common)))
            }
            _ => None,
        }
    }

    fn truthy(&self) -> bool {
        match self {
            Self::Primitive(value) => value.truthy(),
            Self::Data(_) => true,
        }
    }
}

fn same_primitive(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Number(a), Value::Number(b)) => a.to_bits() == b.to_bits(),
        _ => same_value(left, right),
    }
}

#[derive(Default)]
struct Evaluation {
    fact: Option<Fact>,
    inert: bool,
}

impl Evaluation {
    fn primitive(value: Value, inert: bool) -> Self {
        Self {
            fact: Some(Fact::Primitive(value)),
            inert,
        }
    }

    fn data(data: OwnData, inert: bool) -> Self {
        Self {
            fact: Some(Fact::Data(Rc::new(data))),
            inert,
        }
    }

    fn primitive_value(&self) -> Option<&Value> {
        match &self.fact {
            Some(Fact::Primitive(value)) => Some(value),
            _ => None,
        }
    }

    fn unknown_inert() -> Self {
        Self {
            fact: None,
            inert: true,
        }
    }
}

fn intersect(left: &mut Environment, right: &Environment) {
    left.retain(|symbol, fact| {
        let Some(joined) = right.get(symbol).and_then(|other| fact.join(other)) else {
            return false;
        };
        *fact = joined;
        true
    });
}

#[derive(Default)]
pub(crate) struct FreshDataReads {
    values: HashMap<(u32, u32), Value>,
}

impl FreshDataReads {
    pub(crate) fn analyze(
        program: &Program<'_>,
        scoping: &Scoping,
        bindings: &BindingFacts,
        budget: &WorkBudget,
    ) -> Result<Self, BudgetExceeded> {
        let mut analyzer = Analyzer {
            scoping,
            bindings,
            ambient_root: !program.source_type.is_module(),
            reads: Self::default(),
            visited_lists: HashSet::new(),
            budget,
            failure: None,
        };
        analyzer.visit_program(program);
        analyzer.failure.map_or(Ok(analyzer.reads), Err)
    }

    pub(crate) fn get(&self, span: Span) -> Option<&Value> {
        self.values.get(&(span.start, span.end))
    }
}

struct Analyzer<'c> {
    scoping: &'c Scoping,
    bindings: &'c BindingFacts,
    ambient_root: bool,
    reads: FreshDataReads,
    visited_lists: HashSet<(u32, u32)>,
    budget: &'c WorkBudget,
    failure: Option<BudgetExceeded>,
}

impl Analyzer<'_> {
    fn checkpoint(&mut self) -> bool {
        if self.failure.is_some() {
            return false;
        }
        if let Err(failure) = self.budget.checkpoint() {
            self.failure = Some(failure);
            false
        } else {
            true
        }
    }

    fn barrier(environment: &mut Environment) -> Evaluation {
        environment.clear();
        Evaluation::default()
    }

    fn lexical_reference(&self, identifier: &IdentifierReference<'_>) -> Option<SymbolId> {
        let reference = identifier.reference_id.get()?;
        let symbol = crate::statically_resolved_symbol(self.scoping, reference)?;
        if self.ambient_root
            && self.scoping.symbol_scope_id(symbol) == self.scoping.root_scope_id()
            && !self.scoping.symbol_flags(symbol).is_block_scoped()
        {
            return None;
        }
        self.bindings
            .proves_reference_identity(
                self.scoping,
                symbol,
                self.scoping.get_reference(reference).scope_id(),
            )
            .then_some(symbol)
    }

    fn identifier(
        &self,
        identifier: &IdentifierReference<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(symbol) = self.lexical_reference(identifier) else {
            return Self::barrier(environment);
        };
        let Some(reference) = identifier.reference_id.get() else {
            return Self::barrier(environment);
        };
        if !crate::reference_is_statically_resolved_read(self.scoping, reference, symbol) {
            return Self::barrier(environment);
        }
        if let Some(fact) = environment.get(&symbol) {
            return Evaluation {
                fact: Some(fact.clone()),
                inert: true,
            };
        }
        let scope = self.scoping.get_reference(reference).scope_id();
        Evaluation {
            fact: None,
            inert: self.bindings.proves_value_initialized(
                self.scoping,
                symbol,
                scope,
                identifier.span,
            ) || self.bindings.proves_initialized(
                self.scoping,
                symbol,
                scope,
                identifier.span,
            ),
        }
    }

    fn member(
        &mut self,
        span: Span,
        object: Evaluation,
        key: Evaluation,
        environment: &mut Environment,
    ) -> Evaluation {
        // If ToPropertyKey or evaluation of the key can execute user code,
        // even a previously obtained receiver may have changed in the meantime.
        if !key.inert {
            return Self::barrier(environment);
        }
        let Some(name) = key.primitive_value().and_then(Value::js_string) else {
            return Self::barrier(environment);
        };
        let Some(Fact::Data(data)) = object.fact else {
            return Self::barrier(environment);
        };
        let Some(value) = data.get(&name) else {
            return Self::barrier(environment);
        };
        if let Some(value) = value {
            if object.inert {
                self.reads
                    .values
                    .insert((span.start, span.end), value.clone());
            }
            Evaluation::primitive(value.clone(), object.inert)
        } else {
            Evaluation {
                fact: None,
                inert: object.inert,
            }
        }
    }

    fn expression(
        &mut self,
        expression: &Expression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        if !self.checkpoint() {
            return Self::barrier(environment);
        }
        match expression {
            Expression::Identifier(identifier) => self.identifier(identifier, environment),
            Expression::ParenthesizedExpression(paren) => {
                self.expression(&paren.expression, environment)
            }
            Expression::StaticMemberExpression(member) if !member.optional => {
                let object = self.expression(&member.object, environment);
                let key =
                    Evaluation::primitive(Value::String(member.property.name.to_string()), true);
                self.member(member.span, object, key, environment)
            }
            Expression::ComputedMemberExpression(member) if !member.optional => {
                let object = self.expression(&member.object, environment);
                let key = self.expression(&member.expression, environment);
                self.member(member.span, object, key, environment)
            }
            Expression::SequenceExpression(sequence) => {
                let mut result = Evaluation::unknown_inert();
                for item in &sequence.expressions {
                    let mut next = self.expression(item, environment);
                    next.inert &= result.inert;
                    result = next;
                }
                result
            }
            Expression::UnaryExpression(unary) => {
                let operator = unary.operator.as_str();
                if operator == "delete" {
                    return Self::barrier(environment);
                }
                let argument = self.expression(&unary.argument, environment);
                let value = argument
                    .primitive_value()
                    .and_then(|value| eval_unary_value(operator, value));
                if let Some(value) = value {
                    return Evaluation::primitive(value, argument.inert);
                }
                match operator {
                    "!" => argument.fact.as_ref().map_or(
                        Evaluation {
                            fact: None,
                            inert: argument.inert,
                        },
                        |value| Evaluation::primitive(Value::Bool(!value.truthy()), argument.inert),
                    ),
                    "void" => Evaluation::primitive(Value::Undefined, argument.inert),
                    "typeof" => Evaluation {
                        fact: None,
                        inert: argument.inert,
                    },
                    _ => Self::barrier(environment),
                }
            }
            Expression::BinaryExpression(binary) => {
                let left = self.expression(&binary.left, environment);
                let right = self.expression(&binary.right, environment);
                let operator = binary.operator.as_str();
                if let (Some(left_value), Some(right_value)) =
                    (left.primitive_value(), right.primitive_value())
                {
                    if let Some(value) = eval_binary(operator, left_value, right_value) {
                        return Evaluation::primitive(value, left.inert && right.inert);
                    }
                }
                if matches!(operator, "===" | "!==") {
                    Evaluation {
                        fact: None,
                        inert: left.inert && right.inert,
                    }
                } else {
                    Self::barrier(environment)
                }
            }
            Expression::LogicalExpression(logical) => {
                let left = self.expression(&logical.left, environment);
                let decision = match &left.fact {
                    Some(Fact::Primitive(value)) => {
                        eval_logical_left(logical.operator.as_str(), value.clone())
                            .map(|step| matches!(step, LogicalStep::EvaluateRight))
                    }
                    Some(Fact::Data(_)) => Some(logical.operator.as_str() == "&&"),
                    None => None,
                };
                match decision {
                    Some(false) => left,
                    Some(true) => {
                        let mut right = self.expression(&logical.right, environment);
                        right.inert &= left.inert;
                        right
                    }
                    None => {
                        let skip = environment.clone();
                        let right = self.expression(&logical.right, environment);
                        intersect(environment, &skip);
                        Evaluation {
                            fact: None,
                            inert: left.inert && right.inert,
                        }
                    }
                }
            }
            Expression::ConditionalExpression(conditional) => {
                let test = self.expression(&conditional.test, environment);
                if let Some(fact) = &test.fact {
                    let selected = if fact.truthy() {
                        &conditional.consequent
                    } else {
                        &conditional.alternate
                    };
                    let mut result = self.expression(selected, environment);
                    result.inert &= test.inert;
                    return result;
                }
                let mut other = environment.clone();
                let left = self.expression(&conditional.consequent, environment);
                let right = self.expression(&conditional.alternate, &mut other);
                intersect(environment, &other);
                Evaluation {
                    fact: left
                        .fact
                        .as_ref()
                        .zip(right.fact.as_ref())
                        .and_then(|(left, right)| left.join(right)),
                    inert: test.inert && left.inert && right.inert,
                }
            }
            Expression::ArrayExpression(array) => {
                let mut data = OwnData::new();
                let mut inert = true;
                let mut known_index = true;
                for (index, element) in array.elements.iter().enumerate() {
                    match element {
                        ArrayExpressionElement::Elision(_) => {}
                        ArrayExpressionElement::SpreadElement(spread) => {
                            self.expression(&spread.argument, environment);
                            environment.clear();
                            known_index = false;
                            inert = false;
                        }
                        _ => {
                            let Some(value) = element.as_expression() else {
                                return Self::barrier(environment);
                            };
                            let result = self.expression(value, environment);
                            inert &= result.inert;
                            if known_index {
                                data.insert(index.to_string(), result.primitive_value().cloned());
                            }
                        }
                    }
                }
                if known_index {
                    if let Ok(length) = u32::try_from(array.elements.len()) {
                        data.insert("length".into(), Some(Value::Number(f64::from(length))));
                    }
                }
                Evaluation::data(data, inert)
            }
            Expression::ObjectExpression(object) => {
                let mut data = OwnData::new();
                let mut inert = true;
                for item in &object.properties {
                    match item {
                        ObjectPropertyKind::SpreadProperty(spread) => {
                            self.expression(&spread.argument, environment);
                            environment.clear();
                            data.clear();
                            inert = false;
                        }
                        ObjectPropertyKind::ObjectProperty(property) => {
                            let key = if property.computed {
                                let result = property
                                    .key
                                    .as_expression()
                                    .map(|key| self.expression(key, environment))
                                    .unwrap_or_default();
                                inert &= result.inert;
                                let key = result.primitive_value().and_then(Value::js_string);
                                if key.is_none() {
                                    environment.clear();
                                    inert = false;
                                }
                                key
                            } else {
                                literal_property_key(&property.key)
                            };
                            let value = self.expression(&property.value, environment);
                            inert &= value.inert;
                            let Some(key) = key else {
                                data.clear();
                                continue;
                            };
                            if is_prototype_setter(property, &key) {
                                continue;
                            }
                            if property.kind == PropertyKind::Init {
                                data.insert(key, value.primitive_value().cloned());
                            } else {
                                data.remove(&key);
                            }
                        }
                    }
                }
                Evaluation::data(data, inert)
            }
            Expression::CallExpression(call) => {
                // Callee lookup precedes argument evaluation. An unknown
                // getter/global lookup can mutate anything visible to it.
                self.expression(&call.callee, environment);
                self.arguments(&call.arguments, environment);
                Self::barrier(environment)
            }
            Expression::NewExpression(call) => {
                self.expression(&call.callee, environment);
                self.arguments(&call.arguments, environment);
                Self::barrier(environment)
            }
            Expression::AssignmentExpression(assignment) if assignment.operator.as_str() == "=" => {
                let AssignmentTarget::AssignmentTargetIdentifier(identifier) = &assignment.left
                else {
                    return Self::barrier(environment);
                };
                let Some(symbol) = self.lexical_reference(identifier) else {
                    return Self::barrier(environment);
                };
                let flags = self.scoping.symbol_flags(symbol);
                if !flags.is_block_scoped() || flags.is_const_variable() {
                    return Self::barrier(environment);
                }
                let mut value = self.expression(&assignment.right, environment);
                if let Some(fact) = &value.fact {
                    environment.insert(symbol, fact.clone());
                } else {
                    environment.remove(&symbol);
                }
                value.inert = false;
                value
            }
            Expression::FunctionExpression(_) | Expression::ArrowFunctionExpression(_) => {
                Evaluation::unknown_inert()
            }
            _ => eval(expression).map_or_else(
                || Self::barrier(environment),
                |value| Evaluation::primitive(value, true),
            ),
        }
    }

    fn arguments(&mut self, arguments: &[Argument<'_>], environment: &mut Environment) {
        for argument in arguments {
            if let Argument::SpreadElement(spread) = argument {
                self.expression(&spread.argument, environment);
                environment.clear();
            } else if let Some(expression) = argument.as_expression() {
                self.expression(expression, environment);
            }
        }
    }

    fn declaration(
        &mut self,
        declaration: &VariableDeclaration<'_>,
        environment: &mut Environment,
    ) {
        for declarator in &declaration.declarations {
            if declaration.kind == VariableDeclarationKind::Var {
                // ResolveBinding for var initialization precedes its RHS;
                // a with-environment or ambient global can be observable.
                // Do not carry allocation facts across that lookup.
                if declarator.init.is_none() {
                    continue;
                }
                environment.clear();
            }
            let value = declarator
                .init
                .as_ref()
                .map(|init| self.expression(init, environment))
                .unwrap_or_else(|| Evaluation::primitive(Value::Undefined, true));
            let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                environment.clear();
                continue;
            };
            let Some(symbol) = identifier.symbol_id.get() else {
                environment.clear();
                continue;
            };
            if !matches!(
                declaration.kind,
                VariableDeclarationKind::Let | VariableDeclarationKind::Const
            ) {
                // Var initialization can write through global accessors or
                // mapped arguments. It is not a lexical allocation proof.
                environment.clear();
                continue;
            }
            if let Some(fact) = value.fact {
                environment.insert(symbol, fact);
            } else {
                environment.remove(&symbol);
            }
        }
    }

    fn statements(&mut self, statements: &[Statement<'_>], environment: &mut Environment) -> bool {
        if let (Some(first), Some(last)) = (statements.first(), statements.last()) {
            self.visited_lists
                .insert((first.span().start, last.span().end));
        }
        for statement in statements {
            if !self.statement(statement, environment) {
                environment.clear();
                return false;
            }
        }
        true
    }

    fn statement(&mut self, statement: &Statement<'_>, environment: &mut Environment) -> bool {
        if !self.checkpoint() {
            return false;
        }
        match statement {
            Statement::VariableDeclaration(declaration) => {
                self.declaration(declaration, environment)
            }
            Statement::ExportDeclaration(export) => {
                if let Declaration::VariableDeclaration(declaration) = &export.declaration {
                    self.declaration(declaration, environment);
                } else {
                    environment.clear();
                }
            }
            Statement::ExpressionStatement(statement) => {
                self.expression(&statement.expression, environment);
            }
            Statement::BlockStatement(block) => return self.statements(&block.body, environment),
            Statement::IfStatement(branch) => {
                let test = self.expression(&branch.test, environment);
                if let Some(value) = &test.fact {
                    return if value.truthy() {
                        self.statement(&branch.consequent, environment)
                    } else {
                        branch
                            .alternate
                            .as_ref()
                            .is_none_or(|alternate| self.statement(alternate, environment))
                    };
                }
                let mut other = environment.clone();
                let left = self.statement(&branch.consequent, environment);
                let right = branch
                    .alternate
                    .as_ref()
                    .is_none_or(|alternate| self.statement(alternate, &mut other));
                match (left, right) {
                    (true, true) => intersect(environment, &other),
                    (false, true) => *environment = other,
                    (true, false) => {}
                    (false, false) => return false,
                }
            }
            Statement::ReturnStatement(ret) => {
                if let Some(argument) = &ret.argument {
                    self.expression(argument, environment);
                }
                return false;
            }
            Statement::ThrowStatement(throw) => {
                self.expression(&throw.argument, environment);
                return false;
            }
            Statement::BreakStatement(_) | Statement::ContinueStatement(_) => return false,
            Statement::EmptyStatement(_) => {}
            _ => environment.clear(),
        }
        true
    }
}

impl<'a> Visit<'a> for Analyzer<'_> {
    fn visit_statements(&mut self, statements: &oxc_allocator::Vec<'a, Statement<'a>>) {
        if !self.checkpoint() {
            return;
        }
        if let (Some(first), Some(last)) = (statements.first(), statements.last()) {
            if !self
                .visited_lists
                .contains(&(first.span().start, last.span().end))
            {
                self.statements(statements, &mut Environment::new());
            }
        }
        // Descend into independently executing bodies, including functions,
        // loops and exception regions, with no assumed incoming allocation.
        walk::walk_statements(self, statements);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::SourceType;

    fn reads(source: &str) -> Result<Vec<(String, String)>, BudgetExceeded> {
        let allocator = Allocator::default();
        let program = crate::parse_as(&allocator, source, SourceType::cjs())
            .unwrap_or_else(|| unreachable!("{source}"));
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        assert!(semantic.diagnostics.is_empty(), "{source}");
        let scoping = semantic.semantic.scoping();
        let bindings = BindingFacts::analyze(&program, scoping);
        let analysis = FreshDataReads::analyze(
            &program,
            scoping,
            &bindings,
            &WorkBudget::unlimited("fresh-data-tests"),
        )?;
        let mut facts = analysis.values.into_iter().collect::<Vec<_>>();
        facts.sort_by_key(|(span, _)| *span);
        Ok(facts
            .into_iter()
            .filter_map(|((start, end), value)| {
                Some((
                    source.get(start as usize..end as usize)?.to_owned(),
                    value.render()?,
                ))
            })
            .collect())
    }

    #[test]
    fn reaching_facts_follow_real_expression_order_and_joins() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("const a=[7]; a[0]; mutate(a); a[0];", vec![("a[0]", "7")]),
            (
                "const a=[7]; const b=a; b[0]; a[0];",
                vec![("b[0]", "7"), ("a[0]", "7")],
            ),
            (
                "function f(fn){const a=[7];fn(a[0],mutate(a),a[0]);}",
                vec![("a[0]", "7")],
            ),
            (
                "function f(flag){let a={x:7};let b=a;if(flag){b={x:8}}a.x;b.x;}",
                vec![("a.x", "7")],
            ),
            (
                "function f(flag){let a=[7];if(flag){mutate(a);return;}return a[0];}",
                vec![("a[0]", "7")],
            ),
            (
                "function f(flag){let a=[7];if(flag){mutate(a);}return a[0];}",
                vec![],
            ),
            (
                "let a=[7];let i=0;a[i];a=[9];a[i];",
                vec![("a[i]", "7"), ("a[i]", "9")],
            ),
            ("let a={x:7,...side(),x:9};a.x;", vec![("a.x", "9")]),
            ("let a={x:7,...side()};a.x;", vec![]),
            (
                "function f(flag){let a={x:7,y:8};if(flag)a={x:7,z:9};return a.x;}",
                vec![("a.x", "7")],
            ),
            (
                "function f(flag){let a=flag?{x:7,y:8}:{x:7,y:9};a.y;return a.x;}",
                vec![("a.x", "7")],
            ),
            (
                "function f(flag){let a=flag?[-0]:[0];a[0];a.length;}",
                vec![("a.length", "1")],
            ),
            (
                "function f(flag){let a=flag?{x:7}:{get x(){return 7}};return a.x;}",
                vec![],
            ),
            ("let a={'1e+21':7,1e21:9};a[1e21];", vec![("a[1e21]", "9")]),
            (
                "let a={'0.0000001':7,1e-7:9};a['0.0000001'];a[1e-7];",
                vec![("a['0.0000001']", "7"), ("a[1e-7]", "9")],
            ),
            ("const a=[7,...iter];a[0];", vec![("a[0]", "7")]),
            ("const a=[...iter,7];a.length;", vec![]),
            (
                "const a=[,9];a.length;a[1];",
                vec![("a.length", "2"), ("a[1]", "9")],
            ),
            ("({x:7}).x;", vec![("({x:7}).x", "7")]),
            ("({x:7,y:side()}).x;", vec![]),
            ("const a={x:7,y:side()};a.x;", vec![("a.x", "7")]),
            (
                "function f(flag){const a=[7];{if(flag){7;}else{8;}}return a[0];}",
                vec![("a[0]", "7")],
            ),
            (
                "function f(flag){const a=[7];return flag ? a[0] : a.length;}",
                vec![("a[0]", "7"), ("a.length", "1")],
            ),
            ("const a=[7];(true||side());a[0];", vec![("a[0]", "7")]),
            ("const a=[7];false&&side();a[0];", vec![("a[0]", "7")]),
            ("const a=[7];const b={unknown:missing};a[0];", vec![]),
        ] {
            let expected = expected
                .into_iter()
                .map(|(text, value)| (text.to_owned(), value.to_owned()))
                .collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn no_facts_cross_unknown_effects_or_deferred_execution() -> Result<(), BudgetExceeded> {
        for source in [
            "const a=[7];unknown(a[0]);",
        "function f(){const a=[7];with(new Proxy({},{has(t,k){if(k==='b')a[0]=9;return false;}})){var b=a[0];}return b;}f();",
            "const a=[7];(eval)('a[0]=9');a[0];",
            "const a=[7];a[(mutate(a),0)];",
            "const a=[7];a[8];a[0];",
            "const a=[7];delete a[0];a[0];",
            "const a=[7];a[0]=9;a[0];",
            "const a=[7];function f(){return a[0];}",
            "const a=[7];while(flag){a[0];mutate(a);}",
            "let a=[7];try{mutate(a);}catch(e){}a[0];",
            "const a={get x(){return 1},y:2};a.x;a.y;",
            "let a;{a=[7];}eval('a[0]=9');a[0];",
            "function f(flag){const a=[7];flag&&mutate(a);return a[0];}",
            "function f(flag){const a=[7];flag?mutate(a):0;return a[0];}",
        ] {
            assert!(reads(source)?.is_empty(), "{source}");
        }
        Ok(())
    }
}
