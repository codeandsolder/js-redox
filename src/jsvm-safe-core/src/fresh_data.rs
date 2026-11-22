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
    literal_property_key, LogicalStep, Value,
};
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, BindingPattern, Declaration, Expression, IdentifierReference,
    MemberExpression, ObjectPropertyKind, Program, PropertyKind, SimpleAssignmentTarget, Statement,
    VariableDeclaration, VariableDeclarationKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::{operator::AssignmentOperator, symbol::SymbolId};
use std::collections::{HashMap, HashSet};
use work_budget::{BudgetExceeded, WorkBudget};

mod heap;
use heap::{AllocationId, AllocationKind, Environment, Fact, Locations, OwnData};

enum Reference {
    Binding(SymbolId),
    Member { locations: Locations, key: String },
}

impl Reference {
    fn read(&self, environment: &Environment) -> Option<Option<Fact>> {
        match self {
            Self::Binding(symbol) => Some(environment.get(symbol).cloned()),
            Self::Member { locations, key } => environment.read(locations, key),
        }
    }

    fn write(&self, environment: &mut Environment, value: Option<Fact>) -> bool {
        match self {
            Self::Binding(symbol) => {
                if let Some(value) = value {
                    environment.insert(*symbol, value);
                } else {
                    environment.remove(symbol);
                }
                true
            }
            Self::Member { locations, key } => environment.write(locations, key, value),
        }
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

    fn primitive_value(&self) -> Option<&Value> {
        self.fact.as_ref()?.primitive()
    }

    fn unknown_inert() -> Self {
        Self {
            fact: None,
            inert: true,
        }
    }
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
            next_allocation: 0,
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
    next_allocation: AllocationId,
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
        let reference_flags = self.scoping.get_reference(reference);
        // This is an AST value-position read, including the receiver of a
        // property write. MemberWriteTarget marks the containing operation,
        // not a write to the receiver binding itself.
        if !reference_flags.is_read() || reference_flags.is_write() {
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

    fn allocate(
        &mut self,
        environment: &mut Environment,
        data: OwnData,
        inert: bool,
    ) -> Evaluation {
        let id = self.next_allocation;
        self.next_allocation += 1;
        Evaluation {
            fact: Some(environment.allocate(id, data)),
            inert,
        }
    }

    fn key(&mut self, expression: &Expression<'_>, environment: &mut Environment) -> Evaluation {
        if let Expression::BigIntLiteral(literal) = expression.without_parentheses() {
            return Evaluation::primitive(Value::String(literal.value.to_string()), true);
        }
        self.expression(expression, environment)
    }

    fn member(
        &mut self,
        span: Span,
        object: Evaluation,
        key: Evaluation,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(name) = key.primitive_value().and_then(Value::js_string) else {
            return Self::barrier(environment);
        };
        let Some(Fact::Objects(locations)) = object.fact else {
            return Self::barrier(environment);
        };
        // The receiver was evaluated before the key, but its contents must
        // be read *after* key evaluation, including any effects on aliases.
        let Some(fact) = environment.read(&locations, &name) else {
            return Self::barrier(environment);
        };
        let inert = object.inert && key.inert;
        if let Some(Fact::Primitive(value)) = &fact {
            if inert {
                self.reads
                    .values
                    .insert((span.start, span.end), value.clone());
            }
        }
        Evaluation { fact, inert }
    }

    /// Evaluate the receiver before the key, for reads, assignment targets,
    /// updates and delete alike. Never evaluate an optional member as an
    /// unconditional reference, or a private member as a public own key.
    fn member_components(
        &mut self,
        member: &MemberExpression<'_>,
        environment: &mut Environment,
    ) -> Option<(Evaluation, Evaluation)> {
        if member.optional() {
            return None;
        }
        let object = self.expression(member.object(), environment);
        let key = match member {
            MemberExpression::StaticMemberExpression(member) => {
                Evaluation::primitive(Value::String(member.property.name.to_string()), true)
            }
            MemberExpression::ComputedMemberExpression(member) => {
                self.key(&member.expression, environment)
            }
            MemberExpression::PrivateFieldExpression(_) => return None,
        };
        Some((object, key))
    }

    fn member_reference(
        &mut self,
        member: &MemberExpression<'_>,
        environment: &mut Environment,
    ) -> Option<Reference> {
        let (object, key) = self.member_components(member, environment)?;
        let key = key.primitive_value()?.js_string()?;
        let Fact::Objects(locations) = object.fact? else {
            return None;
        };
        Some(Reference::Member { locations, key })
    }

    fn reference(
        &mut self,
        target: &SimpleAssignmentTarget<'_>,
        environment: &mut Environment,
    ) -> Option<Reference> {
        if let SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) = target {
            let symbol = self.lexical_reference(identifier)?;
            let flags = self.scoping.symbol_flags(symbol);
            return (flags.is_block_scoped() && !flags.is_const_variable())
                .then_some(Reference::Binding(symbol));
        }
        self.member_reference(target.as_member_expression()?, environment)
    }

    fn logical_decision(operator: &str, fact: &Fact) -> Option<bool> {
        match fact {
            Fact::Primitive(value) => eval_logical_left(operator, value.clone())
                .map(|step| matches!(step, LogicalStep::EvaluateRight)),
            Fact::Objects(_) => Some(operator == "&&"),
        }
    }

    fn assignment(
        &mut self,
        assignment: &oxc_ast::ast::AssignmentExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(reference) = assignment
            .left
            .as_simple_assignment_target()
            .and_then(|target| self.reference(target, environment))
        else {
            return Self::barrier(environment);
        };
        let operator = assignment.operator;
        if operator == AssignmentOperator::Assign {
            let value = self.expression(&assignment.right, environment);
            if !reference.write(environment, value.fact.clone()) {
                environment.clear();
            }
            return Evaluation {
                fact: value.fact,
                inert: false,
            };
        }

        let Some(previous) = reference.read(environment) else {
            return Self::barrier(environment);
        };
        if let Some(logical) = operator.to_logical_operator() {
            let decision = previous
                .as_ref()
                .and_then(|fact| Self::logical_decision(logical.as_str(), fact));
            if decision == Some(false) {
                return Evaluation {
                    fact: previous,
                    inert: false,
                };
            }
            let skipped = (decision.is_none()).then(|| (environment.clone(), self.next_allocation));
            let value = self.expression(&assignment.right, environment);
            if !reference.write(environment, value.fact.clone()) {
                environment.clear();
            }
            if let Some((skipped, first_new)) = skipped {
                environment.join(&skipped, first_new);
                return Evaluation {
                    fact: None,
                    inert: false,
                };
            }
            return Evaluation {
                fact: value.fact,
                inert: false,
            };
        }

        let right = self.expression(&assignment.right, environment);
        let value = operator.to_binary_operator().and_then(|binary| {
            eval_binary(
                binary.as_str(),
                previous.as_ref()?.primitive()?,
                right.primitive_value()?,
            )
        });
        let Some(value) = value else {
            return Self::barrier(environment);
        };
        let fact = Fact::Primitive(value);
        if !reference.write(environment, Some(fact.clone())) {
            environment.clear();
        }
        Evaluation {
            fact: Some(fact),
            inert: false,
        }
    }

    fn update_expression(
        &mut self,
        update: &oxc_ast::ast::UpdateExpression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let Some(reference) = self.reference(&update.argument, environment) else {
            return Self::barrier(environment);
        };
        let Some(previous) = reference
            .read(environment)
            .flatten()
            .and_then(|fact| fact.primitive()?.number())
        else {
            return Self::barrier(environment);
        };
        let next = if update.operator.as_str() == "++" {
            previous + 1.0
        } else {
            previous - 1.0
        };
        if !reference.write(environment, Some(Fact::Primitive(Value::Number(next)))) {
            environment.clear();
        }
        Evaluation::primitive(
            Value::Number(if update.prefix { next } else { previous }),
            false,
        )
    }

    fn delete_expression(
        &mut self,
        argument: &Expression<'_>,
        environment: &mut Environment,
    ) -> Evaluation {
        let reference = argument
            .without_parentheses()
            .as_member_expression()
            .and_then(|member| self.member_reference(member, environment));
        let Some(Reference::Member { locations, key }) = reference else {
            return Self::barrier(environment);
        };
        if environment.delete(&locations, &key) {
            Evaluation::primitive(Value::Bool(true), false)
        } else {
            Self::barrier(environment)
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
            expression if expression.is_member_expression() => {
                let Some((object, key)) = expression
                    .as_member_expression()
                    .and_then(|member| self.member_components(member, environment))
                else {
                    return Self::barrier(environment);
                };
                self.member(expression.span(), object, key, environment)
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
                    return self.delete_expression(&unary.argument, environment);
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
                    "typeof" if matches!(argument.fact, Some(Fact::Objects(_))) => {
                        Evaluation::primitive(Value::String("object".into()), argument.inert)
                    }
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
                    let equal = left
                        .fact
                        .as_ref()
                        .zip(right.fact.as_ref())
                        .and_then(|(left, right)| left.strict_equal(right));
                    Evaluation {
                        fact: equal.map(|equal| {
                            Fact::Primitive(Value::Bool(equal == (operator == "===")))
                        }),
                        inert: left.inert && right.inert,
                    }
                } else {
                    Self::barrier(environment)
                }
            }
            Expression::LogicalExpression(logical) => {
                let left = self.expression(&logical.left, environment);
                let decision = left
                    .fact
                    .as_ref()
                    .and_then(|fact| Self::logical_decision(logical.operator.as_str(), fact));
                match decision {
                    Some(false) => left,
                    Some(true) => {
                        let mut right = self.expression(&logical.right, environment);
                        right.inert &= left.inert;
                        right
                    }
                    None => {
                        let skip = environment.clone();
                        let first_new = self.next_allocation;
                        let right = self.expression(&logical.right, environment);
                        environment.join(&skip, first_new);
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
                let first_new = self.next_allocation;
                let left = self.expression(&conditional.consequent, environment);
                let right = self.expression(&conditional.alternate, &mut other);
                environment.join(&other, first_new);
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
                let mut data = OwnData::new(AllocationKind::Array);
                let mut inert = true;
                let mut known_index = true;
                for (index, element) in array.elements.iter().enumerate() {
                    match element {
                        ArrayExpressionElement::Elision(_) => {}
                        ArrayExpressionElement::SpreadElement(spread) => {
                            self.expression(&spread.argument, environment);
                            environment.clear();
                            known_index = false;
                            data.unknown_array_tail();
                            inert = false;
                        }
                        _ => {
                            let Some(value) = element.as_expression() else {
                                return Self::barrier(environment);
                            };
                            let result = self.expression(value, environment);
                            inert &= result.inert;
                            if known_index {
                                data.define_data(index.to_string(), result.fact);
                            }
                        }
                    }
                }
                let length = known_index
                    .then(|| u32::try_from(array.elements.len()).ok())
                    .flatten()
                    .map(|length| Fact::Primitive(Value::Number(f64::from(length))));
                data.define_data("length".into(), length);
                self.allocate(environment, data, inert)
            }
            Expression::ObjectExpression(object) => {
                let mut data = OwnData::new(AllocationKind::Ordinary);
                let mut inert = true;
                for item in &object.properties {
                    match item {
                        ObjectPropertyKind::SpreadProperty(spread) => {
                            let value = self.expression(&spread.argument, environment);
                            let copied = match value.fact.as_ref() {
                                Some(fact) => match data.spread(environment, fact, self.budget) {
                                    Ok(copied) => copied,
                                    Err(failure) => {
                                        self.failure = Some(failure);
                                        return Self::barrier(environment);
                                    }
                                },
                                None => false,
                            };
                            if copied {
                                inert &= value.inert;
                            } else {
                                environment.clear();
                                data.define_unknown_key(true, None);
                                inert = false;
                            }
                        }
                        ObjectPropertyKind::ObjectProperty(property) => {
                            let key = if property.computed {
                                let result = property
                                    .key
                                    .as_expression()
                                    .map(|key| self.key(key, environment))
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
                            let is_data = property.kind == PropertyKind::Init;
                            let Some(key) = key else {
                                data.define_unknown_key(is_data, value.fact);
                                continue;
                            };
                            if is_prototype_setter(property, &key) {
                                data.set_literal_prototype(value.fact);
                            } else if is_data {
                                data.define_data(key, value.fact);
                            } else {
                                data.define_accessor(key);
                            }
                        }
                    }
                }
                self.allocate(environment, data, inert)
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
            Expression::AssignmentExpression(assignment) => {
                self.assignment(assignment, environment)
            }
            Expression::UpdateExpression(update) => self.update_expression(update, environment),
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
                let first_new = self.next_allocation;
                let left = self.statement(&branch.consequent, environment);
                let right = branch
                    .alternate
                    .as_ref()
                    .is_none_or(|alternate| self.statement(alternate, &mut other));
                match (left, right) {
                    (true, true) => environment.join(&other, first_new),
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
    fn heap_facts_follow_alias_writes_and_nested_references() -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("const a=[7];a[0]=9;a[0];", vec![("a[0]","9")]),
            ("let a={x:7,y:8};let b=a;b.x=9;a.x;a.y;",vec![("a.x","9"),("a.y","8")]),
            ("let a={x:{y:7}};let b=a.x;b.y=9;a.x.y;",vec![("a.x.y","9")]),
            ("let a={x:7};let b={a};a.x=9;b.a.x;",vec![("b.a.x","9")]),
            ("let a={x:7};let b={a};b.a.x+=2;a.x;",vec![("a.x","9")]),
            ("let a={x:7};let b={a};const p=b.a.x++;const q=++b.a.x;a.x;({p,q}).p;({p,q}).q;",vec![("a.x","9"),("({p,q}).p","7"),("({p,q}).q","9")]),
            ("let a={x:0,y:8};a.x ||= 9;a.x &&= 7;a.x ??= side();a.x;a.y;",vec![("a.x","7"),("a.y","8")]),
            ("let a={x:null};a.x ??= {y:7};a.x.y;",vec![("a.x.y","7")]),
            ("let a={x:7};let b=a;a.x=(a={x:8},9);a.x;b.x;",vec![("a.x","8"),("b.x","9")]),
            ("let a={x:7};let b=a;a[(a={x:8},'x')]=9;a.x;b.x;",vec![("a.x","8"),("b.x","9")]),
            ("let a=[7,8,9];let b=a;b.length=2;a.length;a[1];",vec![("a.length","2"),("a[1]","8")]),
            ("let a=[7,8,9];a.length='1';a[0];a.length;",vec![("a[0]","7"),("a.length","1")]),
            ("let a=[7,8,9];delete a[1];a[0];a[2];a.length;",vec![("a[0]","7"),("a[2]","9"),("a.length","3")]),
            ("let a={x:null};a.x=a;a.x.x.x===a;a.x.x.x.x.x.x.x.x;",vec![]),
            ("let a={x:7};let b={x:9};let c=true?a:b;c.x=8;a.x;b.x;",vec![("a.x","8"),("b.x","9")]),
            ("function f(flag){let a={x:7};let b={x:8};let c=flag?a:b;c.x=9;a.x;b.x;}",vec![]),
            ("function f(flag){let a={x:7,y:8};let b={x:7,y:9};let c=flag?a:b;c.x=9;c.y;a.y;b.y;}",vec![("a.y","8"),("b.y","9")]),
            ("function f(flag){let a={x:7};if(flag)a.x=9;else a.x=9;return a.x;}",vec![("a.x","9")]),
            ("function f(flag){let a={x:7};if(flag)a.x=9;return a.x;}",vec![]),
            ("function f(flag,v){let a={x:v,y:7};a.x ||= 9;return a.y;}",vec![("a.y","7")]),
            ("function f(v){let a={x:7,y:8};a.x=v;return a.y;}",vec![("a.y","8")]),
            ("let a={x:7};let b={p:a};let c={q:b};c.q.p.x=9;c.q.p.x;",vec![("c.q.p.x","9")]),
            ("let a={x:7};let b={p:a,y:side()};b.p.x;",vec![]),
            ("let a={x:7};let b={p:a,y:(a.x=9)};b.p.x;",vec![("b.p.x","9")]),
            ("let a={x:7};a[(a.x=9,'x')];a.x;",vec![("a.x","9")]),
            ("let a={x:7};let b={p:a};unknown();b.p.x;",vec![]),
            ("function f(flag){let a={x:7};let b=flag?{p:a}:{p:a};b.p.x;}",vec![("b.p.x","7")]),
            ("const a=[7,...iter];a.length=1;a[0];a.length;",vec![("a[0]","7"),("a.length","1")]),
            ("let a={x:7};a[0n]=8;a.x;",vec![]),
            ("const a={16:7};a[0x10n]=9;a[16n];",vec![("a[16n]","9")]),
            ("let a={x:7};let b=a;if(a===b)a.x=9;a.x;", vec![("a.x","9")]),
            ("let a={x:7};let b={x:8};if(a!==b)a.x=9;a.x;", vec![("a.x","9")]),
            ("let a={x:7};if(typeof a==='object')a.x=9;a.x;", vec![("a.x","9")]),
            ("function f(flag){let a={x:7};let b={x:8};let c=flag?a:b;if(c===a)a.x=9;a.x;}",vec![]),
        ] {
            let expected = expected.into_iter().map(|(text,value)|(text.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn prototype_and_descriptor_facts_support_inheritance_and_new_properties(
    ) -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let a={__proto__:null};a.missing;a.x=7;a.x;delete a.x;a.x;",vec![("a.missing","void 0"),("a.x","7"),("a.x","void 0")]),
            ("let p={x:7};let a={__proto__:p};a.x;p.x=9;a.x;",vec![("a.x","7"),("a.x","9")]),
            ("let p={x:7};let a={__proto__:p};a.x=9;a.x;p.x;delete a.x;a.x;",vec![("a.x","9"),("p.x","7"),("a.x","7")]),
            ("let p={__proto__:null,x:7};let a={__proto__:p};a.y=9;a.y;p.y;delete a.y;a.y;",vec![("a.y","9"),("p.y","void 0"),("a.y","void 0")]),
            ("let p={__proto__:null,x:{y:7}};let a={__proto__:p};a.x.y=9;p.x.y;a.x.y;",vec![("p.x.y","9"),("a.x.y","9")]),
            ("let p={x:7};let a={__proto__:{__proto__:p}};a.x;p.x=9;a.x;",vec![("a.x","7"),("a.x","9")]),
            ("let a={__proto__:{x:7},x:8};delete a.x;a.x;",vec![("a.x","7")]),
            ("let a={__proto__:null};a.__proto__=9;a.__proto__;",vec![("a.__proto__","9")]),
            ("let a={['__proto__']:7};a.__proto__;",vec![("a.__proto__","7")]),
            ("let a={__proto__:null};a.x??=7;a.x;",vec![("a.x","7")]),
            ("let p={x:7};let a={__proto__:p};a.x+=2;a.x;p.x;",vec![("a.x","9"),("p.x","7")]),
            ("let p={x:7};let a={__proto__:p};let y=a.x++;a.x;p.x;({y}).y;",vec![("a.x","8"),("p.x","7"),("({y}).y","7")]),
            ("function f(flag){let a={__proto__:null};if(flag)a.x=7;a.x=9;a.x;}",vec![("a.x","9")]),
            ("function f(flag){let a={__proto__:null,x:7};if(flag)delete a.x;a.x=9;a.x;}",vec![("a.x","9")]),
            ("function f(flag){let p={x:7};let a={__proto__:p};if(flag)a.x=7;a.x;}",vec![("a.x","7")]),
            ("function f(flag){let p={x:7};let a={__proto__:p,x:7};if(flag)delete a.x;a.x;}",vec![("a.x","7")]),
            ("function f(flag){let p=flag?{x:7}:{x:7};let a={__proto__:p};a.x;}",vec![("a.x","7")]),
            ("function f(flag){let p=flag?{x:7}:{x:9};let a={__proto__:p};a.x;}",vec![]),
            ("function f(flag){let a={__proto__:null};let b={__proto__:null};let c=flag?a:b;c.x=7;c.x=9;}",vec![]),
            ("function f(k){let a={x:7,[k]:9};a.x=8;a.x;}",vec![("a.x","8")]),
            ("function f(k){let a={__proto__:null,[k]:9};a.x=8;a.x;}",vec![("a.x","8")]),
            ("let a={__proto__:null,x:7,...thing};a.x=9;a.x;",vec![("a.x","9")]),
            ("let a={__proto__:null,...thing};a.x=9;a.x;",vec![("a.x","9")]),
            ("let a={x:7,...thing};a.x=9;a.x;",vec![("a.x","9")]),
            ("let a={__proto__:null,get x(){return 7;}};delete a.x;a.x=9;a.x;",vec![("a.x","9")]),
            ("let p=[7,8];let a={__proto__:p};a.length;a[0];p.length=1;a.length;",vec![("a.length","2"),("a[0]","7"),("a.length","1")]),
            ("let p=[7];let a={__proto__:p};a.length=9;a.length;p.length;",vec![("a.length","9"),("p.length","1")]),
            // Unproven prototypes/accessors remain effect barriers, even
            // when the receiver itself is definitely an ordinary object.
            ("let a={__proto__:3};a.missing;",vec![]),
            ("let a={};a.missing;",vec![]),
            ("let a={};a.x=9;a.x;",vec![]),
            ("let p={get x(){return 7;}};let a={__proto__:p};a.x;",vec![]),
            ("let p={set x(v){side(v)}};let a={__proto__:p};a.x=9;a.x;",vec![]),
            ("let a={__proto__:null,get x(){return 7;}};a.x;",vec![]),
            ("function f(k){let a={__proto__:null,x:7,get [k](){return 9;}};a.x;}",vec![]),
            ("function f(k){let a={__proto__:null,x:7,get [k](){return 9;}};a.x=8;a.x;}",vec![]),
            ("let p={x:7};let a={__proto__:p};unknown();a.x;",vec![]),
            ("let p={x:7};let a={__proto__:p,y:unknown()};a.x;",vec![]),
            ("let a={__proto__:null};Object.setPrototypeOf(a,p);a.x;",vec![]),
            ("let a={__proto__:null};Object.defineProperty(a,'x',{value:7});a.x=9;a.x;",vec![]),
        ] {
            let expected = expected.into_iter().map(|(text,value)|(text.to_owned(),value.to_owned())).collect::<Vec<_>>();
            assert_eq!(reads(source)?, expected, "{source}");
        }
        Ok(())
    }

    #[test]
    fn copy_data_properties_preserves_exact_enumerability_aliases_and_effects(
    ) -> Result<(), BudgetExceeded> {
        for (source, expected) in [
            ("let a={x:7};let b={...a};b.x;",vec![("b.x","7")]),
            ("let a={x:7};let b={...a};a.x=9;b.x;",vec![("b.x","7")]),
            ("let a={x:{y:7}};let b={...a};b.x.y=9;a.x.y;b.x.y;",vec![("a.x.y","9"),("b.x.y","9")]),
            ("let a={__proto__:{x:7}};let b={__proto__:null,...a};b.x;",vec![("b.x","void 0")]),
            ("let a=[7,,9];let b={__proto__:null,...a};b[0];b[1];b[2];b.length;",vec![("b[0]","7"),("b[1]","void 0"),("b[2]","9"),("b.length","void 0")]),
            ("let a=[7,8];a.length=1;let b={__proto__:null,...a};b[0];b[1];b.length;",vec![("b[0]","7"),("b[1]","void 0"),("b.length","void 0")]),
            ("let b={x:2,...{x:7},x:9};b.x;",vec![("b.x","9")]),
            ("let b={x:2,...{x:7}};b.x;",vec![("b.x","7")]),
            ("let a={__proto__:null,x:7};let b={__proto__:null,...a};b.x;b.y;",vec![("b.x","7"),("b.y","void 0")]),
            ("let a={__proto__:null,...null,...void 0,...7,...true};a.x;",vec![("a.x","void 0")]),
            ("let a={__proto__:null,...'ab'};a[0];a[1];a[2];a.length;",vec![("a[0]",r#""a""#),("a[1]",r#""b""#),("a[2]","void 0"),("a.length","void 0")]),
            ("let a={__proto__:null,...'é中'};a[0];a[1];a[2];",vec![("a[0]",r#""é""#),("a[1]",r#""中""#),("a[2]","void 0")]),
            ("let a={__proto__:null,...'😀z'};a[0];a[1];a[2];a[3];",vec![("a[2]",r#""z""#),("a[3]","void 0")]),
            ("let a={['__proto__']:7};let b={__proto__:null,...a};b.__proto__;b.x;",vec![("b.__proto__","7"),("b.x","void 0")]),
            ("let a={x:7};let b={get x(){return 9},...a};b.x;",vec![("b.x","7")]),
            ("function f(flag){let a=flag?{x:7}:{y:8};let b={__proto__:null,x:7,...a};b.x;}",vec![("b.x","7")]),
            ("function f(flag){let a=flag?{x:7}:{y:8};let b={__proto__:null,...a};b.x;b.z;}",vec![("b.z","void 0")]),
            ("function f(k){const a={__proto__:null,[k]:7};const b={__proto__:null,x:7,...a};b.x;}",vec![("b.x","7")]),
            ("let a={x:7,...thing};let b={...a};b.x=9;b.x;",vec![("b.x","9")]),
            ("let p={x:7};let b={...{get x(){p.x=9;return 7}}};p.x;",vec![]),
            ("let a={get x(){return 7}};let b={...a};b.x;",vec![]),
            ("function f(k){let a={get [k](){return 7}};let b={__proto__:null,...a};b.x;}",vec![]),
            ("let a={x:7};let b={...a,y:side()};b.x;a.x;",vec![("b.x","7")]),
            ("let a={x:7};let b={...a,y:side()};a.x;b.x;",vec![]),
            ("let a={x:7};let b={...a,y:(a.x=9)};a.x;b.x;",vec![("a.x","9"),("b.x","7")]),
            ("let a={x:7};let b={...a,...(a.x=9,a)};a.x;b.x;",vec![("a.x","9"),("b.x","9")]),
            ("let a={x:7};let b={...a,...(unknown(),a)};b.x;",vec![]),
        ] {
            let expected = expected.into_iter().map(|(text,value)|(text.to_owned(),value.to_owned())).collect::<Vec<_>>();
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
