//! Structural proof of the complete effect and termination shape of a
//! checksum-controlled rotation. Bindings here are semantic IDs, never
//! names recovered by a regular expression.
use super::{
    assignment_identifier, exact_identifier, js_number_from_i64, js_parse_int,
    numeric_object_values, unparenthesized, Decoder,
};
use crate::{
    binding_facts::BindingFacts,
    expression_integer,
    value_eval::{
        eval, exact_computed_property_key, inert_literal_value, known_bool, string_literal_value,
    },
};
use oxc_ast::ast::{
    CallExpression, Expression, ForStatementInit, Function, Statement, VariableDeclaration,
    VariableDeclarationKind,
};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::GetSpan;
use oxc_syntax::{scope::ScopeId, symbol::SymbolId};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub(super) enum ChecksumExpression {
    Number(f64),
    Negate(Box<Self>),
    Binary(&'static str, Box<Self>, Box<Self>),
    ParseInt {
        decoder: SymbolId,
        raw: i64,
        key: Option<String>,
        radix: u32,
    },
}

impl ChecksumExpression {
    pub(super) fn cost(&self) -> u64 {
        match self {
            Self::Negate(value) => 1u64.saturating_add(value.cost()),
            Self::Binary(_, left, right) => 1u64
                .saturating_add(left.cost())
                .saturating_add(right.cost()),
            Self::Number(_) | Self::ParseInt { .. } => 1,
        }
    }

    fn references_decoder(&self, symbol: SymbolId) -> bool {
        match self {
            Self::Negate(value) => value.references_decoder(symbol),
            Self::Binary(_, left, right) => {
                left.references_decoder(symbol) || right.references_decoder(symbol)
            }
            Self::ParseInt { decoder, .. } => *decoder == symbol,
            Self::Number(_) => false,
        }
    }

    pub(super) fn evaluate(
        &self,
        decoders: &HashMap<SymbolId, Decoder>,
        provider: SymbolId,
        rotation: usize,
    ) -> Option<f64> {
        match self {
            Self::Number(value) => Some(*value),
            Self::Negate(value) => Some(-value.evaluate(decoders, provider, rotation)?),
            Self::Binary(operator, left, right) => {
                let left = left.evaluate(decoders, provider, rotation)?;
                let right = right.evaluate(decoders, provider, rotation)?;
                match *operator {
                    "+" => Some(left + right),
                    "-" => Some(left - right),
                    "*" => Some(left * right),
                    "/" => Some(left / right),
                    "%" => Some(left % right),
                    _ => None,
                }
            }
            Self::ParseInt {
                decoder,
                raw,
                key,
                radix,
            } => {
                let decoder = decoders.get(decoder)?;
                if decoder.provider != provider {
                    return None;
                }
                let value =
                    decoder.value_for_raw_rotated_with_key(*raw, rotation, key.as_deref())?;
                js_parse_int(&value.js_string()?, *radix)
            }
        }
    }
}

#[derive(Debug)]
pub(super) struct RotationProof {
    pub(super) provider: SymbolId,
    pub(super) provider_reference: ReferenceId,
    pub(super) target: i64,
    pub(super) checksum: ChecksumExpression,
}

struct Setup<'a> {
    scoping: &'a Scoping,
    facts: &'a BindingFacts,
    scope: ScopeId,
    parameter_provider: Option<SymbolId>,
    parameter_target: Option<SymbolId>,
    table: Option<(SymbolId, SymbolId, ReferenceId)>,
    initialized: HashSet<SymbolId>,
    aliases: HashMap<SymbolId, SymbolId>,
    objects: HashMap<SymbolId, HashMap<String, i64>>,
}

impl Setup<'_> {
    fn identifier(&self, expression: &Expression<'_>) -> Option<SymbolId> {
        exact_identifier(expression, self.scoping, self.facts)
    }

    fn local(&self, symbol: SymbolId) -> bool {
        self.scoping
            .scope_ancestors(self.scoping.symbol_scope_id(symbol))
            .any(|scope| scope == self.scope)
            && self.scoping.symbol_redeclarations(symbol).is_empty()
            && Some(symbol) != self.parameter_provider
            && Some(symbol) != self.parameter_target
    }

    fn assignment<'a>(
        &self,
        expression: &'a Expression<'a>,
    ) -> Option<(SymbolId, &'a Expression<'a>)> {
        let (target, value) = assignment_identifier(expression)?;
        let reference = target.reference_id.get()?;
        let symbol = self
            .facts
            .fixed_assignment_reference(self.scoping, reference)?;
        let flags = self.scoping.symbol_flags(symbol);
        if !self.local(symbol)
            || flags.is_const_variable()
            || flags.is_import()
            || !self.facts.proves_initialized(
                self.scoping,
                symbol,
                self.scoping.get_reference(reference).scope_id(),
                expression.span(),
            )
        {
            return None;
        }
        Some((symbol, value))
    }

    fn initialize(&mut self, symbol: SymbolId, value: &Expression<'_>) -> Option<()> {
        if !self.local(symbol) || !self.initialized.insert(symbol) {
            return None;
        }
        match unparenthesized(value) {
            Expression::CallExpression(call) if !call.optional && call.arguments.is_empty() => {
                let Expression::Identifier(callee) = unparenthesized(&call.callee) else {
                    return None;
                };
                let reference = callee.reference_id.get()?;
                let provider = self.facts.resolved_symbol(self.scoping, reference)?;
                let valid_provider = if let Some(expected) = self.parameter_provider {
                    provider == expected
                } else {
                    !self.local(provider) && self.scoping.symbol_flags(provider).is_function()
                };
                if !valid_provider || self.table.is_some() {
                    return None;
                }
                self.table = Some((symbol, provider, reference));
            }
            Expression::Identifier(_) => {
                let target = self.identifier(value)?;
                if self.local(target)
                    || !self.scoping.symbol_flags(target).is_function()
                    || !self.facts.binding_unmodified_by_eval(self.scoping, target)
                {
                    return None;
                }
                self.aliases.insert(symbol, target);
            }
            Expression::ObjectExpression(object) => {
                self.objects.insert(symbol, numeric_object_values(object)?);
            }
            expression if inert_literal_value(expression) => {}
            _ => return None,
        }
        Some(())
    }

    fn declarations(&mut self, declarations: &VariableDeclaration<'_>) -> Option<()> {
        if !ordinary_declaration(declarations) {
            return None;
        }
        for declaration in &declarations.declarations {
            let symbol = declaration.id.get_binding_identifier()?.symbol_id.get()?;
            if !self.local(symbol) {
                return None;
            }
            if let Some(value) = &declaration.init {
                self.initialize(symbol, value)?;
            }
        }
        Some(())
    }

    fn initialization_expression(&mut self, expression: &Expression<'_>) -> Option<()> {
        if let Expression::SequenceExpression(sequence) = unparenthesized(expression) {
            for expression in &sequence.expressions {
                self.initialization_expression(expression)?;
            }
        } else {
            let (symbol, value) = self.assignment(expression)?;
            self.initialize(symbol, value)?;
        }
        Some(())
    }

    fn prelude(&mut self, statement: &Statement<'_>) -> Option<()> {
        match statement {
            Statement::VariableDeclaration(declaration) => self.declarations(declaration),
            Statement::ExpressionStatement(expression) => {
                self.initialization_expression(&expression.expression)
            }
            Statement::EmptyStatement(_) => Some(()),
            _ => None,
        }
    }

    fn integer(&self, expression: &Expression<'_>) -> Option<i64> {
        expression_integer(expression).or_else(|| {
            let (symbol, property) = member(expression, self.scoping, self.facts)?;
            self.objects.get(&symbol)?.get(&property).copied()
        })
    }

    fn checksum(&self, expression: &Expression<'_>) -> Option<ChecksumExpression> {
        match unparenthesized(expression) {
            Expression::NumericLiteral(number) => Some(ChecksumExpression::Number(number.value)),
            Expression::StaticMemberExpression(_) | Expression::ComputedMemberExpression(_) => {
                Some(ChecksumExpression::Number(js_number_from_i64(
                    self.integer(expression)?,
                )))
            }
            Expression::UnaryExpression(unary) => {
                let value = self.checksum(&unary.argument)?;
                match unary.operator.as_str() {
                    "+" => Some(value),
                    "-" => Some(ChecksumExpression::Negate(Box::new(value))),
                    _ => None,
                }
            }
            Expression::BinaryExpression(binary) => {
                let operator = match binary.operator.as_str() {
                    "+" => "+",
                    "-" => "-",
                    "*" => "*",
                    "/" => "/",
                    "%" => "%",
                    _ => return None,
                };
                Some(ChecksumExpression::Binary(
                    operator,
                    Box::new(self.checksum(&binary.left)?),
                    Box::new(self.checksum(&binary.right)?),
                ))
            }
            Expression::CallExpression(call) => self.parse_int(call),
            _ => None,
        }
    }

    fn parse_int(&self, call: &CallExpression<'_>) -> Option<ChecksumExpression> {
        if call.optional || !(1..=2).contains(&call.arguments.len()) {
            return None;
        }
        let Expression::Identifier(callee) = unparenthesized(&call.callee) else {
            return None;
        };
        if callee.name != "parseInt"
            || !self
                .facts
                .proves_global_reference(self.scoping, callee.reference_id.get()?)
        {
            return None;
        }
        let Expression::CallExpression(decoded) =
            unparenthesized(call.arguments.first()?.as_expression()?)
        else {
            return None;
        };
        if decoded.optional || !(1..=2).contains(&decoded.arguments.len()) {
            return None;
        }
        let alias = self.identifier(&decoded.callee)?;
        let decoder = self.aliases.get(&alias).copied().or_else(|| {
            (!self.local(alias) && self.scoping.symbol_flags(alias).is_function()).then_some(alias)
        })?;
        let raw = self.integer(decoded.arguments.first()?.as_expression()?)?;
        let key = match decoded.arguments.get(1) {
            Some(argument) => {
                let Expression::StringLiteral(literal) = unparenthesized(argument.as_expression()?)
                else {
                    return None;
                };
                Some(string_literal_value(literal)?)
            }
            None => None,
        };
        let radix = match call.arguments.get(1) {
            Some(argument) => u32::try_from(self.integer(argument.as_expression()?)?).ok()?,
            None => 0,
        };
        Some(ChecksumExpression::ParseInt {
            decoder,
            raw,
            key,
            radix,
        })
    }

    fn comparison<'a>(
        &self,
        expression: &'a Expression<'a>,
        prepared: Option<(SymbolId, &'a Expression<'a>)>,
    ) -> Option<(i64, &'a Expression<'a>)> {
        let (comparison, prepared) =
            if let Expression::SequenceExpression(sequence) = unparenthesized(expression) {
                if prepared.is_some() {
                    return None;
                }
                let [assignment, comparison] = sequence.expressions.as_slice() else {
                    return None;
                };
                (comparison, Some(self.assignment(assignment)?))
            } else {
                (expression, prepared)
            };
        let Expression::BinaryExpression(binary) = unparenthesized(comparison) else {
            return None;
        };
        if !matches!(binary.operator.as_str(), "==" | "===") {
            return None;
        }
        let target = |expression: &Expression<'_>| {
            if let Some(symbol) = self.parameter_target {
                (self.identifier(expression) == Some(symbol)).then_some(0)
            } else {
                expression_integer(expression)
            }
        };
        let (target, checksum) = if let Some(target) = target(&binary.left) {
            (target, &binary.right)
        } else {
            (target(&binary.right)?, &binary.left)
        };
        if let Some((symbol, value)) = prepared {
            if !self.local(symbol)
                || self.aliases.contains_key(&symbol)
                || self.objects.contains_key(&symbol)
                || self.table.is_some_and(|(table, _, _)| table == symbol)
                || self.identifier(checksum) != Some(symbol)
            {
                return None;
            }
            Some((target, value))
        } else {
            Some((target, checksum))
        }
    }

    fn loop_body(&self, statement: &Statement<'_>) -> Option<(i64, ChecksumExpression)> {
        let Statement::TryStatement(statement) = single_statement(statement)? else {
            return None;
        };
        if statement.finalizer.is_some() {
            return None;
        }
        let handler = statement.handler.as_ref()?;
        if handler
            .param
            .as_ref()
            .is_some_and(|param| param.pattern.get_binding_identifier().is_none())
        {
            return None;
        }
        let [catch] = handler.body.body.as_slice() else {
            return None;
        };
        let (table, _, _) = self.table?;
        rotation_step(catch, table, self.scoping, self.facts)?;
        let mut statements = statement.block.body.as_slice();
        let prepared = if let Some(Statement::VariableDeclaration(declaration)) = statements.first()
        {
            if !ordinary_declaration(declaration) {
                return None;
            }
            let [declaration] = declaration.declarations.as_slice() else {
                return None;
            };
            let symbol = declaration.id.get_binding_identifier()?.symbol_id.get()?;
            statements = &statements[1..];
            Some((symbol, declaration.init.as_ref()?))
        } else {
            None
        };
        let (first, tail) = statements.split_first()?;
        let Statement::IfStatement(branch) = first else {
            return None;
        };
        let Statement::BreakStatement(exit) = single_statement(&branch.consequent)? else {
            return None;
        };
        if exit.label.is_some() {
            return None;
        }
        if let Some(alternate) = &branch.alternate {
            if !tail.is_empty() {
                return None;
            }
            rotation_step(alternate, table, self.scoping, self.facts)?;
        } else {
            let [rotate] = tail else {
                return None;
            };
            rotation_step(rotate, table, self.scoping, self.facts)?;
        }
        let (target, expression) = self.comparison(&branch.test, prepared)?;
        Some((target, self.checksum(expression)?))
    }
}

fn member(
    expression: &Expression<'_>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<(SymbolId, String)> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => Some((
            exact_identifier(&member.object, scoping, facts)?,
            member.property.name.to_string(),
        )),
        Expression::ComputedMemberExpression(member) if !member.optional => Some((
            exact_identifier(&member.object, scoping, facts)?,
            exact_computed_property_key(&member.expression, eval)?,
        )),
        _ => None,
    }
}

fn rotation_step(
    statement: &Statement<'_>,
    table: SymbolId,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<()> {
    let Statement::ExpressionStatement(statement) = single_statement(statement)? else {
        return None;
    };
    let Expression::CallExpression(push) = unparenthesized(&statement.expression) else {
        return None;
    };
    let [argument] = push.arguments.as_slice() else {
        return None;
    };
    let Expression::CallExpression(shift) = unparenthesized(argument.as_expression()?) else {
        return None;
    };
    let (push_table, push_name) = member(&push.callee, scoping, facts)?;
    let (shift_table, shift_name) = member(&shift.callee, scoping, facts)?;
    (!push.optional
        && !shift.optional
        && shift.arguments.is_empty()
        && push_table == table
        && shift_table == table
        && push_name == "push"
        && shift_name == "shift")
        .then_some(())
}

pub(super) fn ordinary_declaration(declaration: &VariableDeclaration<'_>) -> bool {
    matches!(
        declaration.kind,
        VariableDeclarationKind::Var
            | VariableDeclarationKind::Let
            | VariableDeclarationKind::Const
    )
}

fn single_statement<'a>(statement: &'a Statement<'a>) -> Option<&'a Statement<'a>> {
    if let Statement::BlockStatement(block) = statement {
        let [statement] = block.body.as_slice() else {
            return None;
        };
        single_statement(statement)
    } else {
        Some(statement)
    }
}

/// A single, synchronous loop with a proven infinite test, one local
/// checksum calculation, a terminating equality guard, and the same
/// physical shift in both the nonmatching and exceptional paths.
pub(super) fn prove_checksum_rotation(
    function: &Function<'_>,
    parameter_target: Option<i64>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<RotationProof> {
    let scope = function.scope_id.get()?;
    let parameters = simple_parameters(function)?;
    let (provider, target) = if parameter_target.is_some() {
        (Some(*parameters.first()?), Some(*parameters.get(1)?))
    } else {
        if !parameters.is_empty() {
            return None;
        }
        (None, None)
    };
    let mut setup = Setup {
        scoping,
        facts,
        scope,
        parameter_provider: provider,
        parameter_target: target,
        table: None,
        initialized: HashSet::new(),
        aliases: HashMap::new(),
        objects: HashMap::new(),
    };
    let statements = function.body.as_ref()?.statements.as_slice();
    let (last, prefix) = statements.split_last()?;
    for statement in prefix {
        setup.prelude(statement)?;
    }
    let body = match last {
        Statement::WhileStatement(statement) if known_bool(&statement.test) == Some(true) => {
            &statement.body
        }
        Statement::ForStatement(statement)
            if statement.update.is_none()
                && statement
                    .test
                    .as_ref()
                    .is_none_or(|test| known_bool(test) == Some(true)) =>
        {
            if let Some(initializer) = &statement.init {
                if let ForStatementInit::VariableDeclaration(declaration) = initializer {
                    setup.declarations(declaration)?;
                } else {
                    setup.initialization_expression(initializer.as_expression()?)?;
                }
            }
            &statement.body
        }
        _ => return None,
    };
    let (target, checksum) = setup.loop_body(body)?;
    if setup
        .aliases
        .values()
        .any(|symbol| !checksum.references_decoder(*symbol))
    {
        return None;
    }
    let (_, provider, provider_reference) = setup.table?;
    Some(RotationProof {
        provider,
        provider_reference,
        target: parameter_target.unwrap_or(target),
        checksum,
    })
}

/// Exact prefix arithmetic on a single parameter cell. A same-spelled
/// shadowing declaration, property update or postfix operation is not
/// equivalent to the countdown represented here.
fn prefix_update(
    expression: &Expression<'_>,
    operator: &str,
    symbol: SymbolId,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> bool {
    let Expression::UpdateExpression(update) = unparenthesized(expression) else {
        return false;
    };
    let oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(identifier) =
        &update.argument
    else {
        return false;
    };
    update.prefix
        && update.operator.as_str() == operator
        && identifier
            .reference_id
            .get()
            .and_then(|reference| facts.fixed_assignment_reference(scoping, reference))
            == Some(symbol)
}

pub(super) fn simple_parameters(function: &Function<'_>) -> Option<Vec<SymbolId>> {
    if function.r#async
        || function.generator
        || function.params.rest.is_some()
        || !super::function_parameters_have_no_runtime_effects(function)
    {
        return None;
    }
    let symbols = function
        .params
        .items
        .iter()
        .map(|parameter| parameter.pattern.get_binding_identifier()?.symbol_id.get())
        .collect::<Option<Vec<_>>>()?;
    (symbols.iter().collect::<HashSet<_>>().len() == symbols.len()).then_some(symbols)
}

/// Prove a helper implementing an exact nonnegative countdown:
/// increment the original count once, then decrement before each test.
/// Restrict the input so both increment and decrement are exact Numbers.
pub(super) fn prove_fixed_rotation(
    function: &Function<'_>,
    count: i64,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<()> {
    if !(0..=(1i64 << 53) - 2).contains(&count) {
        return None;
    }
    let parameters = simple_parameters(function)?;
    let [table, count_symbol] = parameters.as_slice() else {
        return None;
    };
    let statements = function.body.as_ref()?.statements.as_slice();
    let [Statement::VariableDeclaration(declaration), Statement::ExpressionStatement(invocation)] =
        statements
    else {
        return None;
    };
    if !ordinary_declaration(declaration) {
        return None;
    }
    let [declarator] = declaration.declarations.as_slice() else {
        return None;
    };
    let helper_symbol = declarator.id.get_binding_identifier()?.symbol_id.get()?;
    if parameters.contains(&helper_symbol)
        || !scoping.symbol_redeclarations(helper_symbol).is_empty()
    {
        return None;
    }
    let Expression::FunctionExpression(helper) = unparenthesized(declarator.init.as_ref()?) else {
        return None;
    };
    let helper_parameters = simple_parameters(helper)?;
    let [cursor] = helper_parameters.as_slice() else {
        return None;
    };
    let [Statement::WhileStatement(countdown)] = helper.body.as_ref()?.statements.as_slice() else {
        return None;
    };
    if !prefix_update(&countdown.test, "--", *cursor, scoping, facts) {
        return None;
    }
    rotation_step(&countdown.body, *table, scoping, facts)?;
    let Expression::CallExpression(call) = unparenthesized(&invocation.expression) else {
        return None;
    };
    let [argument] = call.arguments.as_slice() else {
        return None;
    };
    if call.optional
        || exact_identifier(&call.callee, scoping, facts) != Some(helper_symbol)
        || !prefix_update(
            argument.as_expression()?,
            "++",
            *count_symbol,
            scoping,
            facts,
        )
    {
        return None;
    }
    Some(())
}
