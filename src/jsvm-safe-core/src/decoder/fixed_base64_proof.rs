use super::{
    assignment_identifier, eval_from_char_code_concat, fixed_decoder_control_shape,
    fixed_decoder_iife_calls_proven, fixed_decoder_iife_function,
    fixed_decoder_iife_wrapper_proven, function_parameters_have_no_runtime_effects,
    indexed_table_symbol, unparenthesized,
};
use crate::{
    expression_integer, statically_resolved_symbol, statically_unresolved_global_reference,
    value_eval::{eval, Value},
};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, BindingPattern, Expression, ForStatement, ForStatementInit, Statement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_ecmascript::{
    side_effects::{MayHaveSideEffects, MayHaveSideEffectsContext, PropertyReadSideEffects},
    GlobalContext,
};
use oxc_regular_expression::{
    ast::{CharacterClassContents, CharacterClassContentsKind, Term},
    LiteralParser as RegExpLiteralParser, Options as RegExpOptions,
};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_span::{GetSpan, Span};
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum FixedBase64Value {
    Const(u32),
    Sextet(u8),
    And(Box<FixedBase64Value>, Box<FixedBase64Value>),
    Or(Box<FixedBase64Value>, Box<FixedBase64Value>),
    Shl(Box<FixedBase64Value>, Box<FixedBase64Value>),
    Shr(Box<FixedBase64Value>, Box<FixedBase64Value>),
}

fn fixed_base64_commutative(
    left: FixedBase64Value,
    right: FixedBase64Value,
    and: bool,
) -> FixedBase64Value {
    let (left, right) = if left <= right {
        (left, right)
    } else {
        (right, left)
    };
    if and {
        FixedBase64Value::And(Box::new(left), Box::new(right))
    } else {
        FixedBase64Value::Or(Box::new(left), Box::new(right))
    }
}

fn fixed_base64_expected_bytes() -> [FixedBase64Value; 3] {
    use FixedBase64Value::{Const, Sextet, Shl, Shr};
    [
        fixed_base64_commutative(
            Shl(Box::new(Sextet(0)), Box::new(Const(2))),
            Shr(Box::new(Sextet(1)), Box::new(Const(4))),
            false,
        ),
        fixed_base64_commutative(
            Shl(
                Box::new(fixed_base64_commutative(Const(15), Sextet(1), true)),
                Box::new(Const(4)),
            ),
            Shr(Box::new(Sextet(2)), Box::new(Const(2))),
            false,
        ),
        fixed_base64_commutative(
            Shl(
                Box::new(fixed_base64_commutative(Const(3), Sextet(2), true)),
                Box::new(Const(6)),
            ),
            Sextet(3),
            false,
        ),
    ]
}

fn statically_resolved_identifier_symbol(
    expression: &Expression<'_>,
    scoping: &Scoping,
) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = unparenthesized(expression) else {
        return None;
    };
    statically_resolved_symbol(scoping, identifier.reference_id.get()?)
}

fn assignment_reference_symbol(
    identifier: &oxc_ast::ast::IdentifierReference<'_>,
    scoping: &Scoping,
) -> Option<SymbolId> {
    statically_resolved_symbol(scoping, identifier.reference_id.get()?)
}

fn fixed_base64_direct_source(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
) -> Option<(SymbolId, u32)> {
    let body = function.body.as_ref()?;
    let [Statement::IfStatement(guard), Statement::ForStatement(_), Statement::ReturnStatement(_)] =
        body.statements.as_slice()
    else {
        return None;
    };
    if guard.alternate.is_some() {
        return None;
    }
    let Statement::ReturnStatement(early_return) = &guard.consequent else {
        return None;
    };
    let returned = statically_resolved_identifier_symbol(early_return.argument.as_ref()?, scoping)?;
    let first_param = function.params.items.first()?;
    let BindingPattern::BindingIdentifier(first_param) = &first_param.pattern else {
        return None;
    };
    let index_symbol = first_param.symbol_id.get()?;
    let Expression::BinaryExpression(test) = unparenthesized(&guard.test) else {
        return None;
    };
    if !matches!(test.operator.as_str(), "!=" | "!==") {
        return None;
    }

    fn load_alias(
        expression: &Expression<'_>,
        index_symbol: SymbolId,
        scoping: &Scoping,
    ) -> Option<SymbolId> {
        let Expression::UnaryExpression(unary) = unparenthesized(expression) else {
            return None;
        };
        if unary.operator.as_str() != "typeof" {
            return None;
        }
        let (target, value) = assignment_identifier(&unary.argument)?;
        indexed_table_symbol(value, index_symbol, scoping)?;
        assignment_reference_symbol(target, scoping)
    }

    let string_side = |expression: &Expression<'_>| matches!(eval(expression), Some(Value::String(value)) if value == "string");
    let alias = if string_side(&test.left) {
        load_alias(&test.right, index_symbol, scoping)?
    } else if string_side(&test.right) {
        load_alias(&test.left, index_symbol, scoping)?
    } else {
        return None;
    };
    (alias == returned).then_some((alias, guard.span.end))
}

fn fixed_base64_loop_expressions<'a>(
    statement: &'a Statement<'a>,
) -> Option<Vec<&'a Expression<'a>>> {
    fn push<'a>(expression: &'a Expression<'a>, out: &mut Vec<&'a Expression<'a>>) {
        if let Expression::SequenceExpression(sequence) = unparenthesized(expression) {
            for expression in &sequence.expressions {
                push(expression, out);
            }
        } else {
            out.push(expression);
        }
    }

    let mut out = Vec::new();
    match statement {
        Statement::ExpressionStatement(statement) => push(&statement.expression, &mut out),
        Statement::BlockStatement(block) => {
            for statement in &block.body {
                let Statement::ExpressionStatement(statement) = statement else {
                    return None;
                };
                push(&statement.expression, &mut out);
            }
        }
        _ => return None,
    }
    Some(out)
}

struct FixedBase64Eval<'c> {
    scoping: &'c Scoping,
    values: HashMap<SymbolId, FixedBase64Value>,
    alphabet: Option<SymbolId>,
    input: Option<SymbolId>,
    cursor: Option<SymbolId>,
    next_sextet: u8,
}

impl FixedBase64Eval<'_> {
    fn consistent(slot: &mut Option<SymbolId>, symbol: SymbolId) -> bool {
        match slot {
            Some(existing) => *existing == symbol,
            None => {
                *slot = Some(symbol);
                true
            }
        }
    }

    fn sextet(&mut self, expression: &Expression<'_>) -> Option<FixedBase64Value> {
        let Expression::CallExpression(index_call) = unparenthesized(expression) else {
            return None;
        };
        if index_call.optional
            || index_call.arguments.len() != 1
            || index_call.arguments[0].is_spread()
        {
            return None;
        }
        let Expression::StaticMemberExpression(index_member) = unparenthesized(&index_call.callee)
        else {
            return None;
        };
        if index_member.optional || index_member.property.name.as_str() != "indexOf" {
            return None;
        }
        let alphabet = statically_resolved_identifier_symbol(&index_member.object, self.scoping)?;
        let char_call = index_call.arguments[0].as_expression()?;
        let Expression::CallExpression(char_call) = unparenthesized(char_call) else {
            return None;
        };
        if char_call.optional
            || char_call.arguments.len() != 1
            || char_call.arguments[0].is_spread()
        {
            return None;
        }
        let Expression::StaticMemberExpression(char_member) = unparenthesized(&char_call.callee)
        else {
            return None;
        };
        if char_member.optional || char_member.property.name.as_str() != "charAt" {
            return None;
        }
        let input = statically_resolved_identifier_symbol(&char_member.object, self.scoping)?;
        let Expression::UpdateExpression(update) =
            unparenthesized(char_call.arguments[0].as_expression()?)
        else {
            return None;
        };
        if update.prefix || update.operator.as_str() != "++" {
            return None;
        }
        let oxc_ast::ast::SimpleAssignmentTarget::AssignmentTargetIdentifier(cursor) =
            &update.argument
        else {
            return None;
        };
        let cursor = assignment_reference_symbol(cursor, self.scoping)?;
        if !Self::consistent(&mut self.alphabet, alphabet)
            || !Self::consistent(&mut self.input, input)
            || !Self::consistent(&mut self.cursor, cursor)
            || self.next_sextet >= 4
        {
            return None;
        }
        let value = FixedBase64Value::Sextet(self.next_sextet);
        self.next_sextet += 1;
        Some(value)
    }

    fn value(&mut self, expression: &Expression<'_>) -> Option<FixedBase64Value> {
        let expression = unparenthesized(expression);
        if let Some(value) = self.sextet(expression) {
            return Some(value);
        }
        match expression {
            Expression::NumericLiteral(_) => Some(FixedBase64Value::Const(
                u32::try_from(expression_integer(expression)?).ok()?,
            )),
            Expression::Identifier(_) => {
                let symbol = statically_resolved_identifier_symbol(expression, self.scoping)?;
                self.values.get(&symbol).cloned()
            }
            Expression::AssignmentExpression(assignment) if assignment.operator.as_str() == "=" => {
                let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) =
                    &assignment.left
                else {
                    return None;
                };
                let target = assignment_reference_symbol(target, self.scoping)?;
                let value = self.value(&assignment.right)?;
                self.values.insert(target, value.clone());
                Some(value)
            }
            Expression::BinaryExpression(binary) => {
                let left = self.value(&binary.left)?;
                let right = self.value(&binary.right)?;
                match binary.operator.as_str() {
                    "&" => Some(fixed_base64_commutative(left, right, true)),
                    "|" => Some(fixed_base64_commutative(left, right, false)),
                    "<<" => Some(FixedBase64Value::Shl(Box::new(left), Box::new(right))),
                    ">>" => Some(FixedBase64Value::Shr(Box::new(left), Box::new(right))),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

fn fixed_base64_from_char_code(
    expression: &Expression<'_>,
    evaluator: &mut FixedBase64Eval<'_>,
) -> Option<FixedBase64Value> {
    let Expression::CallExpression(call) = unparenthesized(expression) else {
        return None;
    };
    if call.optional || call.arguments.len() != 1 || call.arguments[0].is_spread() {
        return None;
    }
    let Expression::StaticMemberExpression(member) = unparenthesized(&call.callee) else {
        return None;
    };
    if member.optional || member.property.name.as_str() != "fromCharCode" {
        return None;
    }
    let Expression::Identifier(string) = unparenthesized(&member.object) else {
        return None;
    };
    if string.name.as_str() != "String"
        || !statically_unresolved_global_reference(evaluator.scoping, string.reference_id.get()?)
    {
        return None;
    }
    evaluator.value(call.arguments[0].as_expression()?)
}

fn fixed_base64_append(
    expression: &Expression<'_>,
    evaluator: &mut FixedBase64Eval<'_>,
) -> Option<(SymbolId, FixedBase64Value)> {
    let Expression::AssignmentExpression(assignment) = unparenthesized(expression) else {
        return None;
    };
    if assignment.operator.as_str() != "+=" {
        return None;
    }
    let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left
    else {
        return None;
    };
    let target = assignment_reference_symbol(target, evaluator.scoping)?;
    let value = fixed_base64_from_char_code(&assignment.right, evaluator)?;
    Some((target, value))
}

fn fixed_base64_sentinel_append(
    expression: &Expression<'_>,
    evaluator: &mut FixedBase64Eval<'_>,
    sextet: u8,
) -> Option<(SymbolId, FixedBase64Value)> {
    let Expression::LogicalExpression(logical) = unparenthesized(expression) else {
        return None;
    };
    if logical.operator.as_str() != "&&" {
        return None;
    }
    let Expression::BinaryExpression(test) = unparenthesized(&logical.left) else {
        return None;
    };
    if !matches!(test.operator.as_str(), "!=" | "!==") {
        return None;
    }
    let is_64 = |expression: &Expression<'_>| matches!(unparenthesized(expression), Expression::NumericLiteral(value) if value.value == 64.0);
    let sextet_matches = |expression: &Expression<'_>| {
        let symbol = statically_resolved_identifier_symbol(expression, evaluator.scoping)?;
        (evaluator.values.get(&symbol) == Some(&FixedBase64Value::Sextet(sextet))).then_some(())
    };
    if !((is_64(&test.left) && sextet_matches(&test.right).is_some())
        || (is_64(&test.right) && sextet_matches(&test.left).is_some()))
    {
        return None;
    }
    fixed_base64_append(&logical.right, evaluator)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FixedBase64Init {
    Zero,
    Empty,
    Alphabet,
    Source,
    SanitizedSource,
    Other,
}

fn is_fixed_base64_filter(filter: &oxc_ast::ast::RegExpLiteral<'_>) -> bool {
    if filter.regex.flags != oxc_ast::ast::RegExpFlags::G {
        return false;
    }
    let allocator = Allocator::default();
    let Ok(pattern) = RegExpLiteralParser::new(
        &allocator,
        filter.regex.pattern.text.as_str(),
        Some("g"),
        RegExpOptions::default(),
    )
    .parse() else {
        return false;
    };
    let [alternative] = pattern.body.body.as_slice() else {
        return false;
    };
    let [Term::CharacterClass(class)] = alternative.body.as_slice() else {
        return false;
    };
    if !class.negative || class.strings || class.kind != CharacterClassContentsKind::Union {
        return false;
    }

    let mut included = HashSet::new();
    for item in &class.body {
        match item {
            CharacterClassContents::CharacterClassRange(range) => {
                if range.min.value > range.max.value || range.max.value > 0x7f {
                    return false;
                }
                included.extend(range.min.value..=range.max.value);
            }
            CharacterClassContents::Character(character) if character.value <= 0x7f => {
                included.insert(character.value);
            }
            _ => return false,
        }
    }

    let expected = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="
        .iter()
        .map(|byte| u32::from(*byte))
        .collect::<HashSet<_>>();
    included == expected
}

fn fixed_base64_sanitized_source(
    expression: &Expression<'_>,
    input: SymbolId,
    source: SymbolId,
    output: SymbolId,
    scoping: &Scoping,
) -> bool {
    let expression = unparenthesized(expression);
    if let Expression::AssignmentExpression(assignment) = expression {
        if assignment.operator.as_str() != "=" {
            return false;
        }
        let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left
        else {
            return false;
        };
        if assignment_reference_symbol(target, scoping) != Some(input) {
            return false;
        }
        return fixed_base64_sanitized_source(&assignment.right, input, source, output, scoping);
    }
    let Expression::CallExpression(call) = expression else {
        return false;
    };
    if call.optional || call.arguments.len() != 2 || call.arguments.iter().any(Argument::is_spread)
    {
        return false;
    }
    let Expression::StaticMemberExpression(member) = unparenthesized(&call.callee) else {
        return false;
    };
    if member.optional || member.property.name.as_str() != "replace" {
        return false;
    }
    let source_ok =
        if statically_resolved_identifier_symbol(&member.object, scoping) == Some(source) {
            true
        } else if let Some((target, value)) = assignment_identifier(&member.object) {
            assignment_reference_symbol(target, scoping) == Some(input)
                && statically_resolved_identifier_symbol(value, scoping) == Some(source)
        } else {
            false
        };
    if !source_ok {
        return false;
    }
    let Some(Expression::RegExpLiteral(filter)) =
        call.arguments[0].as_expression().map(unparenthesized)
    else {
        return false;
    };
    if !is_fixed_base64_filter(filter) {
        return false;
    }
    let Some(replacement) = call.arguments[1].as_expression() else {
        return false;
    };
    if matches!(eval(replacement), Some(Value::String(value)) if value.is_empty()) {
        return true;
    }
    let Some((target, value)) = assignment_identifier(replacement) else {
        return false;
    };
    assignment_reference_symbol(target, scoping) == Some(output)
        && matches!(eval(value), Some(Value::String(value)) if value.is_empty())
}

struct FixedBase64EffectContext<'c> {
    scoping: &'c Scoping,
}

impl<'a> GlobalContext<'a> for FixedBase64EffectContext<'_> {
    fn is_global_reference(&self, reference: &oxc_ast::ast::IdentifierReference<'a>) -> bool {
        reference.reference_id.get().is_none_or(|reference_id| {
            self.scoping
                .get_reference(reference_id)
                .symbol_id()
                .is_none()
        })
    }
}

impl<'a> MayHaveSideEffectsContext<'a> for FixedBase64EffectContext<'_> {
    fn annotations(&self) -> bool {
        false
    }

    fn manual_pure_functions(&self, _callee: &Expression<'_>) -> bool {
        false
    }

    fn property_read_side_effects(&self) -> PropertyReadSideEffects {
        PropertyReadSideEffects::All
    }

    fn unknown_global_side_effects(&self) -> bool {
        true
    }
}

struct FixedBase64SetupProof<'c> {
    function_span: Span,
    alphabet: SymbolId,
    input: SymbolId,
    cursor: SymbolId,
    output: SymbolId,
    source: SymbolId,
    expected_alphabet: &'c str,
    scoping: &'c Scoping,
    aliases: &'c HashMap<SymbolId, u32>,
}

impl FixedBase64SetupProof<'_> {
    fn init_kind(&self, target: SymbolId, expression: &Expression<'_>) -> FixedBase64Init {
        if target == self.cursor
            && matches!(unparenthesized(expression), Expression::NumericLiteral(value) if value.value == 0.0)
        {
            FixedBase64Init::Zero
        } else if target == self.output
            && matches!(eval(expression), Some(Value::String(value)) if value.is_empty())
        {
            FixedBase64Init::Empty
        } else if target == self.alphabet {
            let mut used = HashSet::new();
            if eval_from_char_code_concat(expression, self.scoping, self.aliases, &mut used)
                .as_deref()
                == Some(self.expected_alphabet)
            {
                FixedBase64Init::Alphabet
            } else {
                FixedBase64Init::Other
            }
        } else if target == self.input
            && fixed_base64_sanitized_source(
                expression,
                self.input,
                self.source,
                self.output,
                self.scoping,
            )
        {
            FixedBase64Init::SanitizedSource
        } else if target == self.input
            && statically_resolved_identifier_symbol(expression, self.scoping) == Some(self.source)
        {
            FixedBase64Init::Source
        } else {
            FixedBase64Init::Other
        }
    }

    fn expression_proven(&self, expression: &Expression<'_>) -> bool {
        let effects = FixedBase64EffectContext {
            scoping: self.scoping,
        };
        let expression = unparenthesized(expression);
        if let Expression::SequenceExpression(sequence) = expression {
            return sequence
                .expressions
                .iter()
                .all(|expression| self.expression_proven(expression));
        }
        if let Expression::AssignmentExpression(assignment) = expression {
            if assignment.operator.as_str() == "=" {
                if let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) =
                    &assignment.left
                {
                    if let Some(target) = assignment_reference_symbol(target, self.scoping) {
                        let declaration = self.scoping.symbol_span(target);
                        if self.function_span.start > declaration.start
                            || declaration.end > self.function_span.end
                        {
                            return false;
                        }
                        return self.init_kind(target, &assignment.right) != FixedBase64Init::Other
                            || !assignment.right.may_have_side_effects(&effects);
                    }
                }
            }
        }
        !expression.may_have_side_effects(&effects)
    }

    fn declaration_proven(&self, declaration: &oxc_ast::ast::VariableDeclaration<'_>) -> bool {
        let effects = FixedBase64EffectContext {
            scoping: self.scoping,
        };
        declaration.declarations.iter().all(|declarator| {
            if declarator.id.may_have_side_effects(&effects) {
                return false;
            }
            let Some(initializer) = declarator.init.as_ref() else {
                return true;
            };
            let BindingPattern::BindingIdentifier(target) = &declarator.id else {
                return !initializer.may_have_side_effects(&effects);
            };
            let Some(target) = target.symbol_id.get() else {
                return false;
            };
            self.init_kind(target, initializer) != FixedBase64Init::Other
                || !initializer.may_have_side_effects(&effects)
        })
    }

    fn setup_statement_proven(&self, statement: &Statement<'_>) -> bool {
        match statement {
            Statement::VariableDeclaration(declaration) => self.declaration_proven(declaration),
            Statement::ExpressionStatement(statement) => {
                self.expression_proven(&statement.expression)
            }
            Statement::BlockStatement(block) => {
                block.body.iter().all(|statement| match statement {
                    Statement::ExpressionStatement(statement) => {
                        self.expression_proven(&statement.expression)
                    }
                    _ => false,
                })
            }
            _ => false,
        }
    }

    fn loop_initializer_proven(&self, statement: &ForStatement<'_>) -> bool {
        let Some(initializer) = statement.init.as_ref() else {
            return true;
        };
        match initializer {
            ForStatementInit::VariableDeclaration(declaration) => {
                self.declaration_proven(declaration)
            }
            _ => self.expression_proven(initializer.to_expression()),
        }
    }

    fn surrounding_statements_proven(
        &self,
        body: &oxc_ast::ast::FunctionBody<'_>,
        direct_guard: bool,
    ) -> bool {
        let effects = FixedBase64EffectContext {
            scoping: self.scoping,
        };
        let mut seen_loop = false;
        for (index, statement) in body.statements[..body.statements.len() - 1]
            .iter()
            .enumerate()
        {
            match statement {
                Statement::ForStatement(_) => {
                    if seen_loop {
                        return false;
                    }
                    seen_loop = true;
                }
                Statement::IfStatement(_) if direct_guard && index == 0 && !seen_loop => {}
                _ if !seen_loop => {
                    if !self.setup_statement_proven(statement) {
                        return false;
                    }
                }
                _ => {
                    if statement.may_have_side_effects(&effects) {
                        return false;
                    }
                }
            }
        }
        seen_loop
    }
}

fn fixed_base64_setup_proven(
    body: &oxc_ast::ast::FunctionBody<'_>,
    loop_body_start: u32,
    setup: &FixedBase64SetupProof<'_>,
) -> bool {
    struct Probe<'c> {
        limit: u32,
        setup: &'c FixedBase64SetupProof<'c>,
        latest: HashMap<SymbolId, (u32, FixedBase64Init)>,
    }
    impl Probe<'_> {
        fn record(&mut self, target: SymbolId, expression: &Expression<'_>, end: u32) {
            if end > self.limit
                || !matches!(target, t if t == self.setup.alphabet || t == self.setup.input || t == self.setup.cursor || t == self.setup.output)
            {
                return;
            }
            let kind = self.setup.init_kind(target, expression);
            let entry = self.latest.entry(target).or_insert((0, kind));
            if end >= entry.0 {
                *entry = (end, kind);
            }
        }
    }
    impl<'a> Visit<'a> for Probe<'_> {
        fn visit_variable_declarator(&mut self, declarator: &oxc_ast::ast::VariableDeclarator<'a>) {
            if let (BindingPattern::BindingIdentifier(target), Some(initializer)) =
                (&declarator.id, &declarator.init)
            {
                if let Some(symbol) = target.symbol_id.get() {
                    self.record(symbol, initializer, declarator.span.end);
                }
            }
            walk::walk_variable_declarator(self, declarator);
        }

        fn visit_assignment_expression(
            &mut self,
            assignment: &oxc_ast::ast::AssignmentExpression<'a>,
        ) {
            if assignment.operator.as_str() == "=" {
                if let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(target) =
                    &assignment.left
                {
                    if let Some(symbol) = assignment_reference_symbol(target, self.setup.scoping) {
                        self.record(symbol, &assignment.right, assignment.span.end);
                    }
                }
            }
            walk::walk_assignment_expression(self, assignment);
        }

        fn visit_function(&mut self, _function: &oxc_ast::ast::Function<'a>, _flags: ScopeFlags) {}

        fn visit_arrow_function_expression(
            &mut self,
            _function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
        ) {
            // Deferred arrow bodies are not part of the executed setup path.
        }

        fn visit_logical_expression(&mut self, logical: &oxc_ast::ast::LogicalExpression<'a>) {
            // Only the left operand is unconditionally evaluated. The right
            // may be short-circuited, so writes there cannot prove setup state.
            self.visit_expression(&logical.left);
        }

        fn visit_conditional_expression(
            &mut self,
            conditional: &oxc_ast::ast::ConditionalExpression<'a>,
        ) {
            // The test always executes, but neither branch is unconditional.
            self.visit_expression(&conditional.test);
        }

        fn visit_chain_expression(&mut self, _chain: &oxc_ast::ast::ChainExpression<'a>) {
            // Optional chains can skip member/call subexpressions. None of
            // their descendant writes can establish unconditional setup state.
        }
    }

    let mut probe = Probe {
        limit: loop_body_start,
        setup,
        latest: HashMap::new(),
    };
    for statement in &body.statements {
        probe.visit_statement(statement);
    }
    let input_ready = match probe.latest.get(&setup.input).map(|(_, kind)| *kind) {
        Some(FixedBase64Init::Source | FixedBase64Init::SanitizedSource) => true,
        Some(_) => false,
        None => setup.input == setup.source,
    };
    input_ready
        && probe.latest.get(&setup.cursor).map(|(_, kind)| *kind) == Some(FixedBase64Init::Zero)
        && probe.latest.get(&setup.output).map(|(_, kind)| *kind) == Some(FixedBase64Init::Empty)
        && probe.latest.get(&setup.alphabet).map(|(_, kind)| *kind)
            == Some(FixedBase64Init::Alphabet)
}

pub(super) fn fixed_base64_algorithm_proven(
    function: &oxc_ast::ast::Function<'_>,
    scoping: &Scoping,
    aliases: &HashMap<SymbolId, u32>,
    reference_spans: &HashMap<ReferenceId, Span>,
    alphabet: &str,
) -> bool {
    if function.r#async
        || function.generator
        || !function_parameters_have_no_runtime_effects(function)
    {
        return false;
    }
    let Some(outer_body) = function.body.as_ref() else {
        return false;
    };
    let iife = fixed_decoder_iife_wrapper_proven(function, scoping, aliases);
    let (decode_function, decode_body, source, direct_guard_end) = if iife {
        let Some(nested) = fixed_decoder_iife_function(outer_body) else {
            return false;
        };
        if nested.r#async
            || nested.generator
            || !function_parameters_have_no_runtime_effects(nested)
        {
            return false;
        }
        let Some(body) = nested.body.as_ref() else {
            return false;
        };
        let Some(BindingPattern::BindingIdentifier(source)) = nested
            .params
            .items
            .first()
            .map(|parameter| &parameter.pattern)
        else {
            return false;
        };
        let Some(source) = source.symbol_id.get() else {
            return false;
        };
        (nested, body, source, None)
    } else {
        if !fixed_decoder_control_shape(outer_body) {
            return false;
        }
        let Some((source, guard_end)) = fixed_base64_direct_source(function, scoping) else {
            return false;
        };
        (function, outer_body, source, Some(guard_end))
    };

    if let Some(guard_end) = direct_guard_end {
        for reference_id in scoping.get_resolved_reference_ids(source) {
            let Some(span) = reference_spans.get(reference_id) else {
                return false;
            };
            if guard_end <= span.start
                && span.end <= decode_body.span.end
                && scoping.get_reference(*reference_id).is_write()
            {
                return false;
            }
        }
    }

    let loops = decode_body
        .statements
        .iter()
        .filter_map(|statement| match statement {
            Statement::ForStatement(statement) => Some(statement.as_ref()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [for_statement] = loops.as_slice() else {
        return false;
    };
    if for_statement.update.is_some() {
        return false;
    }
    let Some(expressions) = fixed_base64_loop_expressions(&for_statement.body) else {
        return false;
    };
    let [compute0, compute1, compute2, append0, append1, append2] = expressions.as_slice() else {
        return false;
    };
    let mut evaluator = FixedBase64Eval {
        scoping,
        values: HashMap::new(),
        alphabet: None,
        input: None,
        cursor: None,
        next_sextet: 0,
    };
    if evaluator.value(compute0).is_none()
        || evaluator.value(compute1).is_none()
        || evaluator.value(compute2).is_none()
        || evaluator.next_sextet != 4
    {
        return false;
    }
    let expected = fixed_base64_expected_bytes();
    let Some((output, first)) = fixed_base64_append(append0, &mut evaluator) else {
        return false;
    };
    let Some((second_output, second)) = fixed_base64_sentinel_append(append1, &mut evaluator, 2)
    else {
        return false;
    };
    let Some((third_output, third)) = fixed_base64_sentinel_append(append2, &mut evaluator, 3)
    else {
        return false;
    };
    if output != second_output || output != third_output || [first, second, third] != expected {
        return false;
    }
    let (Some(alphabet_symbol), Some(input), Some(cursor)) =
        (evaluator.alphabet, evaluator.input, evaluator.cursor)
    else {
        return false;
    };
    let setup = FixedBase64SetupProof {
        function_span: decode_function.span,
        alphabet: alphabet_symbol,
        input,
        cursor,
        output,
        source,
        expected_alphabet: alphabet,
        scoping,
        aliases,
    };
    if !setup.loop_initializer_proven(for_statement)
        || !setup.surrounding_statements_proven(decode_body, !iife)
    {
        return false;
    }
    let Some(Expression::BinaryExpression(test)) = for_statement.test.as_ref().map(unparenthesized)
    else {
        return false;
    };
    let loop_test = match test.operator.as_str() {
        "<" => {
            statically_resolved_identifier_symbol(&test.left, scoping) == Some(cursor)
                && matches!(unparenthesized(&test.right), Expression::StaticMemberExpression(member)
                    if !member.optional
                        && member.property.name.as_str() == "length"
                        && statically_resolved_identifier_symbol(&member.object, scoping) == Some(input))
        }
        ">" => {
            statically_resolved_identifier_symbol(&test.right, scoping) == Some(cursor)
                && matches!(unparenthesized(&test.left), Expression::StaticMemberExpression(member)
                    if !member.optional
                        && member.property.name.as_str() == "length"
                        && statically_resolved_identifier_symbol(&member.object, scoping) == Some(input))
        }
        _ => false,
    };
    if !loop_test {
        return false;
    }
    let Some(Statement::ReturnStatement(return_statement)) = decode_body.statements.last() else {
        return false;
    };
    if return_statement
        .argument
        .as_ref()
        .and_then(|expression| statically_resolved_identifier_symbol(expression, scoping))
        != Some(output)
    {
        return false;
    }
    fixed_base64_setup_proven(decode_body, for_statement.body.span().start, &setup)
        && (!iife || fixed_decoder_iife_calls_proven(decode_function, scoping, aliases))
}
