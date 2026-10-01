use oxc_ast::ast::{
    Argument, AssignmentExpression, BindingPattern, CallExpression, ConditionalExpression,
    Expression, Function, FunctionBody, ObjectExpression, ObjectPropertyKind, PropertyKind,
    Statement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::Span;

#[derive(Debug)]
pub(crate) struct StructuralSignal {
    pub kind: &'static str,
    pub weight: u32,
    pub span: Span,
    pub subject: Option<String>,
    pub detail: String,
}

type CallDetector = fn(&CallExpression<'_>) -> Option<StructuralSignal>;
type ObjectDetector = fn(&ObjectExpression<'_>) -> Option<StructuralSignal>;

const CALL_DETECTORS: &[CallDetector] = &[
    detect_array_rotation,
    detect_rotation_checksum_iife,
    detect_one_shot_wrapper,
];

const OBJECT_DETECTORS: &[ObjectDetector] = &[detect_operator_proxy_table];

pub(crate) fn call_signals(call: &CallExpression<'_>) -> Vec<StructuralSignal> {
    CALL_DETECTORS
        .iter()
        .filter_map(|detector| detector(call))
        .collect()
}

pub(crate) fn object_signals(object: &ObjectExpression<'_>) -> Vec<StructuralSignal> {
    OBJECT_DETECTORS
        .iter()
        .filter_map(|detector| detector(object))
        .collect()
}

fn literal_member<'a>(expr: &'a Expression<'a>) -> Option<(&'a Expression<'a>, &'a str)> {
    match expr {
        Expression::StaticMemberExpression(member) if !member.optional => {
            Some((&member.object, member.property.name.as_str()))
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = &member.expression else {
                return None;
            };
            Some((&member.object, property.value.as_str()))
        }
        _ => None,
    }
}

fn direct_identifier<'a>(expr: &'a Expression<'a>) -> Option<&'a str> {
    match expr {
        Expression::Identifier(identifier) => Some(identifier.name.as_str()),
        _ => None,
    }
}

fn array_rotation_subject(call: &CallExpression<'_>) -> Option<String> {
    if call.optional || call.arguments.len() != 1 {
        return None;
    }
    let (outer_object, outer_name) = literal_member(&call.callee)?;
    if outer_name != "push" {
        return None;
    }
    let subject = direct_identifier(outer_object)?;
    let Argument::CallExpression(inner_call) = &call.arguments[0] else {
        return None;
    };
    if inner_call.optional || !inner_call.arguments.is_empty() {
        return None;
    }
    let (inner_object, inner_name) = literal_member(&inner_call.callee)?;
    if inner_name != "shift" || direct_identifier(inner_object) != Some(subject) {
        return None;
    }
    Some(subject.to_string())
}

fn detect_array_rotation(call: &CallExpression<'_>) -> Option<StructuralSignal> {
    let subject = array_rotation_subject(call)?;
    Some(StructuralSignal {
        kind: "array_rotation",
        weight: 8,
        span: call.span,
        subject: Some(subject),
        detail: "same-array push(shift()) rotation".to_string(),
    })
}

fn function_expression<'a>(expr: &'a Expression<'a>) -> Option<&'a Function<'a>> {
    match expr {
        Expression::FunctionExpression(function) => Some(function),
        Expression::ParenthesizedExpression(parenthesized) => {
            function_expression(&parenthesized.expression)
        }
        _ => None,
    }
}

#[derive(Default)]
struct RotationBootstrapProbe {
    rotations: usize,
    parse_int_calls: usize,
    try_statements: usize,
    breaks: usize,
    constant_true_loops: usize,
}

impl<'a> Visit<'a> for RotationBootstrapProbe {
    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        if array_rotation_subject(it).is_some() {
            self.rotations += 1;
        }
        if matches!(&it.callee, Expression::Identifier(identifier) if identifier.name.as_str() == "parseInt")
        {
            self.parse_int_calls += 1;
        }
        walk::walk_call_expression(self, it);
    }

    fn visit_try_statement(&mut self, it: &oxc_ast::ast::TryStatement<'a>) {
        self.try_statements += 1;
        walk::walk_try_statement(self, it);
    }

    fn visit_break_statement(&mut self, it: &oxc_ast::ast::BreakStatement<'a>) {
        self.breaks += 1;
        walk::walk_break_statement(self, it);
    }

    fn visit_while_statement(&mut self, it: &oxc_ast::ast::WhileStatement<'a>) {
        if expression_is_static_true(&it.test) {
            self.constant_true_loops += 1;
        }
        walk::walk_while_statement(self, it);
    }

    fn visit_for_statement(&mut self, it: &oxc_ast::ast::ForStatement<'a>) {
        if it.test.as_ref().is_none_or(expression_is_static_true) {
            self.constant_true_loops += 1;
        }
        walk::walk_for_statement(self, it);
    }
}

fn detect_rotation_checksum_iife(call: &CallExpression<'_>) -> Option<StructuralSignal> {
    if call.optional || call.arguments.len() != 2 {
        return None;
    }
    let Argument::Identifier(provider) = &call.arguments[0] else {
        return None;
    };
    if !matches!(
        &call.arguments[1],
        Argument::NumericLiteral(number)
            if number.value.is_finite() && number.value.fract() == 0.0
    ) {
        return None;
    }
    let function = function_expression(&call.callee)?;
    if function.generator || function.r#async || function.params.items.len() < 2 {
        return None;
    }
    let body = function.body.as_ref()?;
    let mut probe = RotationBootstrapProbe::default();
    probe.visit_function_body(body);
    if probe.rotations < 1
        || probe.parse_int_calls < 3
        || probe.try_statements < 1
        || probe.breaks < 1
        || probe.constant_true_loops < 1
    {
        return None;
    }

    Some(StructuralSignal {
        kind: "rotation_checksum_iife",
        weight: 12 + (probe.rotations as u32).min(4) + ((probe.parse_int_calls / 3) as u32).min(4),
        span: call.span,
        subject: Some(provider.name.to_string()),
        detail: format!(
            "{} same-array rotation(s), {} parseInt call(s), {} try block(s), {} break(s), {} constant-true loop(s)",
            probe.rotations,
            probe.parse_int_calls,
            probe.try_statements,
            probe.breaks,
            probe.constant_true_loops
        ),
    })
}

fn expression_is_static_true(expr: &Expression<'_>) -> bool {
    matches!(expr, Expression::BooleanLiteral(value) if value.value)
        || is_obfuscated_bool(expr, true)
}

fn is_obfuscated_bool(expr: &Expression<'_>, expected: bool) -> bool {
    let Expression::UnaryExpression(outer) = expr else {
        return false;
    };
    if outer.operator.as_str() != "!" {
        return false;
    }
    if !expected {
        return matches!(&outer.argument, Expression::ArrayExpression(array) if array.elements.is_empty());
    }
    let Expression::UnaryExpression(inner) = &outer.argument else {
        return false;
    };
    inner.operator.as_str() == "!"
        && matches!(&inner.argument, Expression::ArrayExpression(array) if array.elements.is_empty())
}

struct OneShotProbe<'g> {
    guard: &'g str,
    guarded_conditional: bool,
    guard_disabled: bool,
}

impl<'a> Visit<'a> for OneShotProbe<'_> {
    fn visit_conditional_expression(&mut self, it: &ConditionalExpression<'a>) {
        if direct_identifier(&it.test) == Some(self.guard) {
            self.guarded_conditional = true;
        }
        walk::walk_conditional_expression(self, it);
    }

    fn visit_assignment_expression(&mut self, it: &AssignmentExpression<'a>) {
        if matches!(
            &it.left,
            oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(identifier)
                if identifier.name.as_str() == self.guard
        ) && is_obfuscated_bool(&it.right, false)
        {
            self.guard_disabled = true;
        }
        walk::walk_assignment_expression(self, it);
    }
}

fn returned_function_body<'a>(expr: &'a Expression<'a>) -> Option<&'a FunctionBody<'a>> {
    match expr {
        Expression::FunctionExpression(function) => function.body.as_deref(),
        Expression::ArrowFunctionExpression(function) => Some(&function.body),
        _ => None,
    }
}

fn one_shot_guard(function: &Function<'_>) -> Option<String> {
    if function.generator || function.r#async || !function.params.items.is_empty() {
        return None;
    }
    let body = function.body.as_ref()?;
    let [Statement::VariableDeclaration(declaration), Statement::ReturnStatement(ret)] =
        body.statements.as_slice()
    else {
        return None;
    };
    if declaration.declarations.len() != 1 {
        return None;
    }
    let declarator = &declaration.declarations[0];
    let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
        return None;
    };
    let initializer = declarator.init.as_ref()?;
    if !is_obfuscated_bool(initializer, true) {
        return None;
    }
    let inner_body = returned_function_body(ret.argument.as_ref()?)?;
    let guard = identifier.name.to_string();
    let mut probe = OneShotProbe {
        guard: &guard,
        guarded_conditional: false,
        guard_disabled: false,
    };
    probe.visit_function_body(inner_body);
    (probe.guarded_conditional && probe.guard_disabled).then_some(guard)
}

fn detect_one_shot_wrapper(call: &CallExpression<'_>) -> Option<StructuralSignal> {
    if call.optional || !call.arguments.is_empty() {
        return None;
    }
    let function = function_expression(&call.callee)?;
    let guard = one_shot_guard(function)?;
    Some(StructuralSignal {
        kind: "one_shot_wrapper",
        weight: 10,
        span: call.span,
        subject: Some(guard),
        detail: "obfuscated boolean guard returns a function and disables itself after first use"
            .to_string(),
    })
}

fn is_proxy_return_expression(expr: &Expression<'_>) -> bool {
    matches!(
        expr,
        Expression::BinaryExpression(_)
            | Expression::LogicalExpression(_)
            | Expression::UnaryExpression(_)
            | Expression::ConditionalExpression(_)
            | Expression::CallExpression(_)
    )
}

fn is_tiny_proxy_function(expr: &Expression<'_>) -> bool {
    match expr {
        Expression::FunctionExpression(function) => {
            if function.generator || function.r#async {
                return false;
            }
            let Some(body) = function.body.as_ref() else {
                return false;
            };
            if !body.directives.is_empty() || body.statements.len() != 1 {
                return false;
            }
            matches!(
                &body.statements[0],
                Statement::ReturnStatement(ret)
                    if ret.argument.as_ref().is_some_and(is_proxy_return_expression)
            )
        }
        Expression::ArrowFunctionExpression(function) => {
            if function.r#async || !function.body.directives.is_empty() {
                return false;
            }
            if let Some(returned) = function.get_expression() {
                return is_proxy_return_expression(returned);
            }
            matches!(
                function.body.statements.as_slice(),
                [Statement::ReturnStatement(ret)]
                    if ret.argument.as_ref().is_some_and(is_proxy_return_expression)
            )
        }
        _ => false,
    }
}

fn looks_generated_proxy_key(name: &str) -> bool {
    let len = name.len();
    (4..=8).contains(&len)
        && name
            .bytes()
            .all(|byte| byte == b'_' || byte == b'$' || byte.is_ascii_alphanumeric())
        && name
            .bytes()
            .any(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit())
        && name.bytes().any(|byte| byte.is_ascii_lowercase())
        && !super::apiish_name(name)
}

fn detect_operator_proxy_table(object: &ObjectExpression<'_>) -> Option<StructuralSignal> {
    let mut static_properties = 0usize;
    let mut proxy_functions = 0usize;
    let mut generated_keys = 0usize;

    for item in &object.properties {
        let ObjectPropertyKind::ObjectProperty(property) = item else {
            continue;
        };
        if property.kind != PropertyKind::Init
            || property.computed
            || property.method
            || property.shorthand
        {
            continue;
        }
        let Some(key) = property.key.static_name() else {
            continue;
        };
        static_properties += 1;
        if looks_generated_proxy_key(key.as_ref()) {
            generated_keys += 1;
        }
        if is_tiny_proxy_function(&property.value) {
            proxy_functions += 1;
        }
    }

    if static_properties < 6
        || proxy_functions < 4
        || generated_keys < 4
        || proxy_functions * 2 < static_properties
    {
        return None;
    }

    Some(StructuralSignal {
        kind: "operator_proxy_table",
        weight: 6 + (proxy_functions as u32).min(10),
        span: object.span,
        subject: None,
        detail: format!(
            "{proxy_functions}/{static_properties} tiny proxy functions; {generated_keys} generated-looking short keys"
        ),
    })
}
