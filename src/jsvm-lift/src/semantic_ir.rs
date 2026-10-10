use crate::effect_shape::{analyze_program, hash_shape_text, PropertyMode};
use oxc_allocator::Allocator;
use oxc_ast::ast::{Argument, AssignmentTarget, Expression, Statement};
use oxc_span::{GetSpan, SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;

#[derive(Debug, Serialize)]
pub struct IrOp {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub callee: Option<String>,
    pub source: String,
    pub shape_hash: String,
    pub coarse_shape_hash: String,
    pub confidence: f64,
    pub provenance: &'static str,
}

fn parse_shape_mode(source: &str, property_mode: PropertyMode) -> String {
    for candidate in [
        source.to_string(),
        format!("({source})"),
        format!("function __ir_wrap(){{{source}}}"),
    ] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &candidate, SourceType::cjs());
        if parsed.is_clean() {
            return analyze_program(&parsed.program, property_mode).text;
        }
    }
    "PARSEFAIL".to_string()
}

fn parse_shape(source: &str) -> String {
    parse_shape_mode(source, PropertyMode::Literal)
}

fn coarse_shape_hash(source: &str) -> String {
    format!(
        "{:016x}",
        hash_shape_text(&parse_shape_mode(source, PropertyMode::Opaque))
    )
}

fn fragment(source: &str, span: Span) -> String {
    source
        .get(span.start as usize..(span.end as usize).min(source.len()))
        .unwrap_or_default()
        .to_string()
}

fn expr_root_name(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::Identifier(id) => Some(id.name.to_string()),
        Expression::ParenthesizedExpression(p) => expr_root_name(&p.expression),
        Expression::AssignmentExpression(a) => expr_root_name(&a.right),
        Expression::SequenceExpression(s) => s.expressions.last().and_then(expr_root_name),
        _ => None,
    }
}

fn argument_source(source: &str, arg: &Argument<'_>) -> String {
    fragment(source, arg.span())
}

fn new_op(kind: impl Into<String>, source: &str, shape_hash: &str, confidence: f64) -> IrOp {
    IrOp {
        kind: kind.into(),
        target: None,
        index: None,
        value: None,
        callee: None,
        source: source.to_string(),
        shape_hash: shape_hash.to_string(),
        coarse_shape_hash: coarse_shape_hash(source),
        confidence,
        provenance: "role_normalized_handler_effect",
    }
}

fn classify_assignment(
    source: &str,
    a: &oxc_ast::ast::AssignmentExpression<'_>,
    hash: &str,
) -> IrOp {
    let rhs = fragment(source, a.right.span());
    let op = a.operator.as_str();

    if let Some(name) = a.left.get_identifier_name() {
        if name == "ip" && op == "+=" {
            let mut out = new_op("ip_advance", source, hash, 1.0);
            out.target = Some("ip".into());
            out.value = Some(rhs);
            return out;
        }
        if name == "argc" && op == "=" {
            let mut out = new_op("set_argc", source, hash, 1.0);
            out.target = Some("argc".into());
            out.value = Some(rhs);
            return out;
        }

        let semantic_role = matches!(
            name,
            "ip" | "opcode"
                | "op1"
                | "op2"
                | "op3"
                | "stack"
                | "env"
                | "tmp"
                | "args"
                | "argc"
                | "control"
        );
        let mut out = new_op(
            if semantic_role {
                "set_role"
            } else {
                "local_assign"
            },
            source,
            hash,
            if semantic_role { 0.95 } else { 0.65 },
        );
        out.target = Some(name.to_string());
        out.value = Some(rhs);
        return out;
    }

    match &a.left {
        AssignmentTarget::ComputedMemberExpression(cm) => {
            let container = expr_root_name(&cm.object);
            let index = fragment(source, cm.expression.span());
            let kind = match container.as_deref() {
                Some("env") => "env_store",
                Some("tmp") => "tmp_store",
                Some("stack") => "stack_store",
                Some("control") => "control_store",
                Some("args") => "args_store",
                _ => "computed_store",
            };
            let confidence = if kind == "computed_store" { 0.7 } else { 1.0 };
            let mut out = new_op(kind, source, hash, confidence);
            out.target = container;
            out.index = Some(index);
            out.value = Some(rhs);
            out
        }
        AssignmentTarget::StaticMemberExpression(sm) => {
            let container = expr_root_name(&sm.object);
            let mut out = new_op("property_store", source, hash, 0.8);
            out.target = container;
            out.index = Some(sm.property.name.to_string());
            out.value = Some(rhs);
            out
        }
        _ => new_op("raw_js", source, hash, 0.0),
    }
}

fn classify_call(source: &str, call: &oxc_ast::ast::CallExpression<'_>, hash: &str) -> IrOp {
    let callee = expr_root_name(&call.callee);
    let first_role = call.arguments.first().and_then(|arg| match arg {
        Argument::Identifier(id) => Some(id.name.to_string()),
        Argument::ParenthesizedExpression(p) => expr_root_name(&p.expression),
        _ => None,
    });

    if callee.as_deref() == Some("stack_push") {
        let mut out = new_op("stack_push", source, hash, 1.0);
        out.target = Some("stack".into());
        out.value = call
            .arguments
            .first()
            .map(|arg| argument_source(source, arg));
        out.callee = callee;
        return out;
    }
    if callee.as_deref() == Some("stack_pop") {
        let mut out = new_op("stack_pop", source, hash, 1.0);
        out.target = Some("stack".into());
        out.callee = callee;
        return out;
    }
    if callee.as_deref() == Some("push") && first_role.as_deref() == Some("stack") {
        let mut out = new_op("stack_push", source, hash, 1.0);
        out.target = Some("stack".into());
        out.value = call
            .arguments
            .get(1)
            .map(|arg| argument_source(source, arg));
        out.callee = callee;
        return out;
    }
    if callee.as_deref() == Some("pop") && first_role.as_deref() == Some("stack") {
        let mut out = new_op("stack_pop", source, hash, 1.0);
        out.target = Some("stack".into());
        out.callee = callee;
        return out;
    }
    if callee.as_deref() == Some("splice") && first_role.as_deref() == Some("stack") {
        let mut out = new_op("stack_splice", source, hash, 0.95);
        out.target = Some("stack".into());
        out.callee = callee;
        return out;
    }

    let mut out = new_op(
        if callee.is_some() {
            "helper_call"
        } else {
            "dynamic_call"
        },
        source,
        hash,
        if callee.is_some() { 0.75 } else { 0.55 },
    );
    out.callee = callee;
    out
}

pub fn classify_effect(source: &str) -> IrOp {
    let shape = parse_shape(source);
    let hash = format!("{:016x}", hash_shape_text(&shape));
    let trimmed = source.trim();

    if trimmed.starts_with("return") {
        let mut out = new_op("return", source, &hash, 1.0);
        out.value = trimmed
            .strip_prefix("return")
            .map(str::trim)
            .filter(|x| !x.is_empty())
            .map(str::to_string);
        return out;
    }
    if trimmed.starts_with("throw") {
        let mut out = new_op("throw", source, &hash, 1.0);
        out.value = trimmed
            .strip_prefix("throw")
            .map(str::trim)
            .filter(|x| !x.is_empty())
            .map(str::to_string);
        return out;
    }
    if trimmed.contains("yield") && trimmed.contains("stack_push") {
        return new_op("yield_resume", source, &hash, 0.95);
    }

    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::cjs());
    if !parsed.is_clean() || parsed.program.body.len() != 1 {
        return new_op("raw_js", source, &hash, 0.0);
    }

    match &parsed.program.body[0] {
        Statement::ExpressionStatement(es) => match &es.expression {
            Expression::AssignmentExpression(a) => classify_assignment(source, a, &hash),
            Expression::CallExpression(call) => classify_call(source, call, &hash),
            Expression::NewExpression(_) => new_op("construct", source, &hash, 0.8),
            Expression::StaticMemberExpression(member) => {
                let mut out = new_op("property_read", source, &hash, 0.9);
                out.target = expr_root_name(&member.object);
                out.index = Some(member.property.name.to_string());
                out
            }
            Expression::ComputedMemberExpression(member) => {
                let mut out = new_op("computed_read", source, &hash, 0.85);
                out.target = expr_root_name(&member.object);
                out.index = Some(fragment(source, member.expression.span()));
                out
            }
            Expression::UpdateExpression(update) => {
                let target = fragment(source, update.argument.span());
                let kind = if target == "ip" && update.operator.as_str() == "++" {
                    "ip_advance"
                } else if target == "sp" {
                    "stack_pointer_update"
                } else {
                    "update"
                };
                let mut out = new_op(
                    kind,
                    source,
                    &hash,
                    if kind == "update" { 0.85 } else { 1.0 },
                );
                out.target = Some(target);
                out.value = Some(update.operator.as_str().to_string());
                out
            }
            Expression::ConditionalExpression(_) | Expression::LogicalExpression(_)
                if source.contains("ip") =>
            {
                new_op("conditional_branch", source, &hash, 0.95)
            }
            _ => new_op("raw_expression", source, &hash, 0.25),
        },
        Statement::FunctionDeclaration(_) => new_op("function_create", source, &hash, 0.9),
        Statement::BreakStatement(_) => new_op("break", source, &hash, 1.0),
        Statement::ContinueStatement(_) => new_op("continue", source, &hash, 1.0),
        Statement::BlockStatement(_) => new_op("block_region", source, &hash, 0.5),
        Statement::TryStatement(_) => new_op("try_region", source, &hash, 0.4),
        Statement::IfStatement(_) | Statement::SwitchStatement(_) => {
            new_op("control_region", source, &hash, 0.4)
        }
        Statement::ForStatement(_)
        | Statement::ForInStatement(_)
        | Statement::ForOfStatement(_)
        | Statement::WhileStatement(_)
        | Statement::DoWhileStatement(_) => new_op("loop_region", source, &hash, 0.4),
        Statement::LabeledStatement(_) => new_op("labeled_region", source, &hash, 0.35),
        Statement::VariableDeclaration(_) => new_op("local_declaration", source, &hash, 0.5),
        _ => new_op("raw_js", source, &hash, 0.0),
    }
}
