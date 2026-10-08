use crate::value_eval::{eval, Value};
use crate::{direct_identifier_name, symbol_of};
use oxc_ast::ast::{
    BindingPattern, ComputedMemberExpression, Expression, PropertyKind, Statement,
    StaticMemberExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_syntax::symbol::SymbolId;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum ProxyProperty {
    Literal(Value),
    Unary { operator: String },
    Binary { operator: String },
    StaticMember { property: String },
    ComputedMember,
    Call { arity: usize },
}

pub const fn proxy_literal_kind(value: &Value) -> &'static str {
    if matches!(value, Value::String(_)) {
        "proxy_string"
    } else {
        "proxy_literal"
    }
}

#[derive(Debug, Clone)]
pub struct ProxyObject {
    properties: HashMap<String, ProxyProperty>,
}

impl ProxyObject {
    pub(super) fn get(&self, key: &str) -> Option<&ProxyProperty> {
        self.properties.get(key)
    }
}

#[derive(Default)]
struct MemberReferenceCollector {
    refs: HashMap<ReferenceId, u32>,
}

impl MemberReferenceCollector {
    fn record_object(&mut self, object: &Expression<'_>) {
        let Expression::Identifier(id) = object else {
            return;
        };
        if let Some(reference_id) = id.reference_id.get() {
            self.refs.insert(reference_id, id.span.start);
        }
    }
}

impl<'a> Visit<'a> for MemberReferenceCollector {
    fn visit_static_member_expression(&mut self, it: &StaticMemberExpression<'a>) {
        self.record_object(&it.object);
        walk::walk_static_member_expression(self, it);
    }

    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        self.record_object(&it.object);
        walk::walk_computed_member_expression(self, it);
    }
}

fn analyze_proxy_return(
    params: &oxc_ast::ast::FormalParameters<'_>,
    returned: &Expression<'_>,
) -> Option<ProxyProperty> {
    if params.items.is_empty() || params.rest.is_some() {
        return None;
    }
    let params = params
        .items
        .iter()
        .map(|param| match &param.pattern {
            BindingPattern::BindingIdentifier(id) => Some(id.name.as_str()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;

    if params.len() == 1 {
        if let Expression::UnaryExpression(unary) = returned {
            let operator = unary.operator.as_str();
            if matches!(operator, "!" | "+" | "-" | "~" | "void")
                && direct_identifier_name(&unary.argument)? == params[0]
            {
                return Some(ProxyProperty::Unary {
                    operator: operator.to_string(),
                });
            }
        }
    }

    if params.len() == 1 {
        if let Expression::StaticMemberExpression(member) = returned {
            if !member.optional && direct_identifier_name(&member.object)? == params[0] {
                return Some(ProxyProperty::StaticMember {
                    property: member.property.name.to_string(),
                });
            }
        }
    }

    if params.len() == 2 {
        if let Expression::ComputedMemberExpression(member) = returned {
            if !member.optional
                && direct_identifier_name(&member.object)? == params[0]
                && direct_identifier_name(&member.expression)? == params[1]
            {
                return Some(ProxyProperty::ComputedMember);
            }
        }

        if let Expression::BinaryExpression(binary) = returned {
            if direct_identifier_name(&binary.left)? == params[0]
                && direct_identifier_name(&binary.right)? == params[1]
            {
                return Some(ProxyProperty::Binary {
                    operator: binary.operator.as_str().to_string(),
                });
            }
        }
    }

    let Expression::CallExpression(call) = returned else {
        return None;
    };
    if call.optional || call.arguments.len() + 1 != params.len() {
        return None;
    }
    if direct_identifier_name(&call.callee)? != params[0] {
        return None;
    }
    for (argument, expected) in call.arguments.iter().zip(params.iter().skip(1)) {
        if argument.is_spread() {
            return None;
        }
        let expression = argument.as_expression()?;
        if direct_identifier_name(expression)? != *expected {
            return None;
        }
    }

    Some(ProxyProperty::Call {
        arity: call.arguments.len(),
    })
}

fn analyze_proxy_function(function: &oxc_ast::ast::Function<'_>) -> Option<ProxyProperty> {
    if function.generator || function.r#async {
        return None;
    }
    let body = function.body.as_ref()?;
    if !body.directives.is_empty() || body.statements.len() != 1 {
        return None;
    }
    let Statement::ReturnStatement(ret) = &body.statements[0] else {
        return None;
    };
    analyze_proxy_return(&function.params, ret.argument.as_ref()?)
}

fn analyze_proxy_arrow(
    function: &oxc_ast::ast::ArrowFunctionExpression<'_>,
) -> Option<ProxyProperty> {
    if function.r#async {
        return None;
    }

    if let Some(returned) = function.get_expression() {
        return analyze_proxy_return(&function.params, returned);
    }

    let oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) = &function.body else {
        return None;
    };
    if !body.directives.is_empty() || body.statements.len() != 1 {
        return None;
    }
    let Statement::ReturnStatement(ret) = &body.statements[0] else {
        return None;
    };
    analyze_proxy_return(&function.params, ret.argument.as_ref()?)
}

fn analyze_proxy_object(
    object: &oxc_ast::ast::ObjectExpression<'_>,
) -> HashMap<String, ProxyProperty> {
    let mut properties = HashMap::new();
    for item in &object.properties {
        let oxc_ast::ast::ObjectPropertyKind::ObjectProperty(prop) = item else {
            continue;
        };
        if prop.kind != PropertyKind::Init || prop.computed || prop.method || prop.shorthand {
            continue;
        }
        let Some(key) = prop.key.static_name().map(std::borrow::Cow::into_owned) else {
            continue;
        };
        if let Some(value) = eval(&prop.value) {
            properties.insert(key, ProxyProperty::Literal(value));
            continue;
        }
        let proxy = match &prop.value {
            Expression::FunctionExpression(function) => analyze_proxy_function(function),
            Expression::ArrowFunctionExpression(function) => analyze_proxy_arrow(function),
            _ => None,
        };
        if let Some(proxy) = proxy {
            properties.insert(key, proxy);
        }
    }
    properties
}

struct ProxyObjectCollector<'s, 'c> {
    scoping: &'c Scoping,
    member_refs: &'s HashMap<ReferenceId, u32>,
    objects: HashMap<SymbolId, ProxyObject>,
}

impl<'a> Visit<'a> for ProxyObjectCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for d in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &d.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::ObjectExpression(object)) = &d.init else {
                continue;
            };

            let refs = self.scoping.get_resolved_reference_ids(symbol);
            if refs.is_empty() {
                continue;
            }
            let safe = refs.iter().all(|reference_id| {
                let reference = self.scoping.get_reference(*reference_id);
                !reference.is_write()
                    && !reference.flags().is_member_write_target()
                    && self
                        .member_refs
                        .get(reference_id)
                        .is_some_and(|start| *start >= d.span.end)
            });
            if !safe {
                continue;
            }

            let properties = analyze_proxy_object(object);
            if !properties.is_empty() {
                self.objects.insert(symbol, ProxyObject { properties });
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

pub fn collect_proxy_objects(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, ProxyObject> {
    let mut member_collector = MemberReferenceCollector::default();
    member_collector.visit_program(program);

    let mut collector = ProxyObjectCollector {
        scoping,
        member_refs: &member_collector.refs,
        objects: HashMap::new(),
    };
    collector.visit_program(program);
    collector.objects
}

pub fn static_proxy_member<'a>(
    expr: &'a Expression<'a>,
    scoping: &Scoping,
) -> Option<(SymbolId, String)> {
    match expr {
        Expression::StaticMemberExpression(member) if !member.optional => Some((
            symbol_of(scoping, &member.object)?,
            member.property.name.to_string(),
        )),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Value::String(key) = eval(&member.expression)? else {
                return None;
            };
            Some((symbol_of(scoping, &member.object)?, key))
        }
        _ => None,
    }
}
