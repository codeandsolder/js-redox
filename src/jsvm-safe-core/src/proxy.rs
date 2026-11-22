use crate::binding_facts::BindingFacts;
use crate::value_eval::{eval, exact_property_key, is_prototype_setter, Value};
use crate::{direct_identifier_name, reference_is_statically_resolved_read};
use oxc_ast::ast::{
    BindingPattern, ComputedMemberExpression, Expression, PropertyKind, Statement,
    StaticMemberExpression,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping};
use oxc_syntax::symbol::SymbolId;
use std::collections::{HashMap, HashSet};

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
    refs: HashMap<ReferenceId, Option<String>>,
}

impl MemberReferenceCollector {
    fn record_object(&mut self, object: &Expression<'_>, key: Option<String>) {
        let Expression::Identifier(id) = object else {
            return;
        };
        if let Some(reference_id) = id.reference_id.get() {
            self.refs.insert(reference_id, key);
        }
    }
}

impl<'a> Visit<'a> for MemberReferenceCollector {
    fn visit_static_member_expression(&mut self, it: &StaticMemberExpression<'a>) {
        self.record_object(&it.object, Some(it.property.name.to_string()));
        walk::walk_static_member_expression(self, it);
    }

    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        self.record_object(
            &it.object,
            eval(&it.expression).and_then(|value| value.js_string()),
        );
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
            BindingPattern::BindingIdentifier(id) if param.initializer.is_none() => {
                Some(id.name.as_str())
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;

    if params.iter().copied().collect::<HashSet<_>>().len() != params.len() {
        return None;
    }
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
    if call.optional
        || crate::is_potential_direct_eval(call)
        || call.arguments.len() + 1 != params.len()
    {
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
            // A spread can overwrite any earlier own key.
            properties.clear();
            continue;
        };
        let key = exact_property_key(&prop.key, prop.computed, eval);
        let Some(key) = key else {
            properties.clear();
            continue;
        };
        if is_prototype_setter(prop, &key) {
            // The special colon-form prototype setter does not write an own property.
            continue;
        }
        // Later definitions replace earlier facts, including accessors and
        // unmodeled values. Never retain a stale value after a key collision.
        properties.remove(&key);
        if prop.kind != PropertyKind::Init {
            continue;
        }
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
    member_refs: &'s HashMap<ReferenceId, Option<String>>,
    facts: &'c BindingFacts,
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
            if refs.is_empty()
                || !self.facts.is_private(self.scoping, symbol)
                || !self.scoping.symbol_redeclarations(symbol).is_empty()
            {
                continue;
            }
            let properties = analyze_proxy_object(object);
            // All actual member uses must be own, modeled data properties.
            // An unmodeled getter/method could mutate the receiver even when
            // Oxc records only a read reference to the binding.
            if !refs.iter().all(|reference| {
                reference_is_statically_resolved_read(self.scoping, *reference, symbol)
                    && self
                        .member_refs
                        .get(reference)
                        .and_then(Option::as_ref)
                        .is_some_and(|key| properties.contains_key(key))
            }) {
                continue;
            }
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
    facts: &BindingFacts,
) -> HashMap<SymbolId, ProxyObject> {
    let mut member_collector = MemberReferenceCollector::default();
    member_collector.visit_program(program);

    let mut collector = ProxyObjectCollector {
        scoping,
        member_refs: &member_collector.refs,
        facts,
        objects: HashMap::new(),
    };
    collector.visit_program(program);
    collector.objects
}

pub fn static_proxy_member<'a>(
    expr: &'a Expression<'a>,
    scoping: &Scoping,
    facts: &BindingFacts,
) -> Option<(SymbolId, String)> {
    match expr {
        Expression::StaticMemberExpression(member) if !member.optional => Some((
            facts.initialized_read(scoping, &member.object)?,
            member.property.name.to_string(),
        )),
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Value::String(key) = eval(&member.expression)? else {
                return None;
            };
            Some((facts.initialized_read(scoping, &member.object)?, key))
        }
        _ => None,
    }
}
