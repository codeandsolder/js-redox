//! Effects of defining a fresh ordinary ECMAScript class, rather than
//! constructing one of its instances.

use super::{
    eval, exact_computed_property_key, inert_literal_facts, inert_literal_value,
    literal_property_key, LiteralTypes, Value,
};
use oxc_ast::ast::{
    Class, ClassElement, Expression, MethodDefinitionType, PropertyDefinitionType, PropertyKey,
    Statement,
};

pub(super) fn inert_class_definition(class: &Class<'_>) -> bool {
    class.decorators.is_empty()
        && class.type_parameters.is_none()
        && class.implements.is_empty()
        && !class.r#abstract
        && !class.declare
        && class.heritage.as_ref().is_none_or(|heritage| {
            heritage.type_arguments.is_none() && inert_heritage(&heritage.expression)
        })
        && class.body.body.iter().all(inert_element)
}

/// Heritage is evaluated now and must either be null or a constructor with
/// an independently safe prototype read. Fresh ordinary functions and
/// proven inert class expressions have an own data prototype.
fn inert_heritage(expression: &Expression<'_>) -> bool {
    match expression.without_parentheses() {
        Expression::FunctionExpression(function) => {
            !function.generator && !function.r#async && !function.declare
        }
        Expression::ClassExpression(class) => inert_class_definition(class),
        _ => matches!(eval(expression), Some(Value::Null)),
    }
}

/// A computed name performs `ToPropertyKey` at definition time. A static
/// public name of "prototype" is forbidden even when the key is computed,
/// and may throw before any later definitions or static initializers run.
fn inert_class_key(key: &PropertyKey<'_>, computed: bool, is_static: bool) -> bool {
    if !computed {
        return !is_static || literal_property_key(key).as_deref() != Some("prototype");
    }
    let Some(expression) = key.as_expression() else {
        return false;
    };
    let Some(facts) = inert_literal_facts(expression) else {
        return false;
    };
    let primitive = LiteralTypes::ORDINARY_PRIMITIVE.union(LiteralTypes::BIGINT);
    if !facts.types.subset_of(primitive) {
        return false;
    }
    !is_static
        || !facts.types.includes(LiteralTypes::STRING)
        || exact_computed_property_key(expression, eval).is_some_and(|name| name != "prototype")
}

fn inert_element(element: &ClassElement<'_>) -> bool {
    match element {
        ClassElement::MethodDefinition(method) => {
            method.r#type == MethodDefinitionType::MethodDefinition
                && method.decorators.is_empty()
                && inert_class_key(&method.key, method.computed, method.r#static)
        }
        ClassElement::PropertyDefinition(property) => {
            property.r#type == PropertyDefinitionType::PropertyDefinition
                && !property.declare
                && property.decorators.is_empty()
                && inert_class_key(&property.key, property.computed, property.r#static)
                // Instance initializers execute on construction, not definition.
                && (!property.r#static
                    || property.value.as_ref().is_none_or(inert_literal_value))
        }
        ClassElement::StaticBlock(block) => block.body.iter().all(inert_static_statement),
        ClassElement::AccessorProperty(_) | ClassElement::TSIndexSignature(_) => false,
    }
}

/// Only statements with independent normal-completion/effect proofs may
/// execute inside an inert static block.
fn inert_static_statement(statement: &Statement<'_>) -> bool {
    match statement {
        Statement::EmptyStatement(_) => true,
        Statement::ExpressionStatement(statement) => inert_literal_value(&statement.expression),
        Statement::BlockStatement(block) => block.body.iter().all(inert_static_statement),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::{eval, inert_literal_value, Value};
    use oxc_allocator::Allocator;
    use oxc_ast::ast::Statement;
    use oxc_span::SourceType;

    #[test]
    fn class_definition_effects_are_distinct_from_instance_initialization() {
        for (expression, inert) in [
            ("class {}", true),
            ("class { field = effect() }", true),
            ("class { #field = effect() }", true),
            ("class { m(){effect()} static get x(){effect()} }", true),
            ("class extends null {}", true),
            ("class extends (false ? effect() : null) {}", true),
            ("class extends function(){effect()} {}", true),
            ("class extends (class {}) {}", true),
            ("class { static x = 2 ** 1.5 }", true),
            ("class { static [2 ** 1.5] = 1 }", true),
            ("class { static ['name'] = 1 }", true),
            ("class { static ['__proto__'] = null }", true),
            ("class { ['constructor'](){} }", true),
            ("class { static { ; { 2 ** 1.5; } } }", true),
            ("class { static #x = 1 }", true),
            ("class { static ['prototype'](){} }", false),
            ("class { static ['prototype'] = 1 }", false),
            ("class { static get ['prototype'](){return 1} }", false),
            (
                "class { static [(2 ** 1.5 ? 'prototype' : 'x')] = 1 }",
                false,
            ),
            ("class { [effect()](){} }", false),
            ("class { [{}](){} }", false),
            ("class { static x = effect() }", false),
            ("class { static #x = effect() }", false),
            ("class { static { effect() } }", false),
            ("class { static { throw 1 } }", false),
            ("class extends (effect(), null) {}", false),
            ("class extends (()=>{}) {}", false),
            ("class extends function*(){} {}", false),
            ("class extends async function(){} {}", false),
            ("class extends 1 {}", false),
            ("class extends missing {}", false),
        ] {
            let allocator = Allocator::default();
            let source = format!("typeof ({expression});");
            let program = crate::parse_as(&allocator, &source, SourceType::cjs())
                .unwrap_or_else(|| unreachable!("valid class fixture: {source}"));
            let [Statement::ExpressionStatement(statement)] = program.body.as_slice() else {
                unreachable!("one expression");
            };
            assert_eq!(
                inert_literal_value(&statement.expression),
                inert,
                "{source}"
            );
            assert_eq!(
                matches!(eval(&statement.expression), Some(Value::String(value)) if value == "function"),
                inert,
                "{source}"
            );
        }
    }
}
