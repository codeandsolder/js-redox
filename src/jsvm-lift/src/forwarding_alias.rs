use crate::forwarding_semantics::structurally_proven_forwarding_installers;
use jsvm_safe_core::string_literal_value;
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, BindingPattern, Expression, Function, ReturnStatement,
    Statement, VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use rolldown_redox::ecmascript::parse_program;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaticAliasInstallerCall {
    pub start: u32,
    pub end: u32,
    pub installer: String,
    pub resolver: String,
    pub resolver_member: Option<String>,
    pub source_property: String,
    pub target_selector: u8,
    pub alias_property: String,
    /// The installer contains a structurally proven live getter/setter forwarding path.
    /// This does not imply that this invocation successfully installs that forwarding.
    pub forwarding_installer_proven: bool,
    /// Reserved for call-specific proof that alias substitution is sound.
    pub semantics_proven: bool,
}

#[derive(Debug, Clone)]
struct ResolverShape {
    name: String,
    member: Option<String>,
}

#[derive(Default)]
struct ArgumentsBoxCollector {
    boxes: HashMap<SymbolId, u32>,
    arguments_references: usize,
}

impl<'a> Visit<'a> for ArgumentsBoxCollector {
    fn visit_variable_declaration(&mut self, it: &VariableDeclaration<'a>) {
        for declaration in &it.declarations {
            let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                continue;
            };
            let Some(Expression::ArrayExpression(array)) = &declaration.init else {
                continue;
            };
            if array.elements.len() != 1 {
                continue;
            }
            let ArrayExpressionElement::Identifier(value) = &array.elements[0] else {
                continue;
            };
            if value.name.as_str() != "arguments" {
                continue;
            }
            if let Some(symbol) = id.symbol_id.get() {
                self.boxes.insert(symbol, declaration.span.start);
            }
        }
        walk::walk_variable_declaration(self, it);
    }

    fn visit_identifier_reference(&mut self, it: &oxc_ast::ast::IdentifierReference<'a>) {
        if it.name.as_str() == "arguments" {
            self.arguments_references += 1;
        }
    }

    fn visit_function(&mut self, _it: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
}

fn only_unconditional_statements(statements: &[Statement<'_>]) -> bool {
    statements.iter().all(|statement| match statement {
        Statement::BlockStatement(block) => only_unconditional_statements(&block.body),
        Statement::VariableDeclaration(_)
        | Statement::ExpressionStatement(_)
        | Statement::ReturnStatement(_)
        | Statement::EmptyStatement(_)
        | Statement::DebuggerStatement(_) => true,
        _ => false,
    })
}

#[derive(Default)]
struct ReturnLocationCollector {
    count: usize,
    start: Option<u32>,
}

impl<'a> Visit<'a> for ReturnLocationCollector {
    fn visit_return_statement(&mut self, it: &ReturnStatement<'a>) {
        self.count += 1;
        if self.count == 1 {
            self.start = Some(it.span.start);
        }
    }

    fn visit_function(&mut self, _it: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
}

fn reference_symbol(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(id) = expression else {
        return None;
    };
    scoping.get_reference(id.reference_id.get()?).symbol_id()
}

fn is_zero_index(expression: &Expression<'_>) -> bool {
    matches!(expression, Expression::NumericLiteral(number) if number.value == 0.0)
}

fn is_first_argument(
    scoping: &Scoping,
    expression: &Expression<'_>,
    parameter: SymbolId,
    argument_boxes: &HashSet<SymbolId>,
) -> bool {
    if reference_symbol(scoping, expression) == Some(parameter) {
        return true;
    }

    let Expression::ComputedMemberExpression(outer) = expression else {
        return false;
    };
    if outer.optional || !is_zero_index(&outer.expression) {
        return false;
    }

    let Expression::ComputedMemberExpression(inner) = &outer.object else {
        return false;
    };
    if inner.optional || !is_zero_index(&inner.expression) {
        return false;
    }
    reference_symbol(scoping, &inner.object).is_some_and(|symbol| argument_boxes.contains(&symbol))
}

fn resolver_member(
    scoping: &Scoping,
    returned: &Expression<'_>,
    parameter: SymbolId,
    argument_boxes: &HashSet<SymbolId>,
) -> Option<Option<String>> {
    if is_first_argument(scoping, returned, parameter, argument_boxes) {
        return Some(None);
    }

    let Expression::StaticMemberExpression(member) = returned else {
        return None;
    };
    if member.optional || !is_first_argument(scoping, &member.object, parameter, argument_boxes) {
        return None;
    }
    Some(Some(member.property.name.to_string()))
}

struct ReturnShapeCollector<'c, 'b> {
    scoping: &'c Scoping,
    parameter: SymbolId,
    argument_boxes: &'b HashSet<SymbolId>,
    returns: usize,
    member: Option<Option<String>>,
    invalid: bool,
}

impl<'a> Visit<'a> for ReturnShapeCollector<'_, '_> {
    fn visit_return_statement(&mut self, it: &ReturnStatement<'a>) {
        self.returns += 1;
        let Some(argument) = &it.argument else {
            self.invalid = true;
            return;
        };
        let Some(member) =
            resolver_member(self.scoping, argument, self.parameter, self.argument_boxes)
        else {
            self.invalid = true;
            return;
        };
        if self.returns == 1 {
            self.member = Some(member);
        } else {
            self.invalid = true;
        }
    }

    fn visit_function(&mut self, _it: &Function<'a>, _flags: ScopeFlags) {}

    fn visit_arrow_function_expression(&mut self, _it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
    }
}

struct ResolverCollector<'c> {
    scoping: &'c Scoping,
    resolvers: HashMap<SymbolId, ResolverShape>,
}

impl<'a> Visit<'a> for ResolverCollector<'_> {
    fn visit_function(&mut self, it: &Function<'a>, flags: ScopeFlags) {
        if !it.r#async && !it.generator && it.params.rest.is_none() && it.params.items.len() == 1 {
            if let (Some(id), Some(body)) = (&it.id, &it.body) {
                let Some(function_symbol) = id.symbol_id.get() else {
                    walk::walk_function(self, it, flags);
                    return;
                };
                let BindingPattern::BindingIdentifier(parameter) = &it.params.items[0].pattern
                else {
                    walk::walk_function(self, it, flags);
                    return;
                };
                let Some(parameter_symbol) = parameter.symbol_id.get() else {
                    walk::walk_function(self, it, flags);
                    return;
                };

                if !only_unconditional_statements(&body.statements) {
                    walk::walk_function(self, it, flags);
                    return;
                }
                let mut return_locations = ReturnLocationCollector::default();
                return_locations.visit_function_body(body);
                if return_locations.count != 1 {
                    walk::walk_function(self, it, flags);
                    return;
                }
                let Some(return_start) = return_locations.start else {
                    walk::walk_function(self, it, flags);
                    return;
                };

                let mut box_collector = ArgumentsBoxCollector::default();
                box_collector.visit_function_body(body);
                let declared_boxes = box_collector.boxes.len();
                box_collector.boxes.retain(|symbol, declaration_start| {
                    if *declaration_start >= return_start {
                        return false;
                    }
                    let references = self.scoping.get_resolved_reference_ids(*symbol);
                    if references.len() != 1 {
                        return false;
                    }
                    let reference = self.scoping.get_reference(references[0]);
                    reference.is_read()
                        && !reference.is_write()
                        && !reference.flags().is_member_write_target()
                });
                let argument_boxes = box_collector.boxes.keys().copied().collect::<HashSet<_>>();
                let parameter_is_read_only = self
                    .scoping
                    .get_resolved_reference_ids(parameter_symbol)
                    .iter()
                    .all(|reference_id| {
                        let reference = self.scoping.get_reference(*reference_id);
                        !reference.is_write() && !reference.flags().is_member_write_target()
                    });
                if !parameter_is_read_only || box_collector.arguments_references != declared_boxes {
                    walk::walk_function(self, it, flags);
                    return;
                }
                let mut return_collector = ReturnShapeCollector {
                    scoping: self.scoping,
                    parameter: parameter_symbol,
                    argument_boxes: &argument_boxes,
                    returns: 0,
                    member: None,
                    invalid: false,
                };
                return_collector.visit_function_body(body);

                if !return_collector.invalid && return_collector.returns == 1 {
                    if let Some(member) = return_collector.member {
                        self.resolvers.insert(
                            function_symbol,
                            ResolverShape {
                                name: id.name.to_string(),
                                member,
                            },
                        );
                    }
                }
            }
        }
        walk::walk_function(self, it, flags);
    }
}

struct CallCollector<'c> {
    scoping: &'c Scoping,
    resolvers: &'c HashMap<SymbolId, ResolverShape>,
    proven_installers: &'c HashSet<SymbolId>,
    calls: Vec<StaticAliasInstallerCall>,
}

impl CallCollector<'_> {
    fn resolver_for(&self, argument: &Argument<'_>) -> Option<&ResolverShape> {
        let Argument::Identifier(id) = argument else {
            return None;
        };
        let reference = self.scoping.get_reference(id.reference_id.get()?);
        self.resolvers.get(&reference.symbol_id()?)
    }
}

impl<'a> Visit<'a> for CallCollector<'_> {
    fn visit_call_expression(&mut self, it: &oxc_ast::ast::CallExpression<'a>) {
        if !it.optional && it.arguments.len() == 4 && !it.arguments.iter().any(Argument::is_spread)
        {
            let Expression::Identifier(callee) = &it.callee else {
                walk::walk_call_expression(self, it);
                return;
            };
            let forwarding_installer_proven = callee
                .reference_id
                .get()
                .and_then(|reference_id| self.scoping.get_reference(reference_id).symbol_id())
                .is_some_and(|symbol| self.proven_installers.contains(&symbol));
            let Some(resolver) = self.resolver_for(&it.arguments[0]) else {
                walk::walk_call_expression(self, it);
                return;
            };
            let Argument::StringLiteral(source_property) = &it.arguments[1] else {
                walk::walk_call_expression(self, it);
                return;
            };
            let Argument::NumericLiteral(selector) = &it.arguments[2] else {
                walk::walk_call_expression(self, it);
                return;
            };
            let target_selector = match selector.value {
                0.0 => 0,
                1.0 => 1,
                _ => {
                    walk::walk_call_expression(self, it);
                    return;
                }
            };
            let Argument::StringLiteral(alias_property) = &it.arguments[3] else {
                walk::walk_call_expression(self, it);
                return;
            };
            let Some(source_property) = string_literal_value(source_property) else {
                walk::walk_call_expression(self, it);
                return;
            };
            let Some(alias_property) = string_literal_value(alias_property) else {
                walk::walk_call_expression(self, it);
                return;
            };
            self.calls.push(StaticAliasInstallerCall {
                start: it.span.start,
                end: it.span.end,
                installer: callee.name.to_string(),
                resolver: resolver.name.clone(),
                resolver_member: resolver.member.clone(),
                source_property,
                target_selector,
                alias_property,
                forwarding_installer_proven,
                // A proven installer contains a live-forwarding installation path.
                // This call may still early-return on pre-existing aliases or fail
                // defineProperty under arbitrary host state, so substitution semantics
                // are deliberately not claimed here.
                semantics_proven: false,
            });
        }
        walk::walk_call_expression(self, it);
    }
}

#[must_use]
pub fn static_alias_installer_calls(source: &str) -> Vec<StaticAliasInstallerCall> {
    for source_type in [SourceType::mjs(), SourceType::cjs()] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, source_type);
        if !parsed.is_clean() {
            continue;
        }
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        if !semantic_ret.diagnostics.is_empty() {
            continue;
        }
        let semantic = semantic_ret.semantic;
        let proven_installers =
            structurally_proven_forwarding_installers(&parsed.program, semantic.scoping());
        let mut resolver_collector = ResolverCollector {
            scoping: semantic.scoping(),
            resolvers: HashMap::new(),
        };
        resolver_collector.visit_program(&parsed.program);
        let mut call_collector = CallCollector {
            scoping: semantic.scoping(),
            resolvers: &resolver_collector.resolvers,
            proven_installers: &proven_installers,
            calls: Vec::new(),
        };
        call_collector.visit_program(&parsed.program);
        return call_collector.calls;
    }
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::static_alias_installer_calls;

    #[test]
    fn finds_only_proven_first_argument_resolvers() {
        let source = r#"
            function getArray(root) { return root.Array; }
            function boxed(root) {
                var box = [arguments];
                return box[0][0].Function;
            }
            function identity(root) {
                var box = [arguments];
                return box[0][0];
            }
            function unrelated(root) { return other.RegExp; }
            function tampered(root) {
                var box = [arguments];
                box = [other];
                return box[0][0].Map;
            }
            function argumentsMutated(root) {
                var box = [arguments];
                arguments[0] = other;
                return box[0][0].Set;
            }
            function conditionalBox(root) {
                if (flag) {
                    var box = [arguments];
                }
                return box[0][0].WeakMap;
            }
            function conditionalReturn(root) {
                if (flag) {
                    return root.WeakSet;
                }
            }
            function lateBox(root) {
                return box[0][0].Promise;
                var box = [arguments];
            }
            function install(a, b, c, d) {}
            install(getArray, "push", 1, "f2AA");
            install(boxed, "apply", 1, "o2AA");
            install(identity, "__residual", 0, "i2AA");
            install(unrelated, "test", 1, "bad");
            install(tampered, "add", 1, "bad2");
            install(argumentsMutated, "has", 1, "bad3");
            install(conditionalBox, "get", 1, "bad4");
            install(conditionalReturn, "add", 1, "bad5");
            install(lateBox, "then", 1, "bad6");
            install(getArray, dynamicName, 1, "nope");
        "#;
        let calls = static_alias_installer_calls(source);
        assert_eq!(calls.len(), 3);
        assert_eq!(calls[0].resolver_member.as_deref(), Some("Array"));
        assert_eq!(calls[0].source_property, "push");
        assert_eq!(calls[0].target_selector, 1);
        assert_eq!(calls[0].alias_property, "f2AA");
        assert_eq!(calls[1].resolver_member.as_deref(), Some("Function"));
        assert_eq!(calls[1].source_property, "apply");
        assert_eq!(calls[2].resolver_member, None);
        assert_eq!(calls[2].source_property, "__residual");
    }
}
