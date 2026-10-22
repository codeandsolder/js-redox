use super::{
    exact_zero, expression_is_symbol, expression_property_name, global_constructor,
    parameter_symbols, static_member_of_symbol, symbol_binding_is_stable, symbol_of,
    unparenthesized,
};
use crate::numeric::exact_u64;
use oxc_ast::ast::{
    Argument, AssignmentTarget, BindingPattern, CallExpression, Expression, Function, Statement,
    VariableDeclaration,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_syntax::symbol::SymbolId;
use serde::Serialize;
use std::collections::{HashMap, HashSet};

/// Proven syntax-level semantics for a simple WebAssembly import handler.
///
/// These proofs deliberately describe only the JavaScript handler body. They do not prove
/// that the handler belongs to a particular recovered module; cross-stage correlation owns that join.
#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum WasmImportHandlerSemantic {
    PropertyGetter {
        receiver_param: usize,
        property: &'static str,
        standard_builtin_semantics_required: bool,
    },
    Uint32ArrayConstructor {
        source_param: usize,
        element_width_bits: u8,
        global_object: String,
        standard_builtin_semantics_required: bool,
    },
    TypedArraySet {
        receiver_param: usize,
        source_param: usize,
        offset_param: usize,
        offset_to_u32_proven: bool,
        normal_return_set_call_proven: bool,
        standard_builtin_semantics_required: bool,
    },
    TableInitializerOnly {
        exports_binding: String,
        table_export: &'static str,
        exact_grow_deltas: Vec<u32>,
        standard_builtin_semantics_required: bool,
        standard_webassembly_builtin_semantics_required: bool,
    },
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize)]
pub struct WasmImportHandlerShape {
    pub import_module: Option<String>,
    pub import_name: String,
    /// Stable import-object binding owning this handler assignment, when the
    /// assignment itself proves one. Cross-stage correlation can use this to
    /// tie handler semantics to an exact instantiated import object.
    pub import_object: Option<String>,
    pub assignment_start: u32,
    pub assignment_end: u32,
    #[serde(flatten)]
    pub semantic: WasmImportHandlerSemantic,
}

fn stable_parameters(function: &Function<'_>, scoping: &Scoping) -> Option<Vec<SymbolId>> {
    if function.r#async || function.generator {
        return None;
    }
    let params = parameter_symbols(function)?;
    params
        .iter()
        .all(|symbol| symbol_binding_is_stable(scoping, *symbol))
        .then_some(params)
}

fn single_return_expression<'a>(function: &'a Function<'a>) -> Option<&'a Expression<'a>> {
    let body = function.body.as_ref()?;
    let [Statement::ReturnStatement(statement)] = body.statements.as_slice() else {
        return None;
    };
    statement.argument.as_ref()
}

fn single_expression<'a>(function: &'a Function<'a>) -> Option<&'a Expression<'a>> {
    let body = function.body.as_ref()?;
    let [Statement::ExpressionStatement(statement)] = body.statements.as_slice() else {
        return None;
    };
    Some(&statement.expression)
}

fn property_getter(
    function: &Function<'_>,
    scoping: &Scoping,
) -> Option<WasmImportHandlerSemantic> {
    let params = stable_parameters(function, scoping)?;
    let [receiver] = params.as_slice() else {
        return None;
    };
    let expression = single_return_expression(function)?;
    for property in ["buffer", "length"] {
        if static_member_of_symbol(scoping, expression, *receiver, property) {
            return Some(WasmImportHandlerSemantic::PropertyGetter {
                receiver_param: 0,
                property,
                standard_builtin_semantics_required: true,
            });
        }
    }
    None
}

fn uint32_array_constructor(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> Option<WasmImportHandlerSemantic> {
    let params = stable_parameters(function, scoping)?;
    let [source] = params.as_slice() else {
        return None;
    };
    let Expression::NewExpression(new_expression) =
        unparenthesized(single_return_expression(function)?)
    else {
        return None;
    };
    let global = global_constructor(
        scoping,
        global_aliases,
        &new_expression.callee,
        "Uint32Array",
    )?;
    let [argument] = new_expression.arguments.as_slice() else {
        return None;
    };
    let source_expression = argument.as_expression()?;
    expression_is_symbol(scoping, source_expression, *source).then_some(
        WasmImportHandlerSemantic::Uint32ArrayConstructor {
            source_param: 0,
            element_width_bits: 32,
            global_object: global,
            standard_builtin_semantics_required: true,
        },
    )
}

fn u32_coerced_symbol(scoping: &Scoping, argument: &Argument<'_>, symbol: SymbolId) -> bool {
    let Some(expression) = argument.as_expression() else {
        return false;
    };
    let Expression::BinaryExpression(binary) = unparenthesized(expression) else {
        return false;
    };
    binary.operator.as_str() == ">>>"
        && expression_is_symbol(scoping, &binary.left, symbol)
        && exact_zero(&binary.right)
}

fn typed_array_set(
    function: &Function<'_>,
    scoping: &Scoping,
) -> Option<WasmImportHandlerSemantic> {
    let params = stable_parameters(function, scoping)?;
    let [receiver, source, offset] = params.as_slice() else {
        return None;
    };
    let Expression::CallExpression(call) = unparenthesized(single_expression(function)?) else {
        return None;
    };
    if call.optional || call.arguments.len() != 2 || call.arguments.iter().any(Argument::is_spread)
    {
        return None;
    }
    if expression_property_name(&call.callee) != Some("set") {
        return None;
    }
    let call_receiver = match unparenthesized(&call.callee) {
        Expression::StaticMemberExpression(member) if !member.optional => &member.object,
        Expression::ComputedMemberExpression(member) if !member.optional => &member.object,
        _ => return None,
    };
    let source_argument = call.arguments[0].as_expression()?;
    if !expression_is_symbol(scoping, call_receiver, *receiver)
        || !expression_is_symbol(scoping, source_argument, *source)
        || !u32_coerced_symbol(scoping, &call.arguments[1], *offset)
    {
        return None;
    }
    Some(WasmImportHandlerSemantic::TypedArraySet {
        receiver_param: 0,
        source_param: 1,
        offset_param: 2,
        offset_to_u32_proven: true,
        normal_return_set_call_proven: true,
        standard_builtin_semantics_required: true,
    })
}

fn static_member_parts<'a>(
    expression: &'a Expression<'a>,
) -> Option<(&'a Expression<'a>, &'a str)> {
    match unparenthesized(expression) {
        Expression::StaticMemberExpression(member) if !member.optional => {
            Some((&member.object, member.property.name.as_str()))
        }
        Expression::ComputedMemberExpression(member) if !member.optional => {
            let Expression::StringLiteral(property) = unparenthesized(&member.expression) else {
                return None;
            };
            Some((&member.object, property.value.as_str()?))
        }
        _ => None,
    }
}

pub(super) fn standard_numeric_builtin_call(
    call: &CallExpression<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> bool {
    if call.optional || call.arguments.iter().any(Argument::is_spread) {
        return false;
    }
    let Some((object, property)) = static_member_parts(&call.callee) else {
        return false;
    };
    if symbol_of(scoping, object).is_some_and(|symbol| global_aliases.contains_key(&symbol)) {
        return matches!((property, call.arguments.len()), ("Number" | "parseInt", 1));
    }
    let Some((global, namespace)) = static_member_parts(object) else {
        return false;
    };
    namespace == "Math"
        && symbol_of(scoping, global).is_some_and(|symbol| global_aliases.contains_key(&symbol))
        && matches!(property, "floor" | "ceil" | "trunc")
        && call.arguments.len() == 1
}

pub(super) fn proof_primitive_expression(
    expression: &Expression<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
    primitive_locals: &HashSet<SymbolId>,
) -> bool {
    match unparenthesized(expression) {
        Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::StringLiteral(_) => true,
        Expression::Identifier(identifier) => identifier
            .reference_id
            .get()
            .and_then(|reference_id| scoping.get_reference(reference_id).symbol_id())
            .is_some_and(|symbol| primitive_locals.contains(&symbol)),
        Expression::UnaryExpression(unary) => {
            unary.operator.as_str() != "delete"
                && proof_primitive_expression(
                    &unary.argument,
                    scoping,
                    global_aliases,
                    primitive_locals,
                )
        }
        Expression::BinaryExpression(binary) => {
            proof_primitive_expression(&binary.left, scoping, global_aliases, primitive_locals)
                && proof_primitive_expression(
                    &binary.right,
                    scoping,
                    global_aliases,
                    primitive_locals,
                )
        }
        Expression::CallExpression(call)
            if standard_numeric_builtin_call(call, scoping, global_aliases) =>
        {
            call.arguments.iter().all(|argument| {
                argument.as_expression().is_some_and(|argument| {
                    proof_primitive_expression(argument, scoping, global_aliases, primitive_locals)
                })
            })
        }
        _ => false,
    }
}

fn table_initializer_receiver_call<'a>(
    expression: &'a Expression<'a>,
    scoping: &Scoping,
    receiver: SymbolId,
    method: &str,
    argument_count: usize,
) -> Option<&'a CallExpression<'a>> {
    let Expression::CallExpression(call) = unparenthesized(expression) else {
        return None;
    };
    if call.optional
        || call.arguments.len() != argument_count
        || call.arguments.iter().any(Argument::is_spread)
    {
        return None;
    }
    let (object, property) = static_member_parts(&call.callee)?;
    (property == method && symbol_of(scoping, object) == Some(receiver)).then_some(call)
}

fn table_initializer_only(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> Option<WasmImportHandlerSemantic> {
    if function.r#async || function.generator || !function.params.items.is_empty() {
        return None;
    }
    let body = function.body.as_ref()?;

    struct LocalCollector {
        all: HashSet<SymbolId>,
        uninitialized: HashSet<SymbolId>,
        invalid: bool,
    }
    impl<'a> Visit<'a> for LocalCollector {
        fn visit_variable_declaration(&mut self, declaration: &VariableDeclaration<'a>) {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    self.invalid = true;
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    self.invalid = true;
                    continue;
                };
                self.all.insert(symbol);
                if declarator.init.is_none() {
                    self.uninitialized.insert(symbol);
                }
            }
            walk::walk_variable_declaration(self, declaration);
        }

        fn visit_function(
            &mut self,
            _function: &Function<'a>,
            _flags: oxc_syntax::scope::ScopeFlags,
        ) {
        }
    }
    let mut locals = LocalCollector {
        all: HashSet::new(),
        uninitialized: HashSet::new(),
        invalid: false,
    };
    for statement in &body.statements {
        locals.visit_statement(statement);
    }
    if locals.invalid {
        return None;
    }

    struct BindingCollector<'c, 'l> {
        scoping: &'c Scoping,
        locals: &'l HashSet<SymbolId>,
        candidates: Vec<(SymbolId, SymbolId)>,
    }
    impl<'a> Visit<'a> for BindingCollector<'_, '_> {
        fn visit_function(
            &mut self,
            _function: &Function<'a>,
            _flags: oxc_syntax::scope::ScopeFlags,
        ) {
        }

        fn visit_assignment_expression(
            &mut self,
            assignment: &oxc_ast::ast::AssignmentExpression<'a>,
        ) {
            if assignment.operator.as_str() == "="
                && expression_property_name(&assignment.right) == Some("__wbindgen_export_0")
            {
                if let AssignmentTarget::AssignmentTargetIdentifier(left) = &assignment.left {
                    if let Some((object, _)) = static_member_parts(&assignment.right) {
                        if let (Some(receiver), Some(exports)) = (
                            left.reference_id
                                .get()
                                .and_then(|id| self.scoping.get_reference(id).symbol_id()),
                            symbol_of(self.scoping, object),
                        ) {
                            if self.locals.contains(&receiver) {
                                self.candidates.push((receiver, exports));
                            }
                        }
                    }
                }
            }
            walk::walk_assignment_expression(self, assignment);
        }
    }
    let mut bindings = BindingCollector {
        scoping,
        locals: &locals.all,
        candidates: Vec::new(),
    };
    for statement in &body.statements {
        bindings.visit_statement(statement);
    }
    let [(receiver, exports)] = bindings.candidates.as_slice() else {
        return None;
    };
    if !locals.uninitialized.contains(receiver) {
        return None;
    }

    struct Verifier<'c, 'g, 'l> {
        scoping: &'c Scoping,
        global_aliases: &'g HashMap<SymbolId, String>,
        locals: &'l HashSet<SymbolId>,
        receiver: SymbolId,
        exports: SymbolId,
        primitive_locals: HashSet<SymbolId>,
        receiver_assigned: bool,
        saw_table_operation: bool,
        exact_grow_deltas: Vec<u32>,
    }
    impl Verifier<'_, '_, '_> {
        fn verify_statements(&mut self, statements: &[Statement<'_>]) -> bool {
            statements
                .iter()
                .all(|statement| self.verify_statement(statement))
        }

        fn verify_statement(&mut self, statement: &Statement<'_>) -> bool {
            match statement {
                Statement::BlockStatement(block) => self.verify_statements(&block.body),
                Statement::EmptyStatement(_) => true,
                Statement::VariableDeclaration(declaration) => {
                    for declarator in &declaration.declarations {
                        let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                            return false;
                        };
                        let Some(symbol) = identifier.symbol_id.get() else {
                            return false;
                        };
                        if !self.locals.contains(&symbol) {
                            return false;
                        }
                        if let Some(initializer) = &declarator.init {
                            if !proof_primitive_expression(
                                initializer,
                                self.scoping,
                                self.global_aliases,
                                &self.primitive_locals,
                            ) {
                                return false;
                            }
                            self.primitive_locals.insert(symbol);
                        }
                    }
                    true
                }
                Statement::ExpressionStatement(statement) => {
                    let expression = unparenthesized(&statement.expression);
                    if let Expression::AssignmentExpression(assignment) = expression {
                        if assignment.operator.as_str() != "=" {
                            return false;
                        }
                        let AssignmentTarget::AssignmentTargetIdentifier(left) = &assignment.left
                        else {
                            return false;
                        };
                        let Some(target) = left.reference_id.get().and_then(|reference_id| {
                            self.scoping.get_reference(reference_id).symbol_id()
                        }) else {
                            return false;
                        };
                        if !self.locals.contains(&target) {
                            return false;
                        }

                        if target == self.receiver {
                            if self.receiver_assigned {
                                return false;
                            }
                            let Some((object, property)) = static_member_parts(&assignment.right)
                            else {
                                return false;
                            };
                            if property != "__wbindgen_export_0"
                                || symbol_of(self.scoping, object) != Some(self.exports)
                            {
                                return false;
                            }
                            self.receiver_assigned = true;
                            return true;
                        }

                        if let Some(call) = table_initializer_receiver_call(
                            &assignment.right,
                            self.scoping,
                            self.receiver,
                            "grow",
                            1,
                        ) {
                            if !self.receiver_assigned {
                                return false;
                            }
                            let Some(argument) = call.arguments[0].as_expression() else {
                                return false;
                            };
                            if !proof_primitive_expression(
                                argument,
                                self.scoping,
                                self.global_aliases,
                                &self.primitive_locals,
                            ) {
                                return false;
                            }
                            let Expression::NumericLiteral(delta) = unparenthesized(argument)
                            else {
                                return false;
                            };
                            let Some(delta) =
                                exact_u64(delta.value).and_then(|value| u32::try_from(value).ok())
                            else {
                                return false;
                            };
                            self.exact_grow_deltas.push(delta);
                            self.primitive_locals.insert(target);
                            self.saw_table_operation = true;
                            return true;
                        }

                        if proof_primitive_expression(
                            &assignment.right,
                            self.scoping,
                            self.global_aliases,
                            &self.primitive_locals,
                        ) {
                            self.primitive_locals.insert(target);
                            return true;
                        }
                        false
                    } else if let Some(call) = table_initializer_receiver_call(
                        expression,
                        self.scoping,
                        self.receiver,
                        "set",
                        2,
                    ) {
                        if !self.receiver_assigned {
                            return false;
                        }
                        let [index, value] = call.arguments.as_slice() else {
                            return false;
                        };
                        let (Some(index), Some(value)) =
                            (index.as_expression(), value.as_expression())
                        else {
                            return false;
                        };
                        if !proof_primitive_expression(
                            index,
                            self.scoping,
                            self.global_aliases,
                            &self.primitive_locals,
                        ) || !proof_primitive_expression(
                            value,
                            self.scoping,
                            self.global_aliases,
                            &self.primitive_locals,
                        ) {
                            return false;
                        }
                        self.saw_table_operation = true;
                        true
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
    }

    let mut verifier = Verifier {
        scoping,
        global_aliases,
        locals: &locals.all,
        receiver: *receiver,
        exports: *exports,
        primitive_locals: HashSet::new(),
        receiver_assigned: false,
        saw_table_operation: false,
        exact_grow_deltas: Vec::new(),
    };
    if !verifier.verify_statements(&body.statements)
        || !verifier.receiver_assigned
        || !verifier.saw_table_operation
    {
        return None;
    }

    let exports_name = scoping.symbol_name(*exports);
    if scoping
        .symbol_ids()
        .filter(|symbol| scoping.symbol_name(*symbol) == exports_name)
        .count()
        != 1
    {
        return None;
    }

    Some(WasmImportHandlerSemantic::TableInitializerOnly {
        exports_binding: exports_name.to_string(),
        table_export: "__wbindgen_export_0",
        exact_grow_deltas: verifier.exact_grow_deltas,
        standard_builtin_semantics_required: true,
        standard_webassembly_builtin_semantics_required: true,
    })
}

pub(super) fn analyze_import_handler(
    function: &Function<'_>,
    scoping: &Scoping,
    global_aliases: &HashMap<SymbolId, String>,
) -> Option<WasmImportHandlerSemantic> {
    uint32_array_constructor(function, scoping, global_aliases)
        .or_else(|| typed_array_set(function, scoping))
        .or_else(|| property_getter(function, scoping))
        .or_else(|| table_initializer_only(function, scoping, global_aliases))
}
