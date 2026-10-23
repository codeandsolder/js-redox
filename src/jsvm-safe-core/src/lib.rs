mod control_flow;
mod decoder;
mod decoder_encoding;
mod numeric;
mod proxy;
mod pure_function;
mod rewrite;
mod selector;
mod value_eval;

use control_flow::{
    collect_dispatch_bindings, collect_reference_spans, detect_reference_identity_tables,
    reference_identity, ReferenceIdentityTable,
};
use decoder::{analyze_decoders, js_parse_int, Decoder};
pub use numeric::{exact_i64, exact_u32, exact_u64, exact_usize};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrayExpressionElement, BindingPattern, CallExpression, ComputedMemberExpression,
    Expression, ExpressionStatement, IfStatement, LogicalExpression, Statement,
    StaticMemberExpression, UnaryExpression, VariableDeclarationKind, WithStatement,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{ReferenceId, Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::{
    identifier,
    scope::{ScopeFlags, ScopeId},
    symbol::SymbolId,
};
use proxy::{
    collect_proxy_objects, proxy_literal_kind, static_proxy_member, ProxyObject, ProxyProperty,
};
use pure_function::{collect_pure_functions, PureFunction};
use rewrite::{apply, Counts, Replacement};
use rolldown_redox::ecmascript::parse_program;
use selector::{collect_selector_dispatchers, SelectorDispatcher};
use std::collections::{BTreeMap, HashMap, HashSet};
use value_eval::{
    eval, eval_binary, eval_logical, eval_unary, eval_with_resolver, js_to_uint32, known_bool,
    Value,
};
pub use value_eval::{string_literal_value, template_element_value};

#[derive(Debug, Clone)]
pub struct ArithmeticStateProof {
    pub iteration: usize,
    pub input_start: usize,
    pub input_end: usize,
    pub state_var: String,
    pub state_path: Vec<String>,
    pub termination: String,
    pub register_reads_rewritten: usize,
    pub branch_test: Option<String>,
    pub branch_paths: Vec<Vec<String>>,
    pub branch_terminations: Vec<String>,
}

fn fragment(source: &str, span: Span) -> &str {
    source
        .get(span.start as usize..(span.end as usize).min(source.len()))
        .unwrap_or_default()
}

fn valid_property(name: &str) -> bool {
    identifier::is_identifier_name(name)
}

fn symbol_of(scoping: &Scoping, expr: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(id) = expr else {
        return None;
    };
    scoping.get_reference(id.reference_id.get()?).symbol_id()
}

fn direct_identifier_name<'a>(expr: &'a Expression<'a>) -> Option<&'a str> {
    match expr {
        Expression::Identifier(id) => Some(id.name.as_str()),
        _ => None,
    }
}

#[derive(Debug, Clone)]
struct ConstBinding {
    value: Value,
    available_after: u32,
}

fn eval_with_constants(
    expr: &Expression<'_>,
    scoping: &Scoping,
    constants: &HashMap<SymbolId, ConstBinding>,
) -> Option<Value> {
    eval_with_resolver(expr, &|id| {
        let reference_id = id.reference_id.get()?;
        let reference = scoping.get_reference(reference_id);
        if !reference.is_read()
            || reference.is_write()
            || reference.flags().is_member_write_target()
        {
            return None;
        }
        let binding = constants.get(&reference.symbol_id()?)?;
        (id.span.start >= binding.available_after).then(|| binding.value.clone())
    })
}

struct ConstValueCollector<'s, 'c> {
    scoping: &'c Scoping,
    constants: &'s mut HashMap<SymbolId, ConstBinding>,
    changed: bool,
}

impl<'a> Visit<'a> for ConstValueCollector<'_, '_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        if it.kind == VariableDeclarationKind::Const {
            for d in &it.declarations {
                let BindingPattern::BindingIdentifier(id) = &d.id else {
                    continue;
                };
                let Some(symbol) = id.symbol_id.get() else {
                    continue;
                };
                if self.constants.contains_key(&symbol) {
                    continue;
                }
                let Some(init) = &d.init else {
                    continue;
                };
                let Some(value) = eval_with_constants(init, self.scoping, self.constants) else {
                    continue;
                };
                self.constants.insert(
                    symbol,
                    ConstBinding {
                        value,
                        available_after: d.span.end,
                    },
                );
                self.changed = true;
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_const_values(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, ConstBinding> {
    let mut constants = HashMap::new();
    loop {
        let changed = {
            let mut collector = ConstValueCollector {
                scoping,
                constants: &mut constants,
                changed: false,
            };
            collector.visit_program(program);
            collector.changed
        };
        if !changed {
            break;
        }
    }
    constants
}

/// Immutable primitive bindings proven from `const` declarations.
///
/// Bindings are keyed by Oxc semantic identity, become available only after
/// their declaration, and use the same deliberately narrow pure-expression
/// evaluator as safe deobfuscation.
#[derive(Debug)]
pub struct ProvenConstantEnvironment {
    bindings: HashMap<SymbolId, ConstBinding>,
}

impl ProvenConstantEnvironment {
    #[must_use]
    pub fn collect(program: &oxc_ast::ast::Program<'_>, scoping: &Scoping) -> Self {
        Self {
            bindings: collect_const_values(program, scoping),
        }
    }

    #[must_use]
    pub fn exact_string(&self, expr: &Expression<'_>, scoping: &Scoping) -> Option<String> {
        match eval_with_constants(expr, scoping, &self.bindings)? {
            Value::String(value) => Some(value),
            _ => None,
        }
    }
}

fn array_element(el: &ArrayExpressionElement<'_>) -> Option<Value> {
    match el {
        ArrayExpressionElement::StringLiteral(v) => string_literal_value(v).map(Value::String),
        ArrayExpressionElement::NumericLiteral(v) => Some(Value::Number(v.value)),
        ArrayExpressionElement::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        ArrayExpressionElement::NullLiteral(_) => Some(Value::Null),
        ArrayExpressionElement::UnaryExpression(v) => eval_unary(v),
        _ => None,
    }
}

fn top_level_arrays(program: &oxc_ast::ast::Program<'_>) -> HashMap<SymbolId, Vec<Value>> {
    let mut out = HashMap::new();
    for stmt in &program.body {
        let Statement::VariableDeclaration(decl) = stmt else {
            continue;
        };
        if decl.kind != VariableDeclarationKind::Const {
            continue;
        }
        for d in &decl.declarations {
            let BindingPattern::BindingIdentifier(id) = &d.id else {
                continue;
            };
            let Some(symbol) = id.symbol_id.get() else {
                continue;
            };
            let Some(Expression::ArrayExpression(arr)) = &d.init else {
                continue;
            };
            let Some(values) = arr
                .elements
                .iter()
                .map(array_element)
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if !values.is_empty() {
                out.insert(symbol, values);
            }
        }
    }
    out
}

#[derive(Default)]
struct StableVarNumberCollector {
    candidates: HashMap<SymbolId, i64>,
}

impl<'a> Visit<'a> for StableVarNumberCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        if it.kind == VariableDeclarationKind::Var {
            for declaration in &it.declarations {
                let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                    continue;
                };
                let Some(symbol) = id.symbol_id.get() else {
                    continue;
                };
                let Some(init) = &declaration.init else {
                    continue;
                };
                let Some(Value::Number(number)) = eval(init) else {
                    continue;
                };
                let Some(number) = exact_i64(number) else {
                    continue;
                };
                self.candidates.insert(symbol, number);
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_stable_var_numbers(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, i64> {
    let mut collector = StableVarNumberCollector::default();
    collector.visit_program(program);
    collector.candidates.retain(|symbol, _| {
        scoping
            .get_resolved_reference_ids(*symbol)
            .iter()
            .all(|reference_id| {
                let reference = scoping.get_reference(*reference_id);
                !reference.is_write() && !reference.flags().is_member_write_target()
            })
    });
    collector.candidates
}

#[derive(Debug, Clone, Copy)]
struct VarNumberInitializer {
    value: f64,
    available_after: u32,
}

#[derive(Default)]
struct VarNumberInitializerCollector {
    candidates: HashMap<SymbolId, VarNumberInitializer>,
    seen: HashSet<SymbolId>,
}

impl<'a> Visit<'a> for VarNumberInitializerCollector {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        if it.kind == VariableDeclarationKind::Var {
            for declaration in &it.declarations {
                let BindingPattern::BindingIdentifier(id) = &declaration.id else {
                    continue;
                };
                let Some(symbol) = id.symbol_id.get() else {
                    continue;
                };
                if !self.seen.insert(symbol) {
                    self.candidates.remove(&symbol);
                    continue;
                }
                let Some(init) = &declaration.init else {
                    continue;
                };
                let Some(Value::Number(number)) = eval(init) else {
                    continue;
                };
                if !number.is_finite() || number.fract() != 0.0 {
                    continue;
                }
                self.candidates.insert(
                    symbol,
                    VarNumberInitializer {
                        value: number,
                        available_after: declaration.span.end,
                    },
                );
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_var_number_initializers(
    program: &oxc_ast::ast::Program<'_>,
) -> HashMap<SymbolId, VarNumberInitializer> {
    let mut collector = VarNumberInitializerCollector::default();
    collector.visit_program(program);
    collector.candidates
}

fn expression_integer(expr: &Expression<'_>) -> Option<i64> {
    let Value::Number(number) = eval(expr)? else {
        return None;
    };
    exact_i64(number)
}

#[derive(Default)]
struct ShorthandCollector {
    spans: HashSet<(u32, u32)>,
}

impl<'a> Visit<'a> for ShorthandCollector {
    fn visit_object_property(&mut self, it: &oxc_ast::ast::ObjectProperty<'a>) {
        if it.shorthand {
            let span = it.value.span();
            self.spans.insert((span.start, span.end));
        }
        walk::walk_object_property(self, it);
    }
}

fn collect_shorthand_spans(program: &oxc_ast::ast::Program<'_>) -> HashSet<(u32, u32)> {
    let mut collector = ShorthandCollector::default();
    collector.visit_program(program);
    collector.spans
}

struct FromCharCodeAliasCollector<'c> {
    scoping: &'c Scoping,
    candidates: HashMap<SymbolId, u32>,
}

impl<'a> Visit<'a> for FromCharCodeAliasCollector<'_> {
    fn visit_variable_declaration(&mut self, it: &oxc_ast::ast::VariableDeclaration<'a>) {
        for declaration in &it.declarations {
            let BindingPattern::BindingIdentifier(binding) = &declaration.id else {
                continue;
            };
            let Some(symbol) = binding.symbol_id.get() else {
                continue;
            };
            let Some(Expression::StaticMemberExpression(member)) = &declaration.init else {
                continue;
            };
            if member.optional || member.property.name.as_str() != "fromCharCode" {
                continue;
            }
            let Expression::Identifier(object) = &member.object else {
                continue;
            };
            // Match the ordinary global String builtin only. A locally shadowed
            // `String` binding is not evidence for builtin fromCharCode semantics.
            if object.name.as_str() == "String" && symbol_of(self.scoping, &member.object).is_none()
            {
                self.candidates.insert(symbol, declaration.span().end);
            }
        }
        walk::walk_variable_declaration(self, it);
    }
}

fn collect_from_char_code_aliases(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashMap<SymbolId, u32> {
    let mut collector = FromCharCodeAliasCollector {
        scoping,
        candidates: HashMap::new(),
    };
    collector.visit_program(program);
    collector.candidates.retain(|symbol, _initialized_after| {
        scoping
            .get_resolved_reference_ids(*symbol)
            .iter()
            .all(|reference_id| {
                let reference = scoping.get_reference(*reference_id);
                !reference.is_write() && !reference.flags().is_member_write_target()
            })
    });
    collector.candidates
}

fn direct_global_object_name<'a>(
    scoping: &Scoping,
    expression: &'a Expression<'a>,
) -> Option<&'a str> {
    let Expression::Identifier(identifier) = expression else {
        return None;
    };
    if !matches!(identifier.name.as_str(), "window" | "globalThis" | "self") {
        return None;
    }
    let reference = scoping.get_reference(identifier.reference_id.get()?);
    reference
        .symbol_id()
        .is_none()
        .then_some(identifier.name.as_str())
}

fn collect_global_object_aliases(
    program: &oxc_ast::ast::Program<'_>,
    scoping: &Scoping,
) -> HashSet<SymbolId> {
    struct AliasCollector<'c> {
        scoping: &'c Scoping,
        aliases: HashSet<SymbolId>,
    }
    impl<'a> Visit<'a> for AliasCollector<'_> {
        fn visit_variable_declaration(
            &mut self,
            declaration: &oxc_ast::ast::VariableDeclaration<'a>,
        ) {
            for declarator in &declaration.declarations {
                let BindingPattern::BindingIdentifier(identifier) = &declarator.id else {
                    continue;
                };
                let Some(symbol) = identifier.symbol_id.get() else {
                    continue;
                };
                let Some(initializer) = &declarator.init else {
                    continue;
                };
                if direct_global_object_name(self.scoping, initializer).is_none() {
                    continue;
                }
                let stable = self
                    .scoping
                    .get_resolved_reference_ids(symbol)
                    .iter()
                    .all(|reference_id| !self.scoping.get_reference(*reference_id).is_write());
                if stable {
                    self.aliases.insert(symbol);
                }
            }
            walk::walk_variable_declaration(self, declaration);
        }
    }
    let mut collector = AliasCollector {
        scoping,
        aliases: HashSet::new(),
    };
    collector.visit_program(program);
    collector.aliases
}

#[derive(Clone, Copy)]
enum CallRewriteTraversal {
    Stop,
    WalkChildren,
}

struct Collector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    arrays: &'c HashMap<SymbolId, Vec<Value>>,
    decoders: &'c HashMap<SymbolId, Decoder>,
    constants: &'c HashMap<SymbolId, ConstBinding>,
    shorthand_spans: &'c HashSet<(u32, u32)>,
    proxies: &'c HashMap<SymbolId, ProxyObject>,
    pure_functions: &'c HashMap<SymbolId, PureFunction>,
    from_char_code_aliases: &'c HashMap<SymbolId, u32>,
    global_object_aliases: &'c HashSet<SymbolId>,
    standard_numeric_builtins: bool,
    reference_identity_tables: &'c HashMap<SymbolId, ReferenceIdentityTable>,
    selector_dispatchers: &'c HashMap<SymbolId, SelectorDispatcher>,
    dispatch_orders: &'c HashMap<SymbolId, Vec<String>>,
    zero_counters: &'c HashSet<SymbolId>,
    var_number_initializers: &'c HashMap<SymbolId, VarNumberInitializer>,
    reference_spans: &'c HashMap<ReferenceId, Span>,
    protected_spans: &'c [(usize, usize)],
    replacements: Vec<Replacement>,
}

impl Collector<'_, '_> {
    fn is_protected(&self, start: usize, end: usize) -> bool {
        self.protected_spans
            .iter()
            .any(|(protected_start, protected_end)| {
                start < *protected_end && *protected_start < end
            })
    }

    fn push(&mut self, span: Span, text: String, kind: &'static str) {
        let start = span.start as usize;
        let end = span.end as usize;
        if start >= end || end > self.source.len() || self.is_protected(start, end) {
            return;
        }
        if self.source.get(start..end) == Some(text.as_str()) {
            return;
        }
        self.replacements.push(Replacement {
            start,
            end,
            text,
            kind,
            arithmetic_state_proof: None,
        });
    }

    fn push_arithmetic(&mut self, span: Span, text: String, mut proof: ArithmeticStateProof) {
        let start = span.start as usize;
        let end = span.end as usize;
        if start >= end || end > self.source.len() || self.is_protected(start, end) {
            return;
        }
        if self.source.get(start..end) == Some(text.as_str()) {
            return;
        }
        proof.input_start = start;
        proof.input_end = end;
        self.replacements.push(Replacement {
            start,
            end,
            text,
            kind: "arithmetic_state_unflatten",
            arithmetic_state_proof: Some(proof),
        });
    }
    fn is_plain_call(call: &CallExpression<'_>) -> bool {
        !call.optional && !call.arguments.iter().any(Argument::is_spread)
    }

    fn try_selector_dispatch_rewrite(
        &mut self,
        call: &CallExpression<'_>,
    ) -> Option<CallRewriteTraversal> {
        if !Self::is_plain_call(call) {
            return None;
        }
        let symbol = symbol_of(self.scoping, &call.callee)?;
        let dispatcher = self.selector_dispatchers.get(&symbol)?;
        let selector = call.arguments.first().and_then(argument_integer)?;
        let return_span = *dispatcher.returns.get(&selector)?;
        let used_param_count = dispatcher
            .param_symbols
            .iter()
            .enumerate()
            .filter_map(|(index, symbol)| {
                self.scoping
                    .get_resolved_reference_ids(*symbol)
                    .iter()
                    .filter_map(|reference_id| self.reference_spans.get(reference_id))
                    .any(|span| return_span.start <= span.start && span.end <= return_span.end)
                    .then_some(index + 1)
            })
            .max()
            .unwrap_or(0);
        let params = dispatcher.params[..used_param_count].join(", ");
        let args = call
            .arguments
            .iter()
            .map(|argument| fragment(self.source, argument.span()))
            .collect::<Vec<_>>()
            .join(", ");
        let returned = fragment(self.source, return_span);
        self.push(
            call.span,
            format!("(function({params}){{return ({returned});}})({args})"),
            "selector_dispatch_specialize",
        );
        Some(CallRewriteTraversal::Stop)
    }

    fn try_proxy_call_rewrite(
        &mut self,
        call: &CallExpression<'_>,
    ) -> Option<CallRewriteTraversal> {
        if !Self::is_plain_call(call) {
            return None;
        }
        let (symbol, key) = static_proxy_member(&call.callee, self.scoping)?;
        let property = self.proxies.get(&symbol)?.get(&key)?;
        let rewrite = match property {
            ProxyProperty::Call { arity } if call.arguments.len() == arity + 1 => {
                let callee = fragment(self.source, call.arguments[0].span());
                let args = call.arguments[1..]
                    .iter()
                    .map(|argument| fragment(self.source, argument.span()))
                    .collect::<Vec<_>>()
                    .join(", ");
                Some((format!("((0, ({callee})))({args})"), "proxy_call"))
            }
            ProxyProperty::StaticMember { property } if call.arguments.len() == 1 => {
                let object = fragment(self.source, call.arguments[0].span());
                Some((format!("(({object}).{property})"), "proxy_static_member"))
            }
            ProxyProperty::ComputedMember if call.arguments.len() == 2 => {
                let object = fragment(self.source, call.arguments[0].span());
                let property = fragment(self.source, call.arguments[1].span());
                Some((format!("(({object})[{property}])"), "proxy_computed_member"))
            }
            ProxyProperty::Unary { operator } if call.arguments.len() == 1 => {
                let argument = fragment(self.source, call.arguments[0].span());
                let text = if operator == "void" {
                    format!("(void ({argument}))")
                } else {
                    format!("({operator}({argument}))")
                };
                Some((text, "proxy_unary"))
            }
            ProxyProperty::Binary { operator } if call.arguments.len() == 2 => {
                let left = fragment(self.source, call.arguments[0].span());
                let right = fragment(self.source, call.arguments[1].span());
                Some((format!("(({left}) {operator} ({right}))"), "proxy_binary"))
            }
            _ => None,
        }?;
        self.push(call.span, rewrite.0, rewrite.1);
        Some(CallRewriteTraversal::Stop)
    }

    fn same_function_or_descendant_block_scope(
        scoping: &Scoping,
        mut scope: ScopeId,
        binding_scope: ScopeId,
    ) -> bool {
        if scope == binding_scope {
            return true;
        }
        loop {
            if scoping.scope_flags(scope).is_function() {
                return false;
            }
            let Some(parent) = scoping.scope_parent_id(scope) else {
                return false;
            };
            if parent == binding_scope {
                return true;
            }
            scope = parent;
        }
    }

    fn try_from_char_code_alias_rewrite(
        &mut self,
        call: &CallExpression<'_>,
    ) -> Option<CallRewriteTraversal> {
        if !Self::is_plain_call(call) || call.arguments.is_empty() {
            return None;
        }
        let Expression::Identifier(callee) = &call.callee else {
            return None;
        };
        let reference_id = callee.reference_id.get()?;
        let reference = self.scoping.get_reference(reference_id);
        let symbol = reference.symbol_id()?;
        let initialized_after = self.from_char_code_aliases.get(&symbol)?;
        if call.span.start < *initialized_after
            || !Self::same_function_or_descendant_block_scope(
                self.scoping,
                reference.scope_id(),
                self.scoping.symbol_scope_id(symbol),
            )
        {
            return None;
        }
        let units = call
            .arguments
            .iter()
            .map(|argument| {
                let number = eval_static_argument(argument)?.number()?;
                Some((js_to_uint32(number) & 0xffff) as u16)
            })
            .collect::<Option<Vec<_>>>()?;
        // Rust strings cannot represent an unpaired UTF-16 surrogate. Fail
        // closed in that uncommon case; paired surrogates round-trip exactly.
        let value = String::from_utf16(&units).ok()?;
        let text = Value::String(value).render()?;
        self.push(call.span, text, "from_char_code_alias");
        Some(CallRewriteTraversal::Stop)
    }

    fn try_pure_function_rewrite(
        &mut self,
        call: &CallExpression<'_>,
    ) -> Option<CallRewriteTraversal> {
        if !Self::is_plain_call(call) {
            return None;
        }
        let symbol = symbol_of(self.scoping, &call.callee)?;
        let function = self.pure_functions.get(&symbol)?;
        let values = call
            .arguments
            .iter()
            .map(eval_static_argument)
            .collect::<Option<Vec<_>>>()?;
        let text = function
            .evaluate(&values)
            .and_then(|value| value.render())?;
        self.push(call.span, text, "pure_function_eval");
        Some(CallRewriteTraversal::WalkChildren)
    }

    fn try_decoder_rewrite(&mut self, call: &CallExpression<'_>) -> Option<CallRewriteTraversal> {
        let symbol = symbol_of(self.scoping, &call.callee)?;
        let decoder = self.decoders.get(&symbol)?;
        let argument = call.arguments.first()?;
        if let Some(raw) = decoder_argument_integer(argument) {
            let text = decoder
                .value_for_raw(raw)
                .and_then(|value| value.render())?;
            self.push(call.span, text, "string_array_decode");
            return Some(CallRewriteTraversal::WalkChildren);
        }

        let Argument::ConditionalExpression(conditional) = argument else {
            return None;
        };
        let consequent = expression_integer(&conditional.consequent)
            .and_then(|raw| decoder.value_for_raw(raw))
            .and_then(|value| value.render())?;
        let alternate = expression_integer(&conditional.alternate)
            .and_then(|raw| decoder.value_for_raw(raw))
            .and_then(|value| value.render())?;
        let test = fragment(self.source, conditional.test.span());
        self.push(
            call.span,
            format!("(({test}) ? ({consequent}) : ({alternate}))"),
            "string_array_decode",
        );
        // The replacement spans the whole call. Revisit its copied test on the
        // next fixed-point iteration instead of creating overlapping edits.
        Some(CallRewriteTraversal::Stop)
    }
}

impl<'a> Visit<'a> for Collector<'_, '_> {
    fn visit_expression(&mut self, it: &Expression<'a>) {
        if let Expression::Identifier(id) = it {
            if self.shorthand_spans.contains(&(id.span.start, id.span.end)) {
                walk::walk_expression(self, it);
                return;
            }
            if let Some(reference_id) = id.reference_id.get() {
                let reference = self.scoping.get_reference(reference_id);
                if reference.is_read()
                    && !reference.is_write()
                    && !reference.flags().is_member_write_target()
                {
                    if let Some(symbol) = reference.symbol_id() {
                        if let Some(binding) = self.constants.get(&symbol) {
                            if id.span.start >= binding.available_after {
                                if let Some(text) = binding.value.render() {
                                    self.push(id.span, text, "const_propagate");
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_expression(self, it);
    }

    fn visit_binary_expression(&mut self, it: &oxc_ast::ast::BinaryExpression<'a>) {
        if matches!(it.operator.as_str(), "==" | "===" | "!=" | "!==") {
            let left_reference =
                reference_identity(&it.left, self.scoping, self.reference_identity_tables);
            let right_reference =
                reference_identity(&it.right, self.scoping, self.reference_identity_tables);
            if let (Some((left_symbol, left_identity)), Some((right_symbol, right_identity))) =
                (left_reference, right_reference)
            {
                if left_symbol == right_symbol {
                    let equal = left_identity == right_identity;
                    let value = if matches!(it.operator.as_str(), "==" | "===") {
                        equal
                    } else {
                        !equal
                    };
                    self.push(
                        it.span,
                        if value { "true" } else { "false" }.to_string(),
                        "reference_identity_compare",
                    );
                    return;
                }
            }
        }
        if let (Some(left), Some(right)) = (eval(&it.left), eval(&it.right)) {
            if let Some(value) = eval_binary(it.operator.as_str(), left, right) {
                if let Some(text) = value.render() {
                    self.push(it.span, text, "constant_fold");
                }
            }
        }
        walk::walk_binary_expression(self, it);
    }

    fn visit_unary_expression(&mut self, it: &UnaryExpression<'a>) {
        if let Some(value) = eval_unary(it) {
            if let Some(text) = value.render() {
                self.push(it.span, text, "constant_fold");
            }
        }
        walk::walk_unary_expression(self, it);
    }

    fn visit_logical_expression(&mut self, it: &LogicalExpression<'a>) {
        if let Some(value) = eval_logical(it) {
            if let Some(text) = value.render() {
                self.push(it.span, text, "constant_fold");
            }
        }
        walk::walk_logical_expression(self, it);
    }

    fn visit_conditional_expression(&mut self, it: &oxc_ast::ast::ConditionalExpression<'a>) {
        if let Some(test) = known_bool(&it.test) {
            let selected = if test { &it.consequent } else { &it.alternate };
            self.push(
                it.span,
                fragment(self.source, selected.span()).to_string(),
                "constant_branch",
            );
        }
        walk::walk_conditional_expression(self, it);
    }

    fn visit_if_statement(&mut self, it: &IfStatement<'a>) {
        if let Some(test) = known_bool(&it.test) {
            let text = if test {
                fragment(self.source, it.consequent.span()).to_string()
            } else {
                it.alternate.as_ref().map_or_else(
                    || ";".into(),
                    |s| fragment(self.source, s.span()).to_string(),
                )
            };
            self.push(it.span, text, "dead_branch");
        }
        walk::walk_if_statement(self, it);
    }

    fn visit_for_statement(&mut self, it: &oxc_ast::ast::ForStatement<'a>) {
        if let Some(text) = self.reference_state_replacement(it) {
            self.push(it.span, text, "reference_state_unflatten");
            return;
        }
        if let Some((text, proof)) = self.arithmetic_state_replacement(it) {
            self.push_arithmetic(it.span, text, proof);
            return;
        }
        if let Some(text) = self.ordered_switch_for_replacement(it) {
            self.push(it.span, text, "ordered_switch_unflatten");
            return;
        }
        walk::walk_for_statement(self, it);
    }

    fn visit_while_statement(&mut self, it: &oxc_ast::ast::WhileStatement<'a>) {
        if let Some(text) = self.ordered_switch_while_replacement(it) {
            self.push(it.span, text, "ordered_switch_unflatten");
            return;
        }
        walk::walk_while_statement(self, it);
    }

    fn visit_expression_statement(&mut self, it: &ExpressionStatement<'a>) {
        if let Expression::SequenceExpression(seq) = &it.expression {
            let text = seq
                .expressions
                .iter()
                .map(|expr| format!("({});", fragment(self.source, expr.span())))
                .collect::<Vec<_>>()
                .join("\n");
            self.push(it.span, format!("{{\n{text}\n}}"), "split_sequence");
        }
        walk::walk_expression_statement(self, it);
    }

    fn visit_static_member_expression(&mut self, it: &StaticMemberExpression<'a>) {
        if !it.optional {
            if let Some(symbol) = symbol_of(self.scoping, &it.object) {
                if let Some(ProxyProperty::Literal(value)) = self
                    .proxies
                    .get(&symbol)
                    .and_then(|object| object.get(it.property.name.as_str()))
                {
                    if let Some(text) = value.render() {
                        self.push(it.span, text, proxy_literal_kind(value));
                        return;
                    }
                }
            }
        }
        walk::walk_static_member_expression(self, it);
    }

    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        if !it.optional {
            if let Some(Value::String(property)) = eval(&it.expression) {
                if let Some(symbol) = symbol_of(self.scoping, &it.object) {
                    if let Some(ProxyProperty::Literal(value)) = self
                        .proxies
                        .get(&symbol)
                        .and_then(|object| object.get(&property))
                    {
                        if let Some(text) = value.render() {
                            self.push(it.span, text, proxy_literal_kind(value));
                            return;
                        }
                    }
                }
                if valid_property(&property) {
                    self.push(
                        it.span,
                        format!("{}.{}", fragment(self.source, it.object.span()), property),
                        "computed_property",
                    );
                    walk::walk_computed_member_expression(self, it);
                    return;
                }
            }
            if let Some(symbol) = symbol_of(self.scoping, &it.object) {
                if let Some(values) = self.arrays.get(&symbol) {
                    if let Some(index) = eval(&it.expression)
                        .and_then(|v| v.number())
                        .and_then(exact_usize)
                    {
                        if let Some(text) = values.get(index).and_then(Value::render) {
                            self.push(it.span, text, "static_array_lookup");
                            walk::walk_computed_member_expression(self, it);
                            return;
                        }
                    }
                }
            }
        }
        walk::walk_computed_member_expression(self, it);
    }

    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        let rewrite = self
            .try_selector_dispatch_rewrite(it)
            .or_else(|| self.try_proxy_call_rewrite(it))
            .or_else(|| self.try_from_char_code_alias_rewrite(it))
            .or_else(|| self.try_pure_function_rewrite(it))
            .or_else(|| self.try_decoder_rewrite(it));

        match rewrite {
            Some(CallRewriteTraversal::Stop) => {}
            Some(CallRewriteTraversal::WalkChildren) | None => {
                walk::walk_call_expression(self, it);
            }
        }
    }
}

fn eval_static_argument(arg: &Argument<'_>) -> Option<Value> {
    match arg {
        Argument::StringLiteral(v) => string_literal_value(v).map(Value::String),
        Argument::NumericLiteral(v) => Some(Value::Number(v.value)),
        Argument::BooleanLiteral(v) => Some(Value::Bool(v.value)),
        Argument::NullLiteral(_) => Some(Value::Null),
        Argument::TemplateLiteral(v) if v.expressions.is_empty() => v
            .quasis
            .first()
            .and_then(template_element_value)
            .map(Value::String),
        Argument::ParenthesizedExpression(v) => eval(&v.expression),
        Argument::UnaryExpression(v) => eval_unary(v),
        Argument::BinaryExpression(v) => {
            eval_binary(v.operator.as_str(), eval(&v.left)?, eval(&v.right)?)
        }
        Argument::LogicalExpression(v) => eval_logical(v),
        Argument::ConditionalExpression(v) => {
            let test = known_bool(&v.test)?;
            eval(if test { &v.consequent } else { &v.alternate })
        }
        _ => None,
    }
}

fn argument_integer(arg: &Argument<'_>) -> Option<i64> {
    match arg {
        Argument::NumericLiteral(v) => exact_i64(v.value),
        Argument::UnaryExpression(v) if v.operator.as_str() == "-" => match &v.argument {
            Expression::NumericLiteral(n) => exact_i64(-n.value),
            _ => None,
        },
        _ => None,
    }
}

fn decoder_argument_integer(arg: &Argument<'_>) -> Option<i64> {
    if let Some(value) = argument_integer(arg) {
        return Some(value);
    }
    let Argument::StringLiteral(literal) = arg else {
        return None;
    };
    let text = literal.value.as_str()?.trim();
    let (negative, text) = if let Some(rest) = text.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = text.strip_prefix('+') {
        (false, rest)
    } else {
        (false, text)
    };
    let value = if let Some(hex) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        i64::from_str_radix(hex, 16).ok()?
    } else {
        text.parse::<i64>().ok()?
    };
    value
        .checked_neg()
        .filter(|_| negative)
        .or_else(|| (!negative).then_some(value))
}

#[derive(Default)]
struct DirectEvalProbe {
    found: bool,
}

impl<'a> Visit<'a> for DirectEvalProbe {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(
            &call.callee,
            Expression::Identifier(identifier) if identifier.name.as_str() == "eval"
        ) {
            self.found = true;
            return;
        }
        walk::walk_call_expression(self, call);
    }
}

fn has_direct_eval(program: &oxc_ast::ast::Program<'_>) -> bool {
    let mut probe = DirectEvalProbe::default();
    probe.visit_program(program);
    probe.found
}

fn remove_unused_proven_helpers(
    scoping: &Scoping,
    decoder_helpers: &HashMap<SymbolId, Span>,
    pure_functions: &HashMap<SymbolId, PureFunction>,
    direct_eval_present: bool,
) -> Vec<Replacement> {
    if direct_eval_present {
        return Vec::new();
    }
    let root_scope = scoping.root_scope_id();

    decoder_helpers
        .iter()
        .map(|(symbol, span)| (*symbol, *span))
        .chain(pure_functions.iter().filter_map(|(symbol, function)| {
            function.declaration_span().map(|span| (*symbol, span))
        }))
        .filter(|(symbol, _)| {
            scoping.symbol_scope_id(*symbol) != root_scope && scoping.symbol_is_unused(*symbol)
        })
        .map(|(_, span)| Replacement {
            start: span.start as usize,
            end: span.end as usize,
            text: String::new(),
            kind: "remove_unused_proven_helper",
            arithmetic_state_proof: None,
        })
        .collect()
}

fn parse_as<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    source_type: SourceType,
) -> Option<oxc_ast::ast::Program<'a>> {
    let parsed = parse_program(allocator, source, source_type);
    parsed.is_clean().then_some(parsed.program)
}

#[derive(Default)]
struct WithStatementDetector {
    found: bool,
}

impl<'a> Visit<'a> for WithStatementDetector {
    fn visit_with_statement(&mut self, _statement: &WithStatement<'a>) {
        self.found = true;
    }
}

fn contains_with_statement(program: &oxc_ast::ast::Program<'_>) -> bool {
    let mut detector = WithStatementDetector::default();
    detector.visit_program(program);
    detector.found
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SafeSourceMode {
    Auto,
    Module,
    CommonJs,
}

fn semantically_valid_source_type(source: &str, mode: SafeSourceMode) -> Option<SourceType> {
    // Browser-captured `.js` is normally either a classic Script or an ES
    // Module. Let Oxc resolve that from syntax first, then pin the resolved
    // Program source type for every rewrite iteration. Explicit `.mjs`/`.cjs`
    // callers instead require the host-selected mode; falling back would change
    // the semantics of marker-free modules or CommonJS-only syntax.
    let candidates = match mode {
        SafeSourceMode::Auto => [Some(SourceType::unambiguous()), Some(SourceType::cjs())],
        SafeSourceMode::Module => [Some(SourceType::mjs()), None],
        SafeSourceMode::CommonJs => [Some(SourceType::cjs()), None],
    };
    for source_type in candidates.into_iter().flatten() {
        let allocator = Allocator::default();
        let Some(program) = parse_as(&allocator, source, source_type) else {
            continue;
        };
        if contains_with_statement(&program) {
            continue;
        }
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if semantic_ret.diagnostics.is_empty() {
            return Some(program.source_type);
        }
    }
    None
}

fn transform_once(
    source: &str,
    source_type: SourceType,
    counts: &mut Counts,
    arithmetic_state_proofs: &mut Vec<ArithmeticStateProof>,
    iteration: usize,
    standard_numeric_builtins: bool,
) -> Option<String> {
    let allocator = Allocator::default();
    let program = parse_as(&allocator, source, source_type)?;
    let semantic_ret = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&program);
    if !semantic_ret.diagnostics.is_empty() {
        return None;
    }
    let semantic = semantic_ret.semantic;
    let scoping = semantic.scoping();

    let arrays = top_level_arrays(&program);
    let reference_spans = collect_reference_spans(&program);
    let decoder_analysis = analyze_decoders(source, &program, scoping, &reference_spans);
    let decoders = decoder_analysis.decoders;
    let mut protected_spans = decoder_analysis.protected_spans;
    let mut initial_replacements = decoder_analysis.replacements;
    let constants = collect_const_values(&program, scoping);
    let shorthand_spans = collect_shorthand_spans(&program);
    let proxies = collect_proxy_objects(&program, scoping);
    let pure_functions = collect_pure_functions(&program, scoping);
    let from_char_code_aliases = collect_from_char_code_aliases(&program, scoping);
    let global_object_aliases = collect_global_object_aliases(&program, scoping);
    let reference_identity_tables =
        detect_reference_identity_tables(source, scoping, &reference_spans);
    protected_spans.extend(
        reference_identity_tables
            .values()
            .map(|table| (table.construction_start, table.construction_end)),
    );
    let stable_var_numbers = collect_stable_var_numbers(&program, scoping);
    let var_number_initializers = collect_var_number_initializers(&program);
    let selector_dispatchers = collect_selector_dispatchers(&program, scoping, &stable_var_numbers);
    let (dispatch_orders, zero_counters) = collect_dispatch_bindings(&program);
    initial_replacements.extend(remove_unused_proven_helpers(
        scoping,
        &decoder_analysis.removable_helpers,
        &pure_functions,
        has_direct_eval(&program),
    ));

    let mut collector = Collector {
        source,
        scoping,
        arrays: &arrays,
        decoders: &decoders,
        constants: &constants,
        shorthand_spans: &shorthand_spans,
        proxies: &proxies,
        pure_functions: &pure_functions,
        from_char_code_aliases: &from_char_code_aliases,
        global_object_aliases: &global_object_aliases,
        standard_numeric_builtins,
        reference_identity_tables: &reference_identity_tables,
        selector_dispatchers: &selector_dispatchers,
        dispatch_orders: &dispatch_orders,
        zero_counters: &zero_counters,
        var_number_initializers: &var_number_initializers,
        reference_spans: &reference_spans,
        protected_spans: &protected_spans,
        replacements: initial_replacements,
    };
    collector.visit_program(&program);
    if collector.replacements.is_empty() {
        Some(source.to_string())
    } else {
        apply(
            source,
            collector.replacements,
            counts,
            arithmetic_state_proofs,
            iteration,
        )
    }
}

#[derive(Debug, Clone)]
pub struct SafeTransformResult {
    pub source: String,
    pub iterations: usize,
    pub transforms: BTreeMap<String, usize>,
    pub arithmetic_state_proofs: Vec<ArithmeticStateProof>,
}

fn deobfuscate_with_mode(
    source: &str,
    max_iterations: usize,
    standard_numeric_builtins: bool,
    source_mode: SafeSourceMode,
) -> Option<SafeTransformResult> {
    // Select a source mode only after both parsing and semantic validation. Some
    // legacy browser scripts parse as modules but are invalid under module
    // strictness (for example duplicate top-level function declarations) while
    // remaining valid classic scripts/CommonJS. Preserve that distinction.
    let source_type = semantically_valid_source_type(source, source_mode)?;

    let mut current = source.to_string();
    let mut counts = Counts::default();
    let mut iterations = 0usize;
    let mut arithmetic_state_proofs = Vec::new();

    for iteration in 1..=max_iterations {
        let next = transform_once(
            &current,
            source_type,
            &mut counts,
            &mut arithmetic_state_proofs,
            iteration,
            standard_numeric_builtins,
        )?;
        if next == current {
            break;
        }
        iterations += 1;
        current = next;
    }

    Some(SafeTransformResult {
        source: current,
        iterations,
        transforms: counts.into_inner(),
        arithmetic_state_proofs,
    })
}

#[must_use]
pub fn deobfuscate(source: &str, max_iterations: usize) -> Option<SafeTransformResult> {
    deobfuscate_with_mode(source, max_iterations, false, SafeSourceMode::Auto)
}

/// Proof-oriented deobfuscation with an explicit host-language source mode.
/// Use this when filename semantics make module/CommonJS mode authoritative.
#[must_use]
pub fn deobfuscate_with_source_mode(
    source: &str,
    max_iterations: usize,
    source_mode: SafeSourceMode,
) -> Option<SafeTransformResult> {
    deobfuscate_with_mode(source, max_iterations, false, source_mode)
}

/// Proof-oriented variant that may evaluate standard numeric globals such as
/// `Number`, `parseInt`, and `Math.floor` through a proven stable global-object
/// alias. Callers must surface this assumption in any claim derived from the
/// transformed source; ordinary source rewriting must use [`deobfuscate`].
#[must_use]
pub fn deobfuscate_with_standard_numeric_builtins(
    source: &str,
    max_iterations: usize,
) -> Option<SafeTransformResult> {
    deobfuscate_with_mode(source, max_iterations, true, SafeSourceMode::Auto)
}

#[cfg(test)]
mod tests {
    use super::{
        deobfuscate, deobfuscate_with_source_mode, deobfuscate_with_standard_numeric_builtins,
        ProvenConstantEnvironment, SafeSourceMode,
    };
    use oxc_allocator::Allocator;
    use oxc_ast::ast::{CallExpression, Expression};
    use oxc_ast_visit::{walk, Visit};
    use oxc_semantic::{Scoping, SemanticBuilder};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    #[test]
    fn proven_constant_environment_respects_identity_and_declaration_order() {
        let source = r#"
            const scheme = "https://";
            const host = "api.example.test";
            const exact = scheme + host;
            sink(exact);
            sink(later);
            const later = "https://later.example.test";
            let mutable = "https://mutable.example.test";
            sink(mutable);
            function nested() {
                const exact = "https://nested.example.test";
                sink(exact);
            }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::unambiguous());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let constants = ProvenConstantEnvironment::collect(&parsed.program, scoping);

        struct Probe<'c> {
            scoping: &'c Scoping,
            constants: &'c ProvenConstantEnvironment,
            values: Vec<Option<String>>,
        }
        impl<'a> Visit<'a> for Probe<'_> {
            fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
                if matches!(&call.callee, Expression::Identifier(id) if id.name == "sink") {
                    self.values.push(
                        call.arguments
                            .first()
                            .and_then(|argument| argument.as_expression())
                            .and_then(|expression| {
                                self.constants.exact_string(expression, self.scoping)
                            }),
                    );
                }
                walk::walk_call_expression(self, call);
            }
        }

        let mut probe = Probe {
            scoping,
            constants: &constants,
            values: Vec::new(),
        };
        probe.visit_program(&parsed.program);
        assert_eq!(
            probe.values,
            [
                Some("https://api.example.test".to_string()),
                None,
                None,
                Some("https://nested.example.test".to_string()),
            ]
        );
    }

    #[test]
    fn proven_constants_fail_closed_on_lone_surrogate_strings() {
        let source = r#"
            const normal = "hello";
            const lone = "\uD800";
            const cooked = `world`;
            sink(normal);
            sink(lone);
            sink(cooked);
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::unambiguous());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let scoping = semantic.semantic.scoping();
        let constants = ProvenConstantEnvironment::collect(&parsed.program, scoping);

        struct Probe<'c> {
            scoping: &'c Scoping,
            constants: &'c ProvenConstantEnvironment,
            values: Vec<Option<String>>,
        }
        impl<'a> Visit<'a> for Probe<'_> {
            fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
                if matches!(&call.callee, Expression::Identifier(id) if id.name == "sink") {
                    self.values.push(
                        call.arguments
                            .first()
                            .and_then(|argument| argument.as_expression())
                            .and_then(|expression| {
                                self.constants.exact_string(expression, self.scoping)
                            }),
                    );
                }
                walk::walk_call_expression(self, call);
            }
        }

        let mut probe = Probe {
            scoping,
            constants: &constants,
            values: Vec::new(),
        };
        probe.visit_program(&parsed.program);
        assert_eq!(
            probe.values,
            [Some("hello".to_string()), None, Some("world".to_string())]
        );
    }

    #[test]
    fn explicit_source_mode_does_not_fall_back_across_module_commonjs_boundary() {
        let commonjs_only = "return 1;";
        assert!(
            deobfuscate_with_source_mode(commonjs_only, 1, SafeSourceMode::CommonJs,).is_some()
        );
        assert!(deobfuscate_with_source_mode(commonjs_only, 1, SafeSourceMode::Module,).is_none());
    }

    #[test]
    fn reference_state_standard_numeric_builtins_are_proof_only() {
        let source = r#"
            function identityIndex(A, B, Q, g, E, C, I, unused) {
                return (B * C ^ Q * A ^ g * E) >>> 0 & I - 1;
            }
            function predicate(A, B) {
                var Q = ~B;
                return -5*(A&B)-1*(A&Q)+7*(A|B)+5*~(A|B)-6*~(A|Q)-5*~B;
            }
            var m = window;
            var S = function(row) {
                var init, column, table = [];
                for (init = 0; init < 4; init++) table[init] = new Array(8);
                for (column = 0; column < 8; column++)
                    for (row = 0; row < 4; row++)
                        table[row][column] = table[identityIndex(3, column, row, 7, 11, 5, 4)];
                return table[1];
            }();
            var out = [];
            for (var state = S[0][0], g = m.parseInt(-122.67); true;) {
                var H = m.Number(-150);
                switch (state) {
                    case S[0][0]:
                        predicate(231, 518) < -7*(g&~H)+1*(g|H)+7*~(g&H)-7*~(g|H)-8*~(g|~H) || false
                            ? (out.push("bad"), state = S[0][2])
                            : (out.push("good"), state = S[0][1]);
                        continue;
                    case S[0][1]:
                        out.push("done");
                        break;
                    case S[0][2]:
                        out.push("wrong");
                        break;
                }
                break;
            }
        "#;

        let normal = deobfuscate(source, 16);
        assert!(normal.is_some(), "normal safe transform should succeed");
        let Some(normal) = normal else {
            return;
        };
        assert!(normal.source.contains("switch (state)"));

        let proof = deobfuscate_with_standard_numeric_builtins(source, 16);
        assert!(proof.is_some(), "proof transform should succeed");
        let Some(proof) = proof else {
            return;
        };
        assert!(!proof.source.contains("switch (state)"));
        assert!(proof.source.contains("out.push(\"good\")"));
        assert!(proof.source.contains("out.push(\"done\")"));
        assert!(!proof.source.contains("out.push(\"bad\")"));
        assert!(!proof.source.contains("out.push(\"wrong\")"));
        assert!(proof
            .transforms
            .get("reference_state_unflatten")
            .is_some_and(|count| *count >= 1));
    }
}
