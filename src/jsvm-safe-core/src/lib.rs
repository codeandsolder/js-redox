mod base91;
mod base91_recovery;
mod bitwise_algebra;
mod bitwise_effects;
mod browser_legacy;
mod control_flow;
mod decoder;
mod decoder_encoding;
mod effect_statements;
mod effectful_constant;
mod if_ladder_structure;
mod numeric;
mod proxy;
mod pure_function;
mod rewrite;
mod selector;
mod string_exposure;
mod switch_constant;
mod trivial_loops;
mod value_eval;

pub use browser_legacy::{
    recover_browser_legacy_call_assignments, BrowserLegacyCallAssignmentRecovery,
    BrowserLegacyOpaqueSpan,
};
use control_flow::{
    collect_dispatch_bindings, collect_reference_spans, detect_reference_identity_tables,
    reference_identity, ReferenceIdentityTable,
};
use decoder::{analyze_decoders, decoder_call_rewrite, js_parse_int, static_decoder_pass, Decoder};
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
pub use string_exposure::{
    expose_static_strings, expose_static_strings_with_source_mode, StaticStringExposureResult,
};
use string_exposure::{static_array_lookup_text, static_readonly_arrays};
use value_eval::{
    eval, eval_binary, eval_logical, eval_unary, eval_with_resolver, js_to_uint32, known_bool,
    Value,
};
pub use value_eval::{
    eval as eval_static_primitive, eval_with_resolver as eval_static_primitive_with_resolver,
    known_bool_with_resolver as known_static_bool_with_resolver, string_literal_value,
    template_element_value, Value as StaticPrimitiveValue,
};
use work_budget::{BudgetExceeded, WorkBudget};

pub use base91_recovery::{
    recover_base91_strings_with_source_mode, Base91DecoderProof, Base91Iteration,
    Base91RecoveryResult,
};

#[must_use]
pub fn decode_base91_ascii(encoded: &str, alphabet: &str) -> Option<String> {
    base91::Base91Alphabet::parse(alphabet)?.decode_ascii(encoded)
}

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

/// Resolve a reference to its lexical symbol only when dynamic `with` scope
/// cannot intercept the lookup before the symbol's declaration scope.
#[must_use]
pub fn statically_resolved_symbol(
    scoping: &Scoping,
    reference_id: ReferenceId,
) -> Option<SymbolId> {
    let reference = scoping.get_reference(reference_id);
    let symbol = reference.symbol_id()?;
    let symbol_scope = scoping.symbol_scope_id(symbol);
    for scope_id in scoping.scope_ancestors(reference.scope_id()) {
        if scope_id == symbol_scope {
            return Some(symbol);
        }
        if scoping.scope_flags(scope_id).is_with() {
            return None;
        }
    }
    None
}

/// Prove an unresolved identifier lookup reaches the host/global environment
/// without crossing dynamic `with` scope.
#[must_use]
pub fn statically_unresolved_global_reference(
    scoping: &Scoping,
    reference_id: ReferenceId,
) -> bool {
    let reference = scoping.get_reference(reference_id);
    reference.symbol_id().is_none()
        && scoping
            .scope_ancestors(reference.scope_id())
            .all(|scope_id| !scoping.scope_flags(scope_id).is_with())
}

#[must_use]
pub fn reference_is_statically_resolved_read(
    scoping: &Scoping,
    reference_id: ReferenceId,
    symbol: SymbolId,
) -> bool {
    let reference = scoping.get_reference(reference_id);
    !reference.is_write()
        && !reference.flags().is_member_write_target()
        && reference.is_read()
        && statically_resolved_symbol(scoping, reference_id) == Some(symbol)
}

fn symbol_has_only_read_references(scoping: &Scoping, symbol: SymbolId) -> bool {
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| reference_is_statically_resolved_read(scoping, *reference_id, symbol))
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
    collector
        .candidates
        .retain(|symbol, _| symbol_has_only_read_references(scoping, *symbol));
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

pub(crate) fn expression_integer(expr: &Expression<'_>) -> Option<i64> {
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
    collector
        .candidates
        .retain(|symbol, _| symbol_has_only_read_references(scoping, *symbol));
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

/// Dynamic eval and mapped arguments are function-local hazards for
/// numeric-state proofs. An unrelated bundled helper must not disable
/// source reconstruction throughout an entire source file.
#[derive(Default)]
struct NumericStateAliasRisks {
    /// The nearest ordinary function owns the arguments object; arrows share
    /// it, whereas an ordinary nested function has its own arguments object.
    stack: Vec<(Span, bool)>,
    unsafe_functions: HashSet<(u32, u32)>,
    unsafe_top_level: bool,
}

impl NumericStateAliasRisks {
    fn mark_eval_or_with(&mut self) {
        if self.stack.is_empty() {
            self.unsafe_top_level = true;
        }
        // Direct eval (or with) in a nested function may mutate lexical
        // bindings of any enclosing function, so include every ancestor.
        for (span, _) in &self.stack {
            self.unsafe_functions.insert((span.start, span.end));
        }
    }

    fn mark_arguments(&mut self) {
        // A reference in an arrow resolves the nearest ordinary function's
        // arguments object; only that function and the enclosed arrows can
        // observe or modify the mapped parameters through that object.
        let start = self.stack.iter().rposition(|(_, ordinary)| *ordinary);
        if let Some(start) = start {
            for (span, _) in &self.stack[start..] {
                self.unsafe_functions.insert((span.start, span.end));
            }
        } else if self.stack.is_empty() {
            self.unsafe_top_level = true;
        } else {
            for (span, _) in &self.stack {
                self.unsafe_functions.insert((span.start, span.end));
            }
        }
    }
}

impl<'a> Visit<'a> for NumericStateAliasRisks {
    fn visit_function(&mut self, function: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        self.stack.push((function.span, true));
        walk::walk_function(self, function, flags);
        self.stack.pop();
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.stack.push((function.span, false));
        walk::walk_arrow_function_expression(self, function);
        self.stack.pop();
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if matches!(&call.callee, Expression::Identifier(id) if id.name == "eval") {
            self.mark_eval_or_with();
        }
        walk::walk_call_expression(self, call);
    }

    fn visit_with_statement(&mut self, statement: &WithStatement<'a>) {
        self.mark_eval_or_with();
        walk::walk_with_statement(self, statement);
    }

    fn visit_identifier_reference(&mut self, id: &oxc_ast::ast::IdentifierReference<'a>) {
        if id.name == "arguments" {
            self.mark_arguments();
        }
    }
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
    may_remove_dead_numeric_writes: bool,
    unsafe_numeric_functions: &'c HashSet<(u32, u32)>,
    allow_effect_statements: bool,
    function_depth: usize,
    replacements: Vec<Replacement>,
}

impl Collector<'_, '_> {
    fn reconstruct_while_pairs(&mut self, statements: &[Statement<'_>]) {
        for pair in statements.windows(2) {
            if let [initial, Statement::WhileStatement(loop_stmt)] = pair {
                if let Some(code) =
                    if_ladder_structure::reconstruct_while_adjacent(initial, loop_stmt, self.source)
                {
                    self.push(
                        Span::new(initial.span().start, loop_stmt.span.end),
                        code,
                        "if_ladder_structured",
                    );
                }
            }
        }
    }

    /// Preserve a numeric state initialized before arbitrary intervening
    /// statements or an enclosing block. The real proof obligation is on
    /// the same semantic binding, not adjacency of source statements.
    fn reconstruct_reaching_while(&mut self, statements: &[Statement<'_>]) {
        self.reconstruct_reaching_while_with(statements, &HashMap::<SymbolId, (u64, Span)>::new());
    }

    fn reconstruct_reaching_while_with(
        &mut self,
        statements: &[Statement<'_>],
        inherited: &HashMap<SymbolId, (u64, Span)>,
    ) {
        if !self.may_remove_dead_numeric_writes {
            // Direct eval and sloppy arguments aliasing can change a local
            // numeric state without an ordinary lexically resolved write.
            return;
        }
        let mut reaching = inherited.clone();
        for (index, stmt) in statements.iter().enumerate() {
            if let Statement::WhileStatement(loop_stmt) = stmt {
                if let Some((symbol, name)) =
                    if_ladder_structure::while_state_binding(loop_stmt, self.scoping)
                {
                    let immediately_preceded = index > 0
                        && if_ladder_structure::state_initializer(
                            &statements[index - 1],
                            self.scoping,
                        )
                        .is_some_and(|(other, _, _)| other == symbol);
                    if !immediately_preceded {
                        if let Some(&(initial, init_span)) = reaching.get(&symbol) {
                            if self.reaching_state_is_stable(symbol, init_span, loop_stmt.span) {
                                if let Some(code) =
                                    if_ladder_structure::reconstruct_while_with_known_state(
                                        loop_stmt,
                                        name,
                                        initial,
                                        self.source,
                                    )
                                {
                                    self.push(loop_stmt.span, code, "if_ladder_structured");
                                }
                            }
                        }
                    }
                }
            }
            // Exception-driven dispatchers often use a constant-true loop,
            // rather than testing the state in the condition. The original
            // lexical initializer and write-provenance still prove its entry.
            if let Statement::WhileStatement(loop_stmt) = stmt {
                if let Statement::TryStatement(protected) = &loop_stmt.body {
                    for (&symbol, &(initial, init_span)) in &reaching {
                        if !self.reaching_state_is_stable(symbol, init_span, loop_stmt.span) {
                            continue;
                        }
                        let state = self.scoping.symbol_name(symbol);
                        if let Some(code) = if_ladder_structure::prune_exception_dispatcher(
                            loop_stmt,
                            state,
                            initial,
                            symbol,
                            self.scoping,
                            self.source,
                        ) {
                            if let Some(dispatcher) = protected.block.body.first() {
                                self.push(dispatcher.span(), code, "exception_state_pruned");
                                break;
                            }
                        }
                    }
                }
            }
            match stmt {
                Statement::BlockStatement(block) => {
                    self.reconstruct_reaching_while_with(&block.body, &reaching);
                }
                Statement::IfStatement(branch) => {
                    self.reconstruct_nested_reaching(&branch.consequent, &reaching);
                    if let Some(alternate) = &branch.alternate {
                        self.reconstruct_nested_reaching(alternate, &reaching);
                    }
                }
                _ => {}
            }
            // Kill any state whose value could have changed in this
            // statement before processing the next sibling statement.
            reaching.retain(|&symbol, _| !self.symbol_written_in_span(symbol, stmt.span()));
            if let Some((symbol, _, initial)) =
                if_ladder_structure::state_initializer(stmt, self.scoping)
            {
                if self.scoping.symbol_flags(symbol).is_variable()
                    && !self.scoping.symbol_flags(symbol).is_const_variable()
                    && self.scoping.symbol_scope_id(symbol) != self.scoping.root_scope_id()
                {
                    reaching.insert(symbol, (initial, stmt.span()));
                }
            }
        }
    }

    fn reconstruct_nested_reaching(
        &mut self,
        stmt: &Statement<'_>,
        reaching: &HashMap<SymbolId, (u64, Span)>,
    ) {
        if let Statement::BlockStatement(block) = stmt {
            self.reconstruct_reaching_while_with(&block.body, reaching);
        } else {
            self.reconstruct_reaching_while_with(std::slice::from_ref(stmt), reaching);
        }
    }

    fn symbol_written_in_span(&self, symbol: SymbolId, span: Span) -> bool {
        self.scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .any(|&ref_id| {
                let reference = self.scoping.get_reference(ref_id);
                reference.is_write()
                    && self
                        .reference_spans
                        .get(&ref_id)
                        .is_some_and(|reference_span| {
                            span.start <= reference_span.start && reference_span.end <= span.end
                        })
            })
    }

    fn reaching_state_is_stable(&self, symbol: SymbolId, init: Span, loop_span: Span) -> bool {
        self.scoping.symbol_flags(symbol).is_variable()
            && !self.scoping.symbol_flags(symbol).is_const_variable()
            && self.scoping.symbol_scope_id(symbol) != self.scoping.root_scope_id()
            && self
                .scoping
                .get_resolved_reference_ids(symbol)
                .iter()
                .all(|&ref_id| {
                    let reference = self.scoping.get_reference(ref_id);
                    if !reference.is_write() {
                        return true;
                    }
                    self.reference_spans.get(&ref_id).is_some_and(|span| {
                        (init.start <= span.start && span.end <= init.end)
                            || (loop_span.start <= span.start && span.end <= loop_span.end)
                    })
                })
    }

    // A local scalar that has no remaining lexical reads after structural
    // reconstruction cannot make numeric state assignments observable.
    // Avoid arguments aliasing and direct eval, both of which can observe
    // parameter/local writes without an ordinary identifier reference.
    fn dead_numeric_assignment(&self, expr: &Expression<'_>) -> bool {
        if !self.may_remove_dead_numeric_writes {
            return false;
        }
        let Expression::AssignmentExpression(assign) = expr else {
            return false;
        };
        if assign.operator.as_str() != "="
            || !matches!(&assign.right, Expression::NumericLiteral(_))
        {
            return false;
        }
        let oxc_ast::ast::AssignmentTarget::AssignmentTargetIdentifier(id) = &assign.left else {
            return false;
        };
        let Some(reference) = id.reference_id.get() else {
            return false;
        };
        let Some(symbol) = self.scoping.get_reference(reference).symbol_id() else {
            return false;
        };
        self.scoping.symbol_flags(symbol).is_variable()
            && !self.scoping.symbol_flags(symbol).is_const_variable()
            && self.scoping.symbol_scope_id(symbol) != self.scoping.root_scope_id()
            && self
                .scoping
                .get_resolved_reference_ids(symbol)
                .iter()
                .all(|reference_id| !self.scoping.get_reference(*reference_id).is_read())
    }

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
        let rewrite = decoder_call_rewrite(self.source, self.scoping, self.decoders, call)?;
        self.push(call.span, rewrite.text, "string_array_decode");
        Some(if rewrite.stop {
            CallRewriteTraversal::Stop
        } else {
            CallRewriteTraversal::WalkChildren
        })
    }
}

impl<'a> Visit<'a> for Collector<'_, '_> {
    fn visit_function(&mut self, it: &oxc_ast::ast::Function<'a>, flags: ScopeFlags) {
        let enclosing_safe = self.may_remove_dead_numeric_writes;
        self.may_remove_dead_numeric_writes = enclosing_safe
            && !self
                .unsafe_numeric_functions
                .contains(&(it.span.start, it.span.end));
        self.function_depth += 1;
        walk::walk_function(self, it, flags);
        self.function_depth -= 1;
        self.may_remove_dead_numeric_writes = enclosing_safe;
    }

    fn visit_arrow_function_expression(&mut self, it: &oxc_ast::ast::ArrowFunctionExpression<'a>) {
        let enclosing_safe = self.may_remove_dead_numeric_writes;
        self.may_remove_dead_numeric_writes = enclosing_safe
            && !self
                .unsafe_numeric_functions
                .contains(&(it.span.start, it.span.end));
        self.function_depth += 1;
        walk::walk_arrow_function_expression(self, it);
        self.function_depth -= 1;
        self.may_remove_dead_numeric_writes = enclosing_safe;
    }

    fn visit_expression(&mut self, it: &Expression<'a>) {
        if let Some(replacement) = effectful_constant::fold(it, self.source) {
            self.push(it.span(), replacement, "effectful_constant_fold");
            return;
        }
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
        if self.allow_effect_statements {
            if let Some(text) = bitwise_effects::normalize(it, self.source) {
                self.push(it.span, text, "bitwise_effects");
                return;
            }
        }
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

    fn visit_sequence_expression(&mut self, it: &oxc_ast::ast::SequenceExpression<'a>) {
        if let Some(replacement) = trivial_loops::prune_inert_sequence_values(it, self.source) {
            self.push(it.span, replacement, "prune_inert_sequence_values");
            return;
        }
        walk::walk_sequence_expression(self, it);
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

    fn visit_return_statement(&mut self, it: &oxc_ast::ast::ReturnStatement<'a>) {
        if let Some(Expression::SequenceExpression(sequence)) = it.argument.as_ref() {
            if let Some((last, preceding)) = sequence.expressions.split_last() {
                if !preceding.is_empty()
                    && preceding.iter().all(|expr| {
                        trivial_loops::inert_literal_statement(expr)
                            || matches!(expr, Expression::StringLiteral(_))
                    })
                {
                    // Return always performs GetValue; unlike a call
                    // callee, it cannot observe reference/this identity.
                    self.push(
                        sequence.span,
                        fragment(self.source, last.span()).to_owned(),
                        "return_inert_sequence_prefix",
                    );
                    return;
                }
            }
        }
        walk::walk_return_statement(self, it);
    }

    fn visit_if_statement(&mut self, it: &IfStatement<'a>) {
        if let Some(replacement) = trivial_loops::normalize_empty_if(it, self.source) {
            self.push(it.span, replacement, "normalize_empty_if");
            return;
        }
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

    fn visit_switch_statement(&mut self, it: &oxc_ast::ast::SwitchStatement<'a>) {
        if let Some(text) = switch_constant::select_constant_switch(it, self.source) {
            self.push(it.span, text, "constant_switch");
            return;
        }
        if let Some(text) = switch_constant::structure_boolean_switch(it, self.source) {
            self.push(it.span, text, "boolean_switch_structured");
            return;
        }
        walk::walk_switch_statement(self, it);
    }

    fn visit_for_statement(&mut self, it: &oxc_ast::ast::ForStatement<'a>) {
        if let Some(text) = trivial_loops::single_iteration_for(it, self.source) {
            self.push(it.span, text, "single_iteration_for");
            return;
        }
        if let Some(text) = if_ladder_structure::reconstruct_for(it, self.source) {
            self.push(it.span, text, "if_ladder_structured");
            return;
        }
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
        if let Some(text) = trivial_loops::never_entered_while(it) {
            self.push(it.span, text, "never_entered_loop");
            return;
        }
        if let Some(text) = self.ordered_switch_while_replacement(it) {
            self.push(it.span, text, "ordered_switch_unflatten");
            return;
        }
        walk::walk_while_statement(self, it);
    }

    fn visit_function_body(&mut self, it: &oxc_ast::ast::FunctionBody<'a>) {
        self.reconstruct_while_pairs(&it.statements);
        self.reconstruct_reaching_while(&it.statements);
        if self.allow_effect_statements
            && self.function_depth > 0
            && self.may_remove_dead_numeric_writes
        {
            for (span, expression) in
                bitwise_algebra::scan(&it.statements, self.source, self.scoping)
            {
                self.push(span, expression, "bitwise_algebra");
            }
        }
        for stmt in &it.statements {
            match stmt {
                Statement::EmptyStatement(empty) => {
                    self.push(empty.span, String::new(), "remove_empty_function_statement");
                }
                // A standalone empty block has no bindings, declarations,
                // effects, or control transfers. Do not rewrite blocks used
                // as branch, loop, labelled, or try/catch bodies.
                Statement::BlockStatement(block) if block.body.is_empty() => {
                    self.push(block.span, String::new(), "remove_empty_block_statement");
                }
                Statement::BlockStatement(block) => {
                    if let Some(flattened) =
                        trivial_loops::flatten_standalone_block(block, self.source, self.scoping)
                    {
                        self.push(block.span, flattened, "flatten_redundant_block");
                    }
                }
                _ => {}
            }
        }
        walk::walk_function_body(self, it);
    }

    fn visit_block_statement(&mut self, it: &oxc_ast::ast::BlockStatement<'a>) {
        self.reconstruct_while_pairs(&it.body);
        self.reconstruct_reaching_while(&it.body);
        if self.allow_effect_statements
            && self.function_depth > 0
            && self.may_remove_dead_numeric_writes
        {
            // Top-level var declarations may alias global object properties.
            // Direct eval, mapped arguments, and dynamic with-environments
            // may change local bindings outside the visible statement list.
            for (span, expression) in bitwise_algebra::scan(&it.body, self.source, self.scoping) {
                self.push(span, expression, "bitwise_algebra");
            }
        }
        for stmt in &it.body {
            match stmt {
                Statement::EmptyStatement(empty) => {
                    self.push(empty.span, String::new(), "remove_empty_block_statement");
                }
                Statement::BlockStatement(block) if block.body.is_empty() => {
                    self.push(block.span, String::new(), "remove_empty_block_statement");
                }
                Statement::BlockStatement(block) => {
                    if let Some(flattened) =
                        trivial_loops::flatten_standalone_block(block, self.source, self.scoping)
                    {
                        self.push(block.span, flattened, "flatten_redundant_block");
                    }
                }
                _ => {}
            }
        }
        walk::walk_block_statement(self, it);
    }

    fn visit_expression_statement(&mut self, it: &ExpressionStatement<'a>) {
        if trivial_loops::inert_literal_statement(&it.expression) {
            self.push(it.span, String::new(), "remove_inert_literal_statement");
            return;
        }
        // Script/eval Completion values can expose the result of a top-level
        // expression statement. Inside a function, a normal completion is
        // discarded; the statement may be safely normalized to if/blocks.
        if self.allow_effect_statements
            && self.function_depth > 0
            && effectful_constant::fold(&it.expression, self.source).is_none()
        {
            // A known-result effectful expression can eliminate enormous
            // dead RHS subtrees. Give it precedence over presentation-only
            // statement lowering; the next fixed-point iteration may then
            // lower the surviving effects into readable statements.
            if let Some(replacement) = effect_statements::lower(it, self.source, self.scoping) {
                self.push(it.span, replacement, "effect_statement_lowering");
                return;
            }
        }
        if self.dead_numeric_assignment(&it.expression) {
            self.push(it.span, ";".to_owned(), "dead_numeric_state_write");
            return;
        }
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
                    let object = fragment(self.source, it.object.span());
                    let text = if matches!(&it.object, Expression::NumericLiteral(_)) {
                        // `1["x"]` cannot become `1.x`: the dot is consumed as
                        // part of the numeric literal. Parenthesizing preserves
                        // the receiver while making the member access lexical.
                        format!("({object}).{property}")
                    } else {
                        format!("{object}.{property}")
                    };
                    self.push(it.span, text, "computed_property");
                    walk::walk_computed_member_expression(self, it);
                    return;
                }
            }
            if let Some(text) = static_array_lookup_text(it, self.scoping, self.arrays) {
                self.push(it.span, text, "static_array_lookup");
                walk::walk_computed_member_expression(self, it);
                return;
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SafeSourceRejection {
    ParseFailure,
    DynamicWithScope,
    SemanticFailure,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SafeSourceRecovery {
    BrowserLegacyCallAssignment,
}

impl SafeSourceRecovery {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::BrowserLegacyCallAssignment => "browser-legacy-call-assignment",
        }
    }
}

impl SafeSourceRejection {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ParseFailure => "parse-failure",
            Self::DynamicWithScope => "dynamic-with-scope",
            Self::SemanticFailure => "semantic-failure",
        }
    }
}

fn source_type_candidates(mode: SafeSourceMode) -> [Option<SourceType>; 2] {
    match mode {
        SafeSourceMode::Auto => [Some(SourceType::unambiguous()), Some(SourceType::cjs())],
        SafeSourceMode::Module => [Some(SourceType::mjs()), None],
        SafeSourceMode::CommonJs => [Some(SourceType::cjs()), None],
    }
}

fn browser_legacy_recovery_source_type(source: &str, mode: SafeSourceMode) -> Option<SourceType> {
    for source_type in source_type_candidates(mode).into_iter().flatten() {
        let Some(recovery) = recover_browser_legacy_call_assignments(source, source_type) else {
            continue;
        };
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &recovery.source, source_type);
        if !parsed.is_clean() {
            continue;
        }
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        if semantic_ret.diagnostics.is_empty() {
            return Some(parsed.program.source_type);
        }
    }
    None
}

fn validate_source_type(
    source: &str,
    mode: SafeSourceMode,
) -> Result<SourceType, SafeSourceRejection> {
    // Browser-captured `.js` is normally either a classic Script or an ES
    // Module. Let Oxc resolve that from syntax first, then pin the resolved
    // Program source type for every rewrite iteration. Explicit `.mjs`/`.cjs`
    // callers instead require the host-selected mode; falling back would change
    // the semantics of marker-free modules or CommonJS-only syntax.
    let candidates = source_type_candidates(mode);
    let mut saw_with = false;
    let mut saw_semantic_failure = false;
    for source_type in candidates.into_iter().flatten() {
        let allocator = Allocator::default();
        let Some(program) = parse_as(&allocator, source, source_type) else {
            continue;
        };
        if contains_with_statement(&program) {
            saw_with = true;
            continue;
        }
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if semantic_ret.diagnostics.is_empty() {
            return Ok(program.source_type);
        }
        saw_semantic_failure = true;
    }
    if saw_with {
        Err(SafeSourceRejection::DynamicWithScope)
    } else if saw_semantic_failure {
        Err(SafeSourceRejection::SemanticFailure)
    } else {
        Err(SafeSourceRejection::ParseFailure)
    }
}

fn semantically_valid_source_type(source: &str, mode: SafeSourceMode) -> Option<SourceType> {
    validate_source_type(source, mode).ok()
}

#[must_use]
pub fn safe_source_rejection(source: &str, mode: SafeSourceMode) -> Option<SafeSourceRejection> {
    match validate_source_type(source, mode) {
        Ok(_) => None,
        Err(SafeSourceRejection::ParseFailure)
            if browser_legacy_recovery_source_type(source, mode).is_some() =>
        {
            None
        }
        Err(rejection) => Some(rejection),
    }
}

#[derive(Clone, Copy)]
struct TransformOptions {
    standard_numeric_builtins: bool,
    allow_effect_statements: bool,
}

fn transform_once(
    source: &str,
    source_type: SourceType,
    counts: &mut Counts,
    arithmetic_state_proofs: &mut Vec<ArithmeticStateProof>,
    iteration: usize,
    options: TransformOptions,
    budget: &WorkBudget,
) -> Result<Option<String>, BudgetExceeded> {
    budget.checkpoint()?;
    let allocator = Allocator::default();
    let Some(program) = parse_as(&allocator, source, source_type) else {
        return Ok(None);
    };
    budget.checkpoint()?;
    let semantic_ret = SemanticBuilder::new()
        .with_check_syntax_error(true)
        .build(&program);
    if !semantic_ret.diagnostics.is_empty() {
        return Ok(None);
    }
    budget.checkpoint()?;
    let semantic = semantic_ret.semantic;
    let scoping = semantic.scoping();

    let arrays = static_readonly_arrays(&program, scoping);
    budget.checkpoint()?;
    let reference_spans = collect_reference_spans(&program);
    budget.checkpoint()?;
    let decoder_analysis = analyze_decoders(source, &program, scoping, &reference_spans);
    budget.checkpoint()?;
    let decoders = decoder_analysis.decoders;
    let mut protected_spans = decoder_analysis.protected_spans;
    let mut initial_replacements = decoder_analysis.replacements;
    let constants = collect_const_values(&program, scoping);
    budget.checkpoint()?;
    let shorthand_spans = collect_shorthand_spans(&program);
    let proxies = collect_proxy_objects(&program, scoping);
    budget.checkpoint()?;
    let pure_functions = collect_pure_functions(&program, scoping);
    let from_char_code_aliases = collect_from_char_code_aliases(&program, scoping);
    let global_object_aliases = collect_global_object_aliases(&program, scoping);
    budget.checkpoint()?;
    let reference_identity_tables =
        detect_reference_identity_tables(source, scoping, &reference_spans);
    budget.checkpoint()?;
    protected_spans.extend(
        reference_identity_tables
            .values()
            .map(|table| (table.construction_start, table.construction_end)),
    );
    let stable_var_numbers = collect_stable_var_numbers(&program, scoping);
    let var_number_initializers = collect_var_number_initializers(&program);
    let selector_dispatchers = collect_selector_dispatchers(&program, scoping, &stable_var_numbers);
    let (dispatch_orders, zero_counters) = collect_dispatch_bindings(&program);
    budget.checkpoint()?;
    let direct_eval_present = has_direct_eval(&program);
    let mut numeric_state_risks = NumericStateAliasRisks::default();
    numeric_state_risks.visit_program(&program);
    initial_replacements.extend(remove_unused_proven_helpers(
        scoping,
        &decoder_analysis.removable_helpers,
        &pure_functions,
        direct_eval_present,
    ));
    budget.checkpoint()?;

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
        standard_numeric_builtins: options.standard_numeric_builtins,
        reference_identity_tables: &reference_identity_tables,
        selector_dispatchers: &selector_dispatchers,
        dispatch_orders: &dispatch_orders,
        zero_counters: &zero_counters,
        var_number_initializers: &var_number_initializers,
        reference_spans: &reference_spans,
        protected_spans: &protected_spans,
        // Only dynamic scopes or arguments aliases in the *relevant lexical
        // function* can expose otherwise dead local state writes. Nonlocal
        // script syntax, including string contents, is not such a hazard.
        may_remove_dead_numeric_writes: !numeric_state_risks.unsafe_top_level,
        unsafe_numeric_functions: &numeric_state_risks.unsafe_functions,
        allow_effect_statements: options.allow_effect_statements,
        function_depth: 0,
        replacements: initial_replacements,
    };
    collector.visit_program(&program);
    budget.checkpoint()?;
    if collector.replacements.is_empty() {
        Ok(Some(source.to_string()))
    } else {
        Ok(apply(
            source,
            collector.replacements,
            counts,
            arithmetic_state_proofs,
            iteration,
        ))
    }
}

#[derive(Debug, Clone)]
pub struct StaticDecoderRecoveryResult {
    pub source: String,
    pub iterations: usize,
    pub transforms: BTreeMap<String, usize>,
    pub decoder_candidates: usize,
}

fn recover_static_decoders_with_mode(
    source: &str,
    max_iterations: usize,
    source_mode: SafeSourceMode,
    budget: &WorkBudget,
) -> Result<Option<StaticDecoderRecoveryResult>, BudgetExceeded> {
    budget.checkpoint()?;
    let Some(source_type) = semantically_valid_source_type(source, source_mode) else {
        return Ok(None);
    };
    budget.checkpoint()?;
    let mut current = source.to_string();
    let mut counts = Counts::default();
    let mut iterations = 0usize;
    let mut decoder_candidates = 0usize;

    for iteration in 1..=max_iterations {
        budget.consume(1)?;
        let allocator = Allocator::default();
        let Some(program) = parse_as(&allocator, &current, source_type) else {
            return Ok(None);
        };
        budget.checkpoint()?;
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if !semantic_ret.diagnostics.is_empty() {
            return Ok(None);
        }
        budget.checkpoint()?;
        let scoping = semantic_ret.semantic.scoping();
        let reference_spans = collect_reference_spans(&program);
        let pass = static_decoder_pass(&current, &program, scoping, &reference_spans);
        budget.checkpoint()?;
        decoder_candidates = decoder_candidates.max(pass.decoder_count);
        if pass.replacements.is_empty() {
            break;
        }
        let Some(next) = apply(
            &current,
            pass.replacements,
            &mut counts,
            &mut Vec::new(),
            iteration,
        ) else {
            return Ok(None);
        };
        if next == current {
            break;
        }
        iterations += 1;
        current = next;
    }

    Ok(Some(StaticDecoderRecoveryResult {
        source: current,
        iterations,
        transforms: counts.into_inner(),
        decoder_candidates,
    }))
}

pub fn recover_static_decoders(
    source: &str,
    max_iterations: usize,
    budget: &WorkBudget,
) -> Result<Option<StaticDecoderRecoveryResult>, BudgetExceeded> {
    recover_static_decoders_with_mode(source, max_iterations, SafeSourceMode::Auto, budget)
}

pub fn recover_static_decoders_with_source_mode(
    source: &str,
    max_iterations: usize,
    source_mode: SafeSourceMode,
    budget: &WorkBudget,
) -> Result<Option<StaticDecoderRecoveryResult>, BudgetExceeded> {
    recover_static_decoders_with_mode(source, max_iterations, source_mode, budget)
}

#[derive(Debug, Clone)]
pub struct SafeTransformResult {
    pub source: String,
    pub iterations: usize,
    pub transforms: BTreeMap<String, usize>,
    pub arithmetic_state_proofs: Vec<ArithmeticStateProof>,
    pub analysis_complete: bool,
    pub source_recovery: Option<SafeSourceRecovery>,
}

fn deobfuscate_with_mode(
    source: &str,
    max_iterations: usize,
    standard_numeric_builtins: bool,
    source_mode: SafeSourceMode,
    budget: &WorkBudget,
) -> Result<Option<SafeTransformResult>, BudgetExceeded> {
    budget.checkpoint()?;
    // Select a source mode only after both parsing and semantic validation. Some
    // legacy browser scripts parse as modules but are invalid under module
    // strictness (for example duplicate top-level function declarations) while
    // remaining valid classic scripts/CommonJS. Preserve that distinction.
    let source_type = match validate_source_type(source, source_mode) {
        Ok(source_type) => source_type,
        Err(SafeSourceRejection::ParseFailure)
            if browser_legacy_recovery_source_type(source, source_mode).is_some() =>
        {
            // The masked recovery is analysis-only. Until the proof engine can
            // model the legacy assignment target directly, preserving the exact
            // original source is the only semantics-preserving transform.
            budget.checkpoint()?;
            return Ok(Some(SafeTransformResult {
                source: source.to_string(),
                iterations: 0,
                transforms: BTreeMap::new(),
                arithmetic_state_proofs: Vec::new(),
                analysis_complete: false,
                source_recovery: Some(SafeSourceRecovery::BrowserLegacyCallAssignment),
            }));
        }
        Err(_) => return Ok(None),
    };
    budget.checkpoint()?;

    let mut current = source.to_string();
    let mut counts = Counts::default();
    let mut iterations = 0usize;
    let mut arithmetic_state_proofs = Vec::new();

    for iteration in 1..=max_iterations {
        budget.consume(1)?;
        // Semantic recovery (decoder calls, constant folding, control-flow
        // reconstruction, and pure-function evaluation) always gets the
        // original AST first. Only once that work reaches a fixed point do
        // we normalize the remaining discarded expressions for readability.
        // An eager presentation rewrite can hide source shapes required by
        // other analyzers (notably the decoder and WASM import recognizers).
        let Some(mut next) = transform_once(
            &current,
            source_type,
            &mut counts,
            &mut arithmetic_state_proofs,
            iteration,
            TransformOptions {
                standard_numeric_builtins,
                allow_effect_statements: false,
            },
            budget,
        )?
        else {
            return Ok(None);
        };
        if next == current {
            let Some(presented) = transform_once(
                &current,
                source_type,
                &mut counts,
                &mut arithmetic_state_proofs,
                iteration,
                TransformOptions {
                    standard_numeric_builtins,
                    allow_effect_statements: true,
                },
                budget,
            )?
            else {
                return Ok(None);
            };
            next = presented;
        }
        if next == current {
            break;
        }
        iterations += 1;
        current = next;
    }

    // Every ordinary fixed-point exit has already validated `current` at the
    // start of its final no-op iteration. If every allowed iteration changed
    // the source, however, there is no next iteration to validate the final
    // rewrite. Revalidate only that iteration-budget-exhaustion case so callers
    // can never receive syntactically or semantically invalid transformed source.
    if max_iterations > 0 && iterations == max_iterations {
        budget.checkpoint()?;
        let allocator = Allocator::default();
        let Some(program) = parse_as(&allocator, &current, source_type) else {
            return Ok(None);
        };
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if !semantic_ret.diagnostics.is_empty() {
            return Ok(None);
        }
        budget.checkpoint()?;
    }

    Ok(Some(SafeTransformResult {
        source: current,
        iterations,
        transforms: counts.into_inner(),
        arithmetic_state_proofs,
        analysis_complete: true,
        source_recovery: None,
    }))
}

pub fn deobfuscate(
    source: &str,
    max_iterations: usize,
    budget: &WorkBudget,
) -> Result<Option<SafeTransformResult>, BudgetExceeded> {
    deobfuscate_with_mode(source, max_iterations, false, SafeSourceMode::Auto, budget)
}

/// Proof-oriented deobfuscation with an explicit host-language source mode.
/// Use this when filename semantics make module/CommonJS mode authoritative.
pub fn deobfuscate_with_source_mode(
    source: &str,
    max_iterations: usize,
    source_mode: SafeSourceMode,
    budget: &WorkBudget,
) -> Result<Option<SafeTransformResult>, BudgetExceeded> {
    deobfuscate_with_mode(source, max_iterations, false, source_mode, budget)
}

/// Proof-oriented variant that may evaluate standard numeric globals such as
/// `Number`, `parseInt`, and `Math.floor` through a proven stable global-object
/// alias. Callers must surface this assumption in any claim derived from the
/// transformed source; ordinary source rewriting must use [`deobfuscate`].
pub fn deobfuscate_with_standard_numeric_builtins(
    source: &str,
    max_iterations: usize,
    budget: &WorkBudget,
) -> Result<Option<SafeTransformResult>, BudgetExceeded> {
    deobfuscate_with_mode(source, max_iterations, true, SafeSourceMode::Auto, budget)
}

#[cfg(test)]
mod tests {
    use super::{
        deobfuscate as deobfuscate_budgeted,
        deobfuscate_with_source_mode as deobfuscate_with_source_mode_budgeted,
        deobfuscate_with_standard_numeric_builtins as deobfuscate_with_standard_numeric_builtins_budgeted,
        expose_static_strings as expose_static_strings_budgeted,
        recover_static_decoders as recover_static_decoders_budgeted, safe_source_rejection,
        ProvenConstantEnvironment, SafeSourceMode, SafeSourceRecovery, SafeSourceRejection,
        SafeTransformResult, StaticDecoderRecoveryResult, StaticStringExposureResult,
    };
    use oxc_allocator::Allocator;
    use oxc_ast::ast::{CallExpression, Expression};
    use oxc_ast_visit::{walk, Visit};
    use oxc_semantic::{Scoping, SemanticBuilder};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    use work_budget::WorkBudget;

    fn test_budget() -> WorkBudget {
        WorkBudget::unlimited("jsvm-safe-core-test")
    }

    fn deobfuscate(source: &str, max_iterations: usize) -> Option<SafeTransformResult> {
        deobfuscate_budgeted(source, max_iterations, &test_budget())
            .ok()
            .flatten()
    }

    fn deobfuscate_with_source_mode(
        source: &str,
        max_iterations: usize,
        source_mode: SafeSourceMode,
    ) -> Option<SafeTransformResult> {
        deobfuscate_with_source_mode_budgeted(source, max_iterations, source_mode, &test_budget())
            .ok()
            .flatten()
    }

    fn deobfuscate_with_standard_numeric_builtins(
        source: &str,
        max_iterations: usize,
    ) -> Option<SafeTransformResult> {
        deobfuscate_with_standard_numeric_builtins_budgeted(source, max_iterations, &test_budget())
            .ok()
            .flatten()
    }

    fn recover_static_decoders(
        source: &str,
        max_iterations: usize,
    ) -> Option<StaticDecoderRecoveryResult> {
        recover_static_decoders_budgeted(source, max_iterations, &test_budget())
            .ok()
            .flatten()
    }

    fn expose_static_strings(
        source: &str,
        max_iterations: usize,
    ) -> Option<StaticStringExposureResult> {
        expose_static_strings_budgeted(source, max_iterations, &test_budget())
            .ok()
            .flatten()
    }

    #[test]
    fn exception_dispatcher_prunes_unreachable_state_but_keeps_catch_resume_root() {
        let source = r#"
            function f(flag, log) {
                let state=1;
                let recovery=0;
                while(true) try {
                    if(state==99) {log.push("dead");return log;}
                    else if(state==1) state=flag?2:4;
                    else if(state==2) {
                        recovery=1;
                        log.push("try");
                        throw Error("caught");
                    } else if(state==3) {
                        log.push("recovered");
                        state=4;
                    } else if(state==4) return log;
                } catch(error) {
                    if(recovery==1) {
                        log.push(error.message);
                        state=3;
                    } else throw error;
                }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        assert_eq!(
            result.transforms.get("exception_state_pruned"),
            Some(&1),
            "{result:?}"
        );
        assert!(!result.source.contains("dead"), "{}", result.source);
        assert!(result.source.contains("state==3"), "{}", result.source);
        assert!(result.source.contains("catch"), "{}", result.source);
        assert!(result.source.contains("while"), "{}", result.source);
    }

    #[test]
    fn folds_inert_nonempty_array_truthiness_without_skipping_evaluation() {
        let source = r#"
            function f(log) {
                let n=0;
                while(!["", null, 1, false, [2], {}, /x/, void 0] == 0) {
                    log.push(++n);
                    if(n==2) break;
                }
                return log;
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(
            result.is_some(),
            "inert array should allow constant folding"
        );
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|ch| !ch.is_whitespace())
            .collect();
        assert!(flat.contains("while(true)"), "{}", result.source);
    }

    #[test]
    fn non_inert_array_truthiness_keeps_observable_effects_and_tdz_reads() {
        for source in [
            "function f(log){let n=0;while(![log.push('tick')]==0){if(++n==2)break;}return log;}",
            "function f(iter){while(![...iter]==0){break;}}",
            "function f(){try{while(![later]==0){break;}}catch(e){return e.name;}let later=1;}",
        ] {
            let result = deobfuscate(source, 12);
            let output = result.map_or_else(|| source.to_owned(), |result| result.source);
            let compact: String = output.chars().filter(|ch| !ch.is_whitespace()).collect();
            assert!(compact.contains("while(!["), "{source} -> {output}");
        }
    }

    #[test]
    fn exception_dispatcher_collapses_only_silent_finite_transition_chains() {
        let source = r#"
            function f(flag, log) {
                let state = 57;
                let recovery = 0;
                while (![""] == 0) try {
                    if (state == 57) state = 73;
                    else if (state == 73) state = 37;
                    else if (state == 37) state = 25;
                    else if (state == 25) {
                        log.push("work");
                        state = flag ? 92 : 90;
                    } else if (state == 92) {
                        recovery = 1;
                        throw Error("catch");
                    } else if (state == 90) return log;
                } catch (error) {
                    log.push(error.message);
                    if (recovery == 1) state = 90;
                    else throw error;
                }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|ch| !ch.is_whitespace())
            .collect();
        assert!(!compact.contains("state==73"), "{}", result.source);
        assert!(!compact.contains("state==37"), "{}", result.source);
        assert!(compact.contains("state=25"), "{}", result.source);
        assert!(compact.contains("catch(error)"), "{}", result.source);
        assert!(
            result.transforms.contains_key("exception_state_pruned"),
            "{result:?}"
        );
    }

    #[test]
    fn exception_dispatcher_preserves_catch_entry_into_a_silent_chain() {
        let source = r#"
            function f(log) {
                let state = 1;
                let raised = false;
                while (true) try {
                    if (state == 1) {
                        if (!raised) { raised = true; throw Error("once"); }
                        state = 2;
                    } else if (state == 2) state = 3;
                    else if (state == 3) state = 4;
                    else if (state == 4) return log;
                } catch (error) {
                    log.push(error.message);
                    state = 2;
                }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|ch| !ch.is_whitespace())
            .collect();
        assert!(
            compact.contains("state==2"),
            "catch target must remain: {}",
            result.source
        );
        assert!(!compact.contains("state==3"), "{}", result.source);
        assert!(compact.contains("state=4"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_keeps_silent_cycles_and_effectful_loop_tests() {
        let cycle = r#"
            function f() {
                let state=1;
                while(true) try {
                    if(state==1) state=2;
                    else if(state==2) state=1;
                } catch(error) { throw error; }
            }
        "#;
        let output = deobfuscate(cycle, 12);
        assert!(output.is_some(), "valid source");
        let Some(output) = output else { unreachable!() };
        assert!(
            output.source.contains("state=2") && output.source.contains("state=1"),
            "{}",
            output.source
        );
        let effectful = r#"
            function f(log) {
                let state=1;
                while(log.push("test")) try {
                    if(state==1) state=2;
                    else if(state==2) state=3;
                    else if(state==3) return log;
                } catch(error) { throw error; }
            }
        "#;
        let result = deobfuscate(effectful, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|ch| !ch.is_whitespace())
            .collect();
        assert!(compact.contains("state==2"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_does_not_coerce_boolean_state_assignments() {
        let source = r#"
            function f() {
                let state=1;
                while(true) try {
                    if(state===1) state=true;
                    else if(state===true) state=3;
                    else if(state===3) return 3;
                } catch(error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|ch| !ch.is_whitespace())
            .collect();
        assert!(compact.contains("state=true"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_retargets_effectful_terminal_assignment() {
        let source = r#"
            function f(log) {
                let state = 1;
                while (true) try {
                    if (state == 1) { log.push("start"); state = 2; }
                    else if (state == 2) state = 3;
                    else if (state == 3) { log.push("finish"); state = 4; }
                    else if (state == 4) return log;
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(!flat.contains("state==2"), "{}", result.source);
        assert!(
            flat.contains("log.push(\"start\");state=3"),
            "{}",
            result.source
        );
        assert!(flat.contains("log.push(\"finish\")"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_retargets_conditional_and_sequence_terminals() {
        let source = r#"
            function f(flag, log) {
                let state = 1;
                while (true) try {
                    if (state == 1) {
                        log.push("enter");
                        state = flag ? 2 : (log.push("condition-false"), 5);
                    } else if (state == 2) state = 3;
                    else if (state == 3) { log.push("true"); state = 6; }
                    else if (state == 5) { log.push("false"); state = 6; }
                    else if (state == 6) return log;
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(!flat.contains("state==2"), "{}", result.source);
        assert!(flat.contains("flag?3:"), "{}", result.source);
        assert!(
            flat.contains("log.push(\"condition-false\")"),
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_retains_catch_root_even_if_other_entries_skip_it() {
        let source = r#"
            function f(log) {
                let state = 1, first = true;
                while (true) try {
                    if (state == 1) {
                        log.push("normal");
                        if (first) { first = false; throw Error("once"); }
                        state = 2;
                    } else if (state == 2) state = 3;
                    else if (state == 3) return log;
                } catch (error) {
                    log.push(error.message);
                    state = 2;
                }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(flat.contains("state==2"), "{}", result.source);
        assert!(flat.contains("state=3"), "{}", result.source);
        assert!(flat.contains("log.push(\"normal\")"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_factors_nonthrowing_terminal_return() {
        let source = r#"
            function f(log) {
                let state = 1;
                while (true) try {
                    if (state == 1) { log.push("before"); state = 2; }
                    else if (state == 2) return log;
                } catch (error) { log.push("caught"); throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            compact.contains("if(state==2)returnlog;"),
            "{}",
            result.source
        );
        assert_eq!(
            compact.matches("returnlog;").count(),
            1,
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_preserves_catch_entry_to_inlined_return() {
        let source = r#"
            function f(log) {
                let state = 1, first = true;
                while (true) try {
                    if (state == 1) {
                        if (first) { first = false; throw Error("once"); }
                        state = 2;
                    } else if (state == 2) return log;
                } catch (error) { log.push(error.message); state = 2; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            compact.contains("state==2"),
            "catch target must remain: {}",
            result.source
        );
        assert!(compact.contains("returnlog;"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_merges_throwing_return_in_original_catch_scope() {
        let source = r#"
            function f(object, log) {
                let state = 1;
                while (true) try {
                    if (state == 1) state = 2;
                    else if (state == 2) return object.value;
                } catch (error) { log.push(state); return log; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            compact.contains("state=2") && compact.contains("returnobject.value"),
            "getter must retain state and expression: {}",
            result.source
        );
        assert!(compact.contains("returnobject.value"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_preserves_enclosing_finally_state() {
        let source = r#"
            function f(log) {
                let state = 1;
                try {
                    while (true) try {
                        if (state == 1) state = 2;
                        else if (state == 2) return "done";
                    } catch (error) { throw error; }
                } finally {
                    log.push(state);
                }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            compact.contains("state=2;") && compact.contains("return\"done\";"),
            "{}",
            result.source
        );
        assert!(compact.contains("log.push(state)"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_factored_return_handles_automatic_semicolon_insertion() {
        let source = r#"
            function f(log) {
                let state = 1;
                while (true) try {
                    if (state == 1) {
                        log.push("before");
                        state = 2
                    } else if (state == 2) return log;
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            compact.contains("if(state==2)returnlog;"),
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_does_not_move_return_into_shadowing_block() {
        let source = r#"
            function f(value, log) {
                let state = 0;
                while (true) try {
                    if (state == 0) {
                        let value = "inner";
                        log.push(value);
                        state = 1;
                    } else if (state == 1) return value;
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            compact.contains("state==1"),
            "original return binding must survive: {}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_factors_convergent_return_region_once() {
        let source = r#"
            function f(flag, log) {
                let state = 1;
                while (true) try {
                    if (state === 1) state = flag ? 2 : 3;
                    else if (state === 2) { log.push("left"); state = 4; }
                    else if (state === 3) { log.push("right"); state = 4; }
                    else if (state === 4) return log;
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert_eq!(
            compact.matches("returnlog;").count(),
            1,
            "{}",
            result.source
        );
        assert!(!compact.contains("elseif(state===4)"), "{}", result.source);
        assert!(
            compact.contains("if(state===4)returnlog;"),
            "{}",
            result.source
        );
        assert!(
            compact.contains("log.push(\"left\")") && compact.contains("log.push(\"right\")"),
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_factors_multiple_inert_literal_returns() {
        let source = r#"
            function f(flag) {
                let state = 1;
                while (true) try {
                    if (state == 1) state = flag ? 2 : 3;
                    else if (state == 2) return ["left", true];
                    else if (state == 3) return ["right", false];
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert_eq!(compact.matches("return[").count(), 2, "{}", result.source);
        assert!(compact.contains("if(state==2)return["), "{}", result.source);
        assert!(compact.contains("if(state==3)return["), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_preserves_strict_return_state_comparison() {
        let source = r#"
            function f(flag) {
                let state = 1;
                while (true) try {
                    if (state === 1) state = flag ? 2 : 3;
                    else if (state === 2) return "two";
                    else if (state === 3) return "three";
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let compact: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            compact.contains("if(state===2)return\"two\";"),
            "{}",
            result.source
        );
        assert!(
            compact.contains("if(state===3)return\"three\";"),
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_merges_single_entry_effectful_region() {
        let source = r#"
            function f(flag, log) {
                let state = 1;
                while (true) try {
                    if (state == 1) { state = 2; }
                    else if (state == 2) {
                        log.push("effect");
                        state = flag ? 3 : 4;
                    } else if (state == 3) return "left";
                    else if (state == 4) return "right";
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(!flat.contains("if(state==2)"), "{}", result.source);
        assert!(
            flat.contains("state=2;") && flat.contains("log.push(\"effect\")"),
            "{}",
            result.source
        );
        assert_eq!(
            flat.matches("log.push(\"effect\")").count(),
            1,
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_preserves_multiple_incoming_region() {
        let source = r#"
            function f(flag) {
                let state = 1;
                while (true) try {
                    if (state == 1) state = flag ? 2 : 3;
                    else if (state == 2) state = 4;
                    else if (state == 3) state = 4;
                    else if (state == 4) return flag;
                } catch (error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        // Two independent incoming edges must share, not clone, the terminal.
        assert_eq!(flat.matches("returnflag;").count(), 1, "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_preserves_catch_root_to_single_entry_candidate() {
        let source = r#"
            function f(log) {
                let state = 1, first = true;
                while (true) try {
                    if (state == 1) {
                        if (first) { first = false; throw Error("retry"); }
                        state = 2;
                    } else if (state == 2) { log.push("resumed"); state = 3; }
                    else if (state == 3) return log;
                } catch (error) { log.push(error.message); state = 2; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            flat.contains("if(state==2)"),
            "catch-entry body remains: {}",
            result.source
        );
        assert_eq!(
            flat.matches("log.push(\"resumed\")").count(),
            1,
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_merges_target_that_can_throw() {
        let source = r#"
            function f(log) {
                let state = 1;
                while (true) try {
                    if (state === 1) state = 2;
                    else if (state === 2) {
                        log.push("at-two");
                        throw Error("oops");
                    }
                } catch (error) { log.push(error.message); return [state, log]; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            flat.contains("state=2") && flat.contains("throwError("),
            "{}",
            result.source
        );
        assert_eq!(
            flat.matches("log.push(\"at-two\")").count(),
            1,
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_merges_effectful_predecessor_prefix() {
        let source = r#"
            function f(log) {
                let state = 1;
                while (true) try {
                    if (state == 1) {
                        log.push("prefix");
                        state = 2;
                    } else if (state == 2) {
                        log.push("successor");
                        return log;
                    }
                } catch (error) { throw error; }
            }
        "#;
        let Some(result) = deobfuscate(source, 12) else {
            panic!("valid source")
        };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(!flat.contains("if(state==2)"), "{}", result.source);
        assert!(flat.contains("state=2"), "{}", result.source);
        assert_eq!(
            flat.matches("log.push(\"prefix\")").count(),
            1,
            "{}",
            result.source
        );
        assert_eq!(
            flat.matches("log.push(\"successor\")").count(),
            1,
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_merges_convergent_conditional_arms_once() {
        let source = r#"
            function f(flag, log) {
                let state = 1;
                while (true) try {
                    if (state === 1) {
                        if (flag) { log.push("left"); state = 2; }
                        else { log.push("right"); state = 2; }
                    } else if (state === 2) {
                        log.push("tail");
                        return log;
                    }
                } catch (error) { throw error; }
            }
        "#;
        let Some(result) = deobfuscate(source, 12) else {
            panic!("valid source")
        };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(!flat.contains("if(state===2)"), "{}", result.source);
        assert_eq!(
            flat.matches("log.push(\"tail\")").count(),
            1,
            "{}",
            result.source
        );
        assert_eq!(
            flat.matches("log.push(\"left\")").count(),
            1,
            "{}",
            result.source
        );
        assert_eq!(
            flat.matches("log.push(\"right\")").count(),
            1,
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_keeps_nonconvergent_conditional_target() {
        let source = r#"
            function f(flag, log) {
                let state = 1;
                while (true) try {
                    if (state == 1) {
                        if (flag) { log.push("left"); state = 2; }
                        else { log.push("right"); state = 3; }
                    } else if (state == 2) return "two";
                    else if (state == 3) return "three";
                } catch (error) { throw error; }
            }
        "#;
        let Some(result) = deobfuscate(source, 12) else {
            panic!("valid source")
        };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(
            flat.contains("state=2") && flat.contains("state=3"),
            "{}",
            result.source
        );
        assert_eq!(
            flat.matches("return\"two\";").count(),
            1,
            "{}",
            result.source
        );
        assert_eq!(
            flat.matches("return\"three\";").count(),
            1,
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_convergent_throw_preserves_catch_visible_state() {
        let source = r#"
            function f(flag, log) {
                let state = 1;
                while (true) try {
                    if (state == 1) {
                        if (flag) { log.push("left"); state = 2; }
                        else { log.push("right"); state = 2; }
                    } else if (state == 2) {
                        log.push("before-throw");
                        throw Error("oops");
                    }
                } catch (error) { log.push(error.message); return [state, log]; }
            }
        "#;
        let Some(result) = deobfuscate(source, 12) else {
            panic!("valid source")
        };
        let flat: String = result
            .source
            .chars()
            .filter(|c| !c.is_whitespace())
            .collect();
        assert!(!flat.contains("if(state==2)"), "{}", result.source);
        assert_eq!(
            flat.matches("log.push(\"before-throw\")").count(),
            1,
            "{}",
            result.source
        );
        assert!(flat.contains("return[state,log]"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_handles_inert_array_literal_loop_test() {
        let source = r#"
            function f(flag) {
                let state=1;
                while(![""]==0) try {
                    if(state==99) return "unreachable";
                    else if(state==1) state=flag?2:3;
                    else if(state==2) return "two";
                    else if(state==3) return "three";
                } catch(error) { state=3; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        assert_eq!(
            result.transforms.get("exception_state_pruned"),
            Some(&1),
            "{result:?}"
        );
        assert!(!result.source.contains("unreachable"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_preserves_destructured_var_hoists_from_dead_states() {
        let source = r#"
            const shadowed = "outer";
            function f() {
                let state=1;
                while(true) try {
                    if(state==99) {
                        var {shadowed, spare} = {shadowed:"inner", spare:42};
                        state=2;
                    } else if(state==1) return [typeof shadowed, typeof spare];
                } catch(error) { throw error; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        assert_eq!(
            result.transforms.get("exception_state_pruned"),
            Some(&1),
            "{result:?}"
        );
        assert!(!result.source.contains("state==99"), "{}", result.source);
        assert!(
            result.source.contains("var shadowed, spare;"),
            "{}",
            result.source
        );
    }

    #[test]
    fn exception_dispatcher_refuses_unknown_reachable_transitions() {
        let source = r#"
            function f(value) {
                let state=1;
                let other=0;
                while(true) try {
                    if(state==1) state=value;
                    else if(state==2) return 2;
                    else if(state==3) return 3;
                } catch(error) {
                    other++;
                    state=3;
                }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        assert!(
            !result.transforms.contains_key("exception_state_pruned"),
            "{result:?}"
        );
    }

    #[test]
    fn exception_dispatcher_refuses_loop_condition_that_mutates_state() {
        let source = r#"
            function f(log) {
                let state=1;
                while((state=99,true)) try {
                    if(state==1) return "initial";
                    else if(state==99) return "condition";
                    else if(state==2) return "other";
                } catch(error) { state=2; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        assert!(
            !result.transforms.contains_key("exception_state_pruned"),
            "{result:?}"
        );
        assert!(result.source.contains("state==99"), "{}", result.source);
    }

    #[test]
    fn exception_dispatcher_refuses_effectful_property_read_in_condition() {
        let source = r#"
            function f(guard) {
                let state=1;
                while(guard.enabled) try {
                    if(state==1) state=2;
                    else if(state==2) return 2;
                    else if(state==99) return 99;
                } catch(error) { state=2; }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        assert!(
            !result.transforms.contains_key("exception_state_pruned"),
            "{result:?}"
        );
    }

    #[test]
    fn exception_dispatcher_refuses_dynamic_catch_state() {
        let source = r#"
            function f(value) {
                let state=1;
                let other=0;
                while(true) try {
                    if(state==1) throw Error("x");
                    else if(state==2) return 2;
                    else if(state==3) return 3;
                } catch(error) {
                    other++;
                    state=value;
                }
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else { unreachable!() };
        assert!(
            !result.transforms.contains_key("exception_state_pruned"),
            "{result:?}"
        );
    }

    #[test]
    fn numeric_state_proofs_ignore_unrelated_eval_and_literal_arguments_text() {
        let fixtures = [
            // A direct eval in another function cannot observe this helper's
            // unreferenced local variable.
            "function unrelated(x){return eval(x);}function healthy(){let dead=0;dead=5;return 1;}",
            // An occurrence in string content is not an arguments reference.
            "function unrelated(){return 'arguments';}function healthy(){let dead=0;dead=5;return 1;}",
            // A nested ordinary function owns its own arguments object.
            "function healthy(){let dead=0;function inner(){return arguments[0];}dead=5;return 1;}",
        ];
        for source in fixtures {
            let result = deobfuscate(source, 12);
            assert!(result.is_some(), "fixture not recovered: {source}");
            let Some(output) = result else {
                unreachable!();
            };
            assert!(
                output
                    .transforms
                    .get("dead_numeric_state_write")
                    .is_some_and(|count| *count >= 1),
                "{source} -> {} {:#?}",
                output.source,
                output.transforms
            );
            assert!(!output.source.contains("dead=5"), "{}", output.source);
        }
    }

    #[test]
    fn numeric_state_proofs_keep_writes_visible_to_eval_and_mapped_arguments() {
        let fixtures = [
            "function f(x){x=5;eval('x');return 1;}",
            "function f(x){x=5;arguments[0];return 1;}",
            "function f(x){const change=()=>eval('x');x=5;return change();}",
            "function f(x){const nested=()=>arguments[0];x=5;return nested();}",
            // An ancestor direct eval may inspect a local written by a
            // nested ordinary function, even without a static identifier read.
            "function outer(){let state=0;function inner(){state=5;}inner();return eval('state');}",
        ];
        for source in fixtures {
            let result = deobfuscate(source, 12);
            assert!(result.is_some(), "fixture not recovered: {source}");
            let Some(output) = result else {
                unreachable!();
            };
            assert!(
                !output.transforms.contains_key("dead_numeric_state_write"),
                "{source} -> {} {:#?}",
                output.source,
                output.transforms
            );
        }
    }

    #[test]
    fn numeric_state_proofs_keep_independent_sibling_function_regions() {
        let source = r#"
            function outer(){
                function risky(x){arguments[0]=3;x=5;}
                function healthy(){let dead=0;dead=5;return 1;}
                return healthy();
            }
        "#;
        let result = deobfuscate(source, 12);
        assert!(result.is_some(), "valid source");
        let Some(result) = result else {
            unreachable!();
        };
        assert_eq!(
            result.transforms.get("dead_numeric_state_write"),
            Some(&1),
            "{result:?}"
        );
        assert!(!result.source.contains("dead=5"), "{}", result.source);
    }

    #[test]
    fn eliminates_only_standalone_empty_blocks_after_deobfuscation() {
        let input = "function recovered(flag){ {} { {} } {}; if(flag) {} else {}                     for(;flag;) {} label: {} return 7; }";
        let result = deobfuscate(input, 12);
        assert!(result.is_some(), "fixture should be valid JavaScript");
        let Some(output) = result else {
            unreachable!();
        };
        assert!(!output.source.contains("{} {"), "{}", output.source);
        assert!(!output.source.contains("{ {} }"), "{}", output.source);
        // Branches and labelled bodies are not anonymous direct statements;
        // their meaning must not be changed by a blanket brace stripper.
        // The preexisting empty-if simplifier evaluates flag once;
        // an empty loop/label body is NOT a removable standalone block.
        assert!(output.source.contains("(flag);"), "{}", output.source);
        assert!(
            output.source.contains("for(;flag;) {}"),
            "{}",
            output.source
        );
        assert!(output.source.contains("label: {}"), "{}", output.source);
        assert!(
            output
                .transforms
                .get("remove_empty_block_statement")
                .copied()
                .unwrap_or_default()
                >= 2,
            "{:?}",
            output.transforms
        );
    }

    #[test]
    fn flattens_unnecessary_nested_blocks_with_real_effects() {
        let input = "function recovered(x){ { { x+=1; } x*=2; } return x; }";
        let result = deobfuscate(input, 12);
        assert!(result.is_some());
        let Some(output) = result else {
            unreachable!();
        };
        assert!(!output.source.contains("{ {"), "{}", output.source);
        assert!(output.source.contains("x+=1"), "{}", output.source);
        assert!(output.source.contains("x*=2"), "{}", output.source);
        assert_eq!(output.transforms.get("flatten_redundant_block"), Some(&2));
    }

    #[test]
    fn retains_lexical_scopes_directives_and_control_flow_blocks() {
        let fixtures = [
            "function f(){let x=3;{let x=4;run(x);}return x;}",
            "function f(){let x=3;{const y=4;run(y);}return x;}",
            "function f(){ {class C{};run(C);}return 1;}",
            "function f(){ {function inner(){return globalThis.value;} inner.tag=1; run(inner);}return 2;}",
            "function f(){ {\"use strict\";return this;} }",
            "function f(x){if(x){return 1;}else{return 2;}}",
            "function f(x){while(x){x--;}}",
            "function f(){label:{run();break label;}}",
            "function f(){try{run();}catch(e){throw e;}}",
        ];
        for input in fixtures {
            let result = deobfuscate(input, 12);
            assert!(result.is_some(), "{input}");
            let Some(output) = result else {
                unreachable!();
            };
            assert_eq!(
                output.transforms.get("flatten_redundant_block"),
                None,
                "{input} -> {}",
                output.source
            );
        }
    }

    #[test]
    fn permits_var_hoisting_and_direct_break_targets_after_block_flattening() {
        let input = "function f(flag){var count=0;while(true){{var x=++count;if(flag)break;}break;}return [x,count];}";
        let result = deobfuscate(input, 12);
        assert!(result.is_some());
        let Some(output) = result else {
            unreachable!();
        };
        assert!(output.source.contains("var x=++count"), "{}", output.source);
        assert!(output.source.contains("if(flag)break"), "{}", output.source);
        assert!(
            output
                .transforms
                .get("flatten_redundant_block")
                .copied()
                .unwrap_or_default()
                >= 1
        );
    }

    #[test]
    fn safe_deobfuscation_propagates_work_budget_exhaustion() {
        let budget = WorkBudget::new("safe-deob-fuel", work_budget::BudgetLimits::work(0));
        assert!(matches!(
            deobfuscate_budgeted("const x = 1 + 2; sink(x);", 8, &budget),
            Err(ref error)
                if error.kind() == work_budget::BudgetExceededKind::Work
                    && error.scope() == "safe-deob-fuel"
        ));
    }

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
    fn static_string_exposure_reaches_fixed_point_without_accepting_escaping_arrays() {
        let source = r#"
            function recover() {
                const table = ["al", "pha"];
                return table[0] + table[1];
            }
        "#;
        let result = expose_static_strings(source, 4);
        assert!(result.is_some());
        let result = result.unwrap_or_else(|| unreachable!());
        assert!(result.source.contains("return \"alpha\";"));
        assert_eq!(result.iterations, 2);
        assert_eq!(
            result.transforms.get("static_string_table_lookup"),
            Some(&2)
        );
        assert_eq!(result.transforms.get("literal_string_concat"), Some(&1));

        for source in [
            r#"const table = ["a", "b"]; table[0] = "x"; sink(table[0] + table[1]);"#,
            r#"const table = ["a", "b"]; const alias = table; sink(alias, table[0]);"#,
            r#"const table = ["a", "b"]; sink(table[index]);"#,
        ] {
            let result = expose_static_strings(source, 4);
            assert!(result.is_some());
            let result = result.unwrap_or_else(|| unreachable!());
            assert_eq!(result.source, source);
            assert!(result.transforms.is_empty());
        }
    }

    #[test]
    fn computed_property_rewrite_parenthesizes_numeric_receiver() {
        let source = r#"sink(1["fetchLater"], 1.5["toString"]);"#;
        let result = deobfuscate(source, 2);
        assert!(result.is_some());
        let result = result.unwrap_or_else(|| unreachable!());
        assert_eq!(result.source, r#"sink((1).fetchLater, (1.5).toString);"#);
        assert_eq!(result.transforms.get("computed_property"), Some(&2));
        assert_eq!(
            safe_source_rejection(&result.source, SafeSourceMode::Auto),
            None
        );
    }

    #[test]
    fn static_array_lookup_requires_non_escaping_read_only_array() {
        let immutable = r#"const table = ["alpha"]; sink(table[0]);"#;
        let result = deobfuscate(immutable, 4);
        assert!(result.is_some());
        let result = result.unwrap_or_else(|| unreachable!());
        assert!(result.source.contains("sink(\"alpha\")"));
        assert_eq!(result.transforms.get("static_array_lookup"), Some(&1));

        for source in [
            r#"const table = ["before"]; table[0] = "after"; sink(table[0]);"#,
            r#"const table = ["before"]; const alias = table; alias[0] = "after"; sink(table[0]);"#,
            r#"const table = ["before"]; mutate(table); sink(table[0]);"#,
            r#"const table = ["before"]; table["push"]("after"); sink(table[0]);"#,
        ] {
            let result = deobfuscate(source, 4);
            assert!(result.is_some());
            let result = result.unwrap_or_else(|| unreachable!());
            assert!(result.source.contains("sink(table[0])"));
            assert_eq!(result.transforms.get("static_array_lookup"), None);
        }
    }

    #[test]
    fn decoder_only_recovery_proves_rotation_and_rejects_bad_checksum() {
        let source = include_str!(
            "../../../corpus/generated/reversible-obfuscation/rotated-base64-string-array.js"
        );
        let recovered = recover_static_decoders(source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert!(
            recovered
                .transforms
                .get("string_array_decode")
                .copied()
                .unwrap_or_default()
                >= 2
        );
        assert_eq!(
            recovered.transforms.get("materialize_decoder_rotation"),
            Some(&1)
        );
        assert_eq!(
            recovered.transforms.get("remove_decoder_rotation_iife"),
            Some(&1)
        );

        let bad = source.replace("2454246", "2454247");
        let rejected = recover_static_decoders(&bad, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.source, bad);
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );
    }

    #[test]
    fn decoder_only_recovery_proves_inline_self_rewriting_plain_decoder() {
        let source = r#"
function provider() {
    var table = ["alpha", "beta"];
    return (provider = function() { return table; })();
}
function decode(index, unused) {
    var table = provider();
    return (decode = function(index, unused) { return table[index -= 0x10]; })(index, unused);
}
var alias = decode;
sink(alias(0x10), alias(0x11));
"#;
        let recovered = recover_static_decoders(source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert_eq!(recovered.transforms.get("string_array_decode"), Some(&2));
        assert!(recovered.source.contains("sink(\"alpha\", \"beta\")"));

        let rebound = source.replace("var alias = decode;", "var alias = decode; alias = other;");
        let rebound_result = recover_static_decoders(&rebound, 8);
        assert!(rebound_result.is_some());
        let rebound_result = rebound_result.unwrap_or_else(|| unreachable!());
        assert_eq!(rebound_result.transforms.get("string_array_decode"), None);

        let conditional = source.replace(
            "var alias = decode;",
            "if (enabled) { var alias = decode; }",
        );
        let conditional_result = recover_static_decoders(&conditional, 8);
        assert!(conditional_result.is_some());
        let conditional_result = conditional_result.unwrap_or_else(|| unreachable!());
        assert_eq!(
            conditional_result.transforms.get("string_array_decode"),
            None
        );

        let dynamic = source.replace(
            "var alias = decode;",
            "var alias = decode; eval(\"alias = other\");",
        );
        let dynamic_result = recover_static_decoders(&dynamic, 8);
        assert!(dynamic_result.is_some());
        let dynamic_result = dynamic_result.unwrap_or_else(|| unreachable!());
        assert_eq!(dynamic_result.transforms.get("string_array_decode"), None);

        let local_alias = source.replace(
            "sink(alias(0x10), alias(0x11));",
            "function use() { var unused, local = alias; return sink(local(0x10), local(0x11)); } use();",
        );
        let local_result = recover_static_decoders(&local_alias, 8);
        assert!(local_result.is_some());
        let local_result = local_result.unwrap_or_else(|| unreachable!());
        assert!(
            local_result
                .transforms
                .get("string_array_decode")
                .copied()
                .unwrap_or_default()
                >= 2
        );

        let unsafe_leading = source.replace(
            "sink(alias(0x10), alias(0x11));",
            "function use() { var before = helper(), local = alias; return sink(local(0x10), local(0x11)); } use();",
        );
        let unsafe_result = recover_static_decoders(&unsafe_leading, 8);
        assert!(unsafe_result.is_some());
        let unsafe_result = unsafe_result.unwrap_or_else(|| unreachable!());
        assert_eq!(unsafe_result.transforms.get("string_array_decode"), None);

        let impure = source.replace(
            "var table = [\"alpha\", \"beta\"];",
            "var table = [\"alpha\", \"beta\"]; sideEffect();",
        );
        let rejected = recover_static_decoders(&impure, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
    }

    #[test]
    fn decoder_only_recovery_proves_closed_over_checksum_rotation() {
        let original = include_str!(
            "../../../corpus/generated/reversible-obfuscation/rotated-base64-string-array.js"
        );
        let rotation_start = original
            .find("(function (provider, target)")
            .unwrap_or_else(|| unreachable!());
        let rotation_end = original[rotation_start..]
            .find("\n\nconsole.log")
            .map(|offset| rotation_start + offset)
            .unwrap_or_else(|| unreachable!());
        let mut source = original.to_string();
        source.replace_range(
            rotation_start..rotation_end,
            r#"!function() {
  for (var alias = d, table = p();;) try {
    if (2454246 === parseInt(alias(0x10)) * 10 + parseInt(alias(0x11))) break;
    table.push(table.shift());
  } catch (error) {
    table.push(table.shift());
  }
}();"#,
        );

        let recovered = recover_static_decoders(&source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert!(
            recovered
                .transforms
                .get("string_array_decode")
                .copied()
                .unwrap_or_default()
                >= 2
        );
        assert_eq!(
            recovered.transforms.get("materialize_decoder_rotation"),
            Some(&1)
        );
        assert_eq!(
            recovered.transforms.get("remove_decoder_rotation_iife"),
            Some(&1)
        );
        assert!(!recovered.source.contains("table.push(table.shift())"));

        let bad = source.replace("2454246 ===", "2454247 ===");
        let rejected = recover_static_decoders(&bad, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );
        assert_eq!(
            rejected.transforms.get("remove_decoder_rotation_iife"),
            None
        );
    }

    #[test]
    fn decoder_only_recovery_generalizes_split_provider_sequence_accessor_and_nested_rotation() {
        let source = r#"
function provider(table) {
    return table = `12!34!56!78`.split(`!`), provider = function() { return table; }, provider();
}
function decode(index, unused, table, value) {
    return index = index - 0x10, table = provider(), value = table[index], value;
}
let setup, after;
for (
    setup = 1,
    function(provider_arg, target, indices, alias, table, sum) {
        for (
            indices = { a: 0x10, b: 0x11 },
            alias = decode,
            table = provider_arg();
            !![];
        ) try {
            if (
                sum = parseInt(alias(indices.a)) * 10 + parseInt(alias(indices.b)),
                target === sum
            ) break;
            else table.push(table.shift());
        } catch (error) {
            table.push(table.shift());
        }
    }(provider, 396),
    after = 2;
    false;
) {}
sink(decode(0x10), decode(0x11));
"#;
        let recovered = recover_static_decoders(source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert_eq!(recovered.transforms.get("string_array_decode"), Some(&2));
        assert_eq!(
            recovered.transforms.get("materialize_decoder_rotation"),
            Some(&1)
        );
        assert_eq!(
            recovered.transforms.get("remove_decoder_rotation_iife"),
            Some(&1)
        );
        assert!(recovered.source.contains("sink(\"34\", \"56\")"));
        assert!(recovered.source.contains("void 0"));

        let shadowed_parse_int = source.replace(
            "function(provider_arg, target, indices, alias, table, sum) {",
            "function(provider_arg, target, indices, alias, table, sum) { function parseInt() { return 36; }",
        );
        assert_ne!(shadowed_parse_int, source);
        let rejected = recover_static_decoders(&shadowed_parse_int, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );
        assert_eq!(
            rejected.transforms.get("remove_decoder_rotation_iife"),
            None
        );

        let bad = source.replace("provider, 396", "provider, 397");
        let rejected = recover_static_decoders(&bad, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );
        assert_eq!(
            rejected.transforms.get("remove_decoder_rotation_iife"),
            None
        );

        let special_proto = source.replace(
            "indices = { a: 0x10, b: 0x11 }",
            "indices = { a: 0x10, b: 0x11, __proto__: 1 }",
        );
        let rejected = recover_static_decoders(&special_proto, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );

        let shadowed_parameter = source.replace(
            "        ) try {\n            if (",
            "        ) try {\n            let indices = { a: 0x20, b: 0x21 };\n            if (",
        );
        let rejected = recover_static_decoders(&shadowed_parameter, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );

        let shadowed_decoder = source.replace(
            "    function(provider_arg, target, indices, alias, table, sum) {",
            "    function(provider_arg, target, indices, alias, table, sum) { let decode = other;",
        );
        let rejected = recover_static_decoders(&shadowed_decoder, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );

        let provider_rebound = source.replace(
            "sink(decode(0x10), decode(0x11));",
            "provider = replacement; sink(decode(0x10), decode(0x11));",
        );
        let rejected = recover_static_decoders(&provider_rebound, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);

        let outer_table = source.replace(
            "function decode(index, unused, table, value) {",
            "let table; function decode(index, unused, value) {",
        );
        let rejected = recover_static_decoders(&outer_table, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);

        let outer_value = source.replace(
            "function decode(index, unused, table, value) {",
            "let value; function decode(index, unused, table) {",
        );
        let rejected = recover_static_decoders(&outer_value, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);

        let collapsed_table_role = source.replace(
            "function decode(index, unused, table, value) {\n    return index = index - 0x10, table = provider(), value = table[index], value;",
            "function decode(index, unused, value) {\n    return index = index - 0x10, index = provider(), value = index[index], value;",
        );
        let rejected = recover_static_decoders(&collapsed_table_role, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);

        let collapsed_value_role = source.replace(
            "function decode(index, unused, table, value) {\n    return index = index - 0x10, table = provider(), value = table[index], value;",
            "function decode(index, unused, table) {\n    return index = index - 0x10, table = provider(), table = table[index], table;",
        );
        let rejected = recover_static_decoders(&collapsed_value_role, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);

        let rebound_rotation_alias = source.replace(
            "        ) try {\n            if (",
            "        ) try {\n            alias = replacement;\n            if (",
        );
        let rejected = recover_static_decoders(&rebound_rotation_alias, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
        assert_eq!(
            rejected.transforms.get("materialize_decoder_rotation"),
            None
        );

        let dynamic_eval = source.replace(
            "        ) try {\n            if (",
            "        ) try {\n            eval(\"alias = replacement\");\n            if (",
        );
        let rejected = recover_static_decoders(&dynamic_eval, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
    }

    #[test]
    fn decoder_alias_assigned_in_for_initializer_is_dominating_and_stable() {
        let source = r#"
function provider(table) {
    return table = `alpha!beta`.split(`!`), provider = function() { return table; }, provider();
}
function decode(index, table, value) {
    return index = index - 0x10, table = provider(), value = table[index], value;
}
function use(alias) {
    for (alias = decode; true;) {
        sink(alias(0x10), alias(0x11));
        break;
    }
}
use();
"#;
        let recovered = recover_static_decoders(source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert_eq!(recovered.transforms.get("string_array_decode"), Some(&2));
        assert!(recovered.source.contains("sink(\"alpha\", \"beta\")"));

        let mutated = source.replace(
            "sink(alias(0x10), alias(0x11));",
            "sink(alias(0x10), alias(0x11)); alias = replacement;",
        );
        let rejected = recover_static_decoders(&mutated, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
    }

    #[test]
    fn decoder_alias_first_statement_dominates_closure_reads() {
        let source = r#"
function provider(table) {
    return table = `alpha!beta`.split(`!`), provider = function() { return table; }, provider();
}
function decode(index, table, value) {
    return index = index - 0x10, table = provider(), value = table[index], value;
}
function use(alias) {
    for (alias = decode; false;) {}
    function later() {
        return alias(0x10);
    }
    sink(later(), alias(0x11));
}
use();
"#;
        let recovered = recover_static_decoders(source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert_eq!(recovered.transforms.get("string_array_decode"), Some(&2));
        assert!(recovered.source.contains("return \"alpha\""));
        assert!(recovered.source.contains("sink(later(), \"beta\")"));

        let preceded = source.replace(
            "function use(alias) {\n    for",
            "function use(alias) {\n    before();\n    for",
        );
        let rejected = recover_static_decoders(&preceded, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);

        let delayed = source.replace("for (alias = decode;", "for (before(), alias = decode;");
        let rejected = recover_static_decoders(&delayed, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert_eq!(rejected.transforms.get("string_array_decode"), None);
    }

    #[test]
    fn standard_base64_decoder_uses_structural_local_effect_proof() {
        let source = r#"
const sequence_table = ["YQ=="];
function sequence_decode(index, cached) {
    return cached = sequence_table[(index)], (atob)((cached));
}
const declaration_table = ["Yg=="];
function declaration_decode(index) {
    "use strict";
    const cached = declaration_table[index];
    return atob(cached);
}
const rest_table = ["Yw=="];
function rest_decode(index, ...unused) {
    return atob(rest_table[index]);
}
sink(sequence_decode(0), declaration_decode(0), rest_decode(0));
"#;
        let recovered = recover_static_decoders(source, 4);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert_eq!(recovered.transforms.get("string_array_decode"), Some(&3));
        assert!(recovered.source.contains("sink(\"a\", \"b\", \"c\")"));

        for rejected_source in [
            r#"
const table = ["YQ=="];
let escaped;
function decode(index) {
    escaped = table[index];
    return atob(escaped);
}
sink(decode(0));
"#,
            r#"
const table = ["YQ=="];
function outer(atob) {
    function decode(index) { return atob(table[index]); }
    return decode(0);
}
sink(outer(identity));
"#,
            r#"
const table = ["YQ=="];
async function decode(index) { return atob(table[index]); }
sink(decode(0));
"#,
            r#"
const table = ["YQ=="];
function decode(index, ignored = sideEffect()) { return atob(table[index]); }
sink(decode(0));
"#,
        ] {
            let rejected = recover_static_decoders(rejected_source, 4);
            assert!(rejected.is_some());
            let rejected = rejected.unwrap_or_else(|| unreachable!());
            assert_eq!(rejected.transforms.get("string_array_decode"), None);
        }
    }

    #[test]
    fn fixed_base64_decoder_proves_dataflow_instead_of_operation_counts() {
        let source = r#"
const table = ["us49uStFKk5Z"];
function decode(index, value) {
    if ("string" != typeof (value = table[index])) return value;
    for (
        var byte0, sextet0, sextet3, sextet2, sextet1, byte1, output = void 0,
            alphabet = "318mC4sQfF7VWJ/h5AiBOtzHogbKun2jvxwlp6NkXD=eUraRTy9+GcS0qYEIdLMPZ",
            cursor = 0,
            input = (input = value).replace(/[^A-Za-z0-9\+\/\=]/g, output = "");
        cursor < input.length;
    )
        sextet0 = alphabet.indexOf(input.charAt(cursor++)),
        byte1 = (15 & (sextet1 = alphabet.indexOf(input.charAt(cursor++)))) << 4 | (sextet2 = alphabet.indexOf(input.charAt(cursor++))) >> 2,
        byte0 = (3 & sextet2) << 6 | (sextet3 = alphabet.indexOf(input.charAt(cursor++))),
        output += String.fromCharCode(sextet0 << 2 | sextet1 >> 4),
        64 != sextet2 && (output += String.fromCharCode(byte1)),
        64 != sextet3 && (output += String.fromCharCode(byte0));
    return output;
}
sink(decode(0));
"#;
        let recovered = recover_static_decoders(source, 4);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert_eq!(recovered.transforms.get("string_array_decode"), Some(&1));

        let equivalent_filter = source.replace(r"\+\/\=", r"+\/=");
        let equivalent = recover_static_decoders(&equivalent_filter, 4);
        assert!(equivalent.is_some());
        let equivalent = equivalent.unwrap_or_else(|| unreachable!());
        assert_eq!(equivalent.transforms.get("string_array_decode"), Some(&1));

        let dead_short_circuit_setup =
            source.replace("cursor = 0,", "cursor = 1, hidden = false && (cursor = 0),");
        assert_ne!(dead_short_circuit_setup, source);

        let deferred_setup = source.replace(
            r#"output = void 0,
            alphabet = "318mC4sQfF7VWJ/h5AiBOtzHogbKun2jvxwlp6NkXD=eUraRTy9+GcS0qYEIdLMPZ",
            cursor = 0,
            input = (input = value).replace(/[^A-Za-z0-9\+\/\=]/g, output = "")"#,
            r#"output, alphabet, cursor, input,
            hidden = () => (
                alphabet = "318mC4sQfF7VWJ/h5AiBOtzHogbKun2jvxwlp6NkXD=eUraRTy9+GcS0qYEIdLMPZ",
                cursor = 0,
                input = (input = value).replace(/[^A-Za-z0-9\+\/\=]/g, output = "")
            )"#,
        );
        assert_ne!(deferred_setup, source);

        for rejected_source in [
            source.replace("sextet1 >> 4", "sextet1 >> 3"),
            source.replace("64 != sextet2", "64 != sextet1"),
            source.replace("var byte0,", "var hidden = sideEffect(), byte0,"),
            dead_short_circuit_setup,
            deferred_setup,
        ] {
            let rejected = recover_static_decoders(&rejected_source, 4);
            assert!(rejected.is_some());
            let rejected = rejected.unwrap_or_else(|| unreachable!());
            assert_eq!(rejected.transforms.get("string_array_decode"), None);
        }
    }

    #[test]
    fn fixed_base64_iife_rejects_effectful_setup_reads() {
        let source =
            include_str!("../../../corpus/generated/reversible-obfuscation/sparse-direct-table.js");
        let recovered = recover_static_decoders(source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert!(!recovered.source.contains("INested(0)"));

        let effectful = source.replace("var r, c, u, x,", "var hidden = n.x, r, c, u, x,");
        let rejected = recover_static_decoders(&effectful, 8);
        assert!(rejected.is_some());
        let rejected = rejected.unwrap_or_else(|| unreachable!());
        assert!(rejected.source.contains("INested(0)"));
    }

    #[test]
    fn decoder_only_recovery_handles_literal_key_rc4() {
        let source = r#"
function p(){var table=["xSov","xCor"];p=function(){return table;};return p();}
function d(a,b){var c=p();return d=function(x,y){x=x-0x10;var v=c[x];if(d.ready===undefined){var decode=function(s){var alphabet="abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=";var bytes="",uri="",helper=bytes+decode;for(var q=0,r,ch,i=0;ch=s.charAt(i++);~ch&&(r=q%4?r*64+ch:ch,q++%4)?bytes+=helper.charCodeAt(i+10)-10!==0?String.fromCharCode(255&r>>(-2*q&6)):q:0){ch=alphabet.indexOf(ch);}for(var z=0;z<bytes.length;z++){uri+="%"+("00"+bytes.charCodeAt(z).toString(16)).slice(-2);}return decodeURIComponent(uri);};var rc4=function(str,key){var state=[],j=0,tmp,out="";for(var i=0;i<0x100;i++){state[i]=i;}for(i=0;i<0x100;i++){j=(j+state[i]+key.charCodeAt(i%key.length))%0x100;tmp=state[i];state[i]=state[j];state[j]=tmp;}i=0;j=0;for(var n=0;n<str.length;n++){i=(i+1)%0x100;j=(j+state[i])%0x100;tmp=state[i];state[i]=state[j];state[j]=tmp;out+=String.fromCharCode(str.charCodeAt(n)^state[(state[i]+state[j])%0x100]);}return out;};d.decode=function(value,key){return rc4(decode(value),key);};d.ready=true;}v=d.decode(v,y);return v;},d(a,b);}
console.log(d(0x10,"k"),d(0x11,"k"));
"#;
        let recovered = recover_static_decoders(source, 8);
        assert!(recovered.is_some());
        let recovered = recovered.unwrap_or_else(|| unreachable!());
        assert_eq!(recovered.transforms.get("string_array_decode"), Some(&2));
        assert!(recovered.source.contains("\"17\""));
        assert!(recovered.source.contains("\"23\""));
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
    fn safe_source_rejection_distinguishes_dynamic_scope_from_parse_failure() {
        assert_eq!(
            safe_source_rejection("with (scope) { value; }", SafeSourceMode::CommonJs),
            Some(SafeSourceRejection::DynamicWithScope)
        );
        assert_eq!(
            safe_source_rejection("(1 + 2) = 3;", SafeSourceMode::CommonJs),
            Some(SafeSourceRejection::ParseFailure)
        );
        assert_eq!(
            safe_source_rejection("const value = 1;", SafeSourceMode::CommonJs),
            None
        );
        let legacy = "function target() {} target() = 1;";
        assert_eq!(
            safe_source_rejection(legacy, SafeSourceMode::CommonJs),
            None
        );
        let result = deobfuscate_with_source_mode(legacy, 16, SafeSourceMode::CommonJs);
        assert!(
            result.is_some(),
            "legacy browser syntax should be preserved as an explicit pass-through"
        );
        let result = result.unwrap_or_else(|| unreachable!());
        assert_eq!(result.source, legacy);
        assert_eq!(result.iterations, 0);
        assert!(!result.analysis_complete);
        assert_eq!(
            result.source_recovery,
            Some(SafeSourceRecovery::BrowserLegacyCallAssignment)
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

#[cfg(test)]
mod fixture_regressions {
    use super::{deobfuscate, safe_source_rejection, SafeSourceMode};
    use work_budget::WorkBudget;

    fn checked(source: &str) -> super::SafeTransformResult {
        let result = deobfuscate(source, 16, &WorkBudget::unlimited("fixture-regression"))
            .ok()
            .flatten();
        assert!(
            result.is_some(),
            "fixture should be accepted by safe deobfuscation"
        );
        let Some(result) = result else {
            unreachable!();
        };
        assert_eq!(
            safe_source_rejection(&result.source, SafeSourceMode::Auto),
            None,
            "transformed fixture must remain parser-valid"
        );
        result
    }

    #[test]
    fn selector_dispatch_fixture_specializes_only_proven_calls() {
        let source =
            include_str!("../../../corpus/generated/reversible-obfuscation/selector-dispatch.js");
        let result = checked(source);
        assert_eq!(
            result.transforms.get("selector_dispatch_specialize"),
            Some(&7)
        );
        assert!(result.source.contains("dispatch(42, 9, 4)"));
        assert_eq!(result.source.matches("ambiguous(1, 4)").count(), 2);
    }

    #[test]
    fn direct_table_fixture_keeps_unsafe_decoder_shapes_dynamic() {
        let source = include_str!(
            "../../../corpus/generated/reversible-obfuscation/datadome-direct-table.js"
        );
        let result = checked(source);
        for dynamic in [
            "QInvalid(0)",
            "QDecoy(0)",
            "CDecoy(0)",
            "reassigned(5, 2)",
            "QEscaped(0)",
            "QInternalEscaped(0)",
            "QReassigned(0)",
            "QSideEffect(0)",
            "C(7)",
            "C(dynamicChoice ? 0 : 7)",
            "CFixedSide(0)",
        ] {
            assert!(
                result.source.contains(dynamic),
                "missing dynamic shape {dynamic}"
            );
        }
        assert!(!result.source.contains("C(dynamicChoice ? 0 : 1)"));
        for recovered in [
            "\"cookie\"",
            "\"reload\"",
            "\"parseInt\"",
            "17",
            "true",
            "null",
        ] {
            assert!(
                result.source.contains(recovered),
                "missing recovered value {recovered}"
            );
        }
        assert!(result
            .transforms
            .get("string_array_decode")
            .is_some_and(|count| *count >= 15));
        assert!(result
            .transforms
            .get("pure_function_eval")
            .is_some_and(|count| *count >= 5));
    }

    #[test]
    fn sparse_direct_table_fixture_folds_only_proven_entries() {
        let source =
            include_str!("../../../corpus/generated/reversible-obfuscation/sparse-direct-table.js");
        let result = checked(source);
        for folded in ["QSparse(0)", "QSparse(2)", "CSparse(0)", "CSparse(2)"] {
            assert!(!result.source.contains(folded), "failed to fold {folded}");
        }
        for dynamic in ["QSparse(1)", "CSparse(1)", "INested(1)"] {
            assert!(
                result.source.contains(dynamic),
                "lost dynamic shape {dynamic}"
            );
        }
        assert!(!result.source.contains("INested(0)"));
        assert!(result
            .transforms
            .get("string_array_decode")
            .is_some_and(|count| *count >= 5));
    }

    #[test]
    fn reference_identity_fixture_unflattens_proven_state_machine() {
        let source = include_str!(
            "../../../corpus/generated/reversible-obfuscation/reference-identity-table.js"
        );
        let result = checked(source);
        assert!(!result.source.contains("S[0][0] === S[4][0]"));
        assert!(!result.source.contains("S[0][0] !== S[0][1]"));
        assert!(!result.source.contains("switch (state)"));
        assert!(!result.source.contains("switch(state)"));
        assert!(result
            .transforms
            .get("reference_identity_compare")
            .is_some_and(|count| *count >= 4));
        assert!(result
            .transforms
            .get("reference_state_unflatten")
            .is_some_and(|count| *count >= 1));
    }
}
