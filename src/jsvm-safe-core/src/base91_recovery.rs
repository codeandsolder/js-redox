use crate::rewrite::{apply, Counts, Replacement};
use crate::string_exposure::static_string_exposure_pass;
use crate::value_eval::{string_literal_value, Value};
use crate::{
    array_element, decode_base91_ascii, parse_as, source_type_candidates,
    statically_resolved_symbol, SafeSourceMode,
};
use oxc_allocator::Allocator;
use oxc_ast::ast::{Argument, AssignmentTarget, BindingPattern, Expression};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{SourceType, Span};
use oxc_syntax::{scope::ScopeId, symbol::SymbolId};
use regex::{Captures, Regex};
use std::collections::{BTreeMap, HashMap, HashSet};

const IDENT: &str = r"[A-Za-z_$][A-Za-z0-9_$]*";
const NUM: &str = r"(?:0[xX][0-9A-Fa-f]+|\d+)";
const SIGNATURE: [&str; 10] = [
    ".indexOf(",
    ".push(",
    "*91",
    "&8191",
    ">88?13:14",
    "&255",
    ">>=8",
    "-=8",
    "=-1",
    ">-1",
];

#[derive(Debug, Clone)]
pub struct Base91DecoderProof {
    pub decoder: String,
    pub provider: String,
    pub transform: String,
    pub rotation: usize,
    pub table_entries: usize,
    pub scope_start: usize,
    pub scope_end: usize,
    pub declaration_start: usize,
    pub replacements: usize,
    pub iteration: usize,
}

#[derive(Debug, Clone)]
pub struct Base91Iteration {
    pub iteration: usize,
    pub preflight_skipped: bool,
    pub decoder_calls: usize,
    pub immutable_string_table_replacements: usize,
    pub literal_concat_folds: usize,
}

#[derive(Debug, Clone)]
pub struct Base91RecoveryResult {
    pub source: String,
    pub decoders: Vec<Base91DecoderProof>,
    pub iterations: Vec<Base91Iteration>,
    pub replacements: usize,
    pub transforms: BTreeMap<String, usize>,
}

fn owning_function_scope(scoping: &Scoping, mut scope: ScopeId) -> ScopeId {
    loop {
        if scoping.scope_flags(scope).is_function() || scoping.scope_parent_id(scope).is_none() {
            return scope;
        }
        let Some(parent) = scoping.scope_parent_id(scope) else {
            return scope;
        };
        scope = parent;
    }
}

fn scope_is_descendant_of(scoping: &Scoping, scope: ScopeId, ancestor: ScopeId) -> bool {
    scoping
        .scope_ancestors(scope)
        .any(|candidate| candidate == ancestor)
}

#[derive(Debug, Clone)]
struct FunctionInfo {
    symbol: SymbolId,
    name: String,
    params: Vec<String>,
    span: Span,
    owner_scope: ScopeId,
    body_scope: ScopeId,
}

struct FunctionCollector<'s> {
    scoping: &'s Scoping,
    functions: Vec<FunctionInfo>,
    scope_spans: HashMap<ScopeId, Span>,
}

impl<'a> Visit<'a> for FunctionCollector<'_> {
    fn visit_function(
        &mut self,
        function: &oxc_ast::ast::Function<'a>,
        flags: oxc_syntax::scope::ScopeFlags,
    ) {
        if let Some(body_scope) = function.scope_id.get() {
            self.scope_spans.insert(body_scope, function.span);
            if let Some(id) = &function.id {
                if let Some(symbol) = id.symbol_id.get() {
                    let params = function
                        .params
                        .items
                        .iter()
                        .filter_map(|param| match &param.pattern {
                            BindingPattern::BindingIdentifier(id) => Some(id.name.to_string()),
                            _ => None,
                        })
                        .collect();
                    self.functions.push(FunctionInfo {
                        symbol,
                        name: id.name.to_string(),
                        params,
                        span: function.span,
                        owner_scope: owning_function_scope(
                            self.scoping,
                            self.scoping.symbol_scope_id(symbol),
                        ),
                        body_scope,
                    });
                }
            }
        }
        walk::walk_function(self, function, flags);
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        if let Some(scope) = function.scope_id.get() {
            self.scope_spans.insert(scope, function.span);
        }
        walk::walk_arrow_function_expression(self, function);
    }
}

struct FunctionCallCollector<'s> {
    scoping: &'s Scoping,
    calls: HashMap<ScopeId, HashSet<SymbolId>>,
}

impl<'a> Visit<'a> for FunctionCallCollector<'_> {
    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        if let Expression::Identifier(callee) = &call.callee {
            if let Some(reference) = callee.reference_id.get() {
                if let Some(symbol) = statically_resolved_symbol(self.scoping, reference) {
                    let caller = owning_function_scope(
                        self.scoping,
                        self.scoping.get_reference(reference).scope_id(),
                    );
                    self.calls.entry(caller).or_default().insert(symbol);
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn reachable_nested_function_scopes(
    scoping: &Scoping,
    decoder: &FunctionInfo,
    functions: &[FunctionInfo],
    calls: &HashMap<ScopeId, HashSet<SymbolId>>,
) -> HashSet<ScopeId> {
    let by_symbol = functions
        .iter()
        .map(|function| (function.symbol, function))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::from([decoder.body_scope]);
    let mut pending = vec![decoder.body_scope];
    while let Some(caller) = pending.pop() {
        for symbol in calls.get(&caller).into_iter().flatten() {
            let Some(callee) = by_symbol.get(symbol).copied() else {
                continue;
            };
            // Only lexical descendants are implementation delegates. Calls to
            // sibling/global helpers do not make those helpers part of the
            // decoder proof merely because the decoder invokes them.
            if !scope_is_descendant_of(scoping, callee.owner_scope, decoder.body_scope) {
                continue;
            }
            if reachable.insert(callee.body_scope) {
                pending.push(callee.body_scope);
            }
        }
    }
    reachable
}

#[derive(Debug, Clone)]
struct ProviderTable {
    provider: String,
    provider_symbol: SymbolId,
    rotator_symbol: SymbolId,
    values: Vec<String>,
    rotation: usize,
    assignment_start: usize,
    assignment_end: usize,
    owner_scope: ScopeId,
}

struct ProviderCollector<'s> {
    scoping: &'s Scoping,
    providers: Vec<ProviderTable>,
}

fn argument_number(argument: &Argument<'_>) -> Option<f64> {
    match argument {
        Argument::NumericLiteral(value) => Some(value.value),
        _ => None,
    }
}

impl<'a> Visit<'a> for ProviderCollector<'_> {
    fn visit_assignment_expression(&mut self, assignment: &oxc_ast::ast::AssignmentExpression<'a>) {
        if assignment.operator.as_str() == "=" {
            if let AssignmentTarget::AssignmentTargetIdentifier(target) = &assignment.left {
                if let Expression::CallExpression(call) = &assignment.right {
                    if !call.optional && call.arguments.len() == 2 {
                        if let Expression::Identifier(rotator) = &call.callee {
                            if let Argument::ArrayExpression(array) = &call.arguments[0] {
                                let provider_reference = target.reference_id.get();
                                let provider_symbol = provider_reference.and_then(|reference| {
                                    statically_resolved_symbol(self.scoping, reference)
                                });
                                let owner_scope = provider_reference.map(|reference| {
                                    owning_function_scope(
                                        self.scoping,
                                        self.scoping.get_reference(reference).scope_id(),
                                    )
                                });
                                let rotator_symbol =
                                    rotator.reference_id.get().and_then(|reference| {
                                        statically_resolved_symbol(self.scoping, reference)
                                    });
                                let values = array
                                    .elements
                                    .iter()
                                    .map(array_element)
                                    .map(|value| match value {
                                        Some(Value::String(value)) => Some(value),
                                        _ => None,
                                    })
                                    .collect::<Option<Vec<_>>>();
                                let rotation = argument_number(&call.arguments[1])
                                    .filter(|value| {
                                        value.is_finite() && *value >= 0.0 && value.fract() == 0.0
                                    })
                                    .and_then(crate::exact_usize);
                                if let (
                                    Some(provider_symbol),
                                    Some(rotator_symbol),
                                    Some(values),
                                    Some(rotation),
                                    Some(owner_scope),
                                ) = (
                                    provider_symbol,
                                    rotator_symbol,
                                    values,
                                    rotation,
                                    owner_scope,
                                ) {
                                    if !values.is_empty() {
                                        self.providers.push(ProviderTable {
                                            provider: target.name.to_string(),
                                            provider_symbol,
                                            rotator_symbol,
                                            rotation: rotation % values.len(),
                                            values,
                                            assignment_start: assignment.span.start as usize,
                                            assignment_end: assignment.span.end as usize,
                                            owner_scope,
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_assignment_expression(self, assignment);
    }
}

#[derive(Default)]
struct SimpleArrayCollector {
    arrays: HashMap<String, Vec<Value>>,
    by_symbol: HashMap<SymbolId, Vec<Value>>,
}

impl<'a> Visit<'a> for SimpleArrayCollector {
    fn visit_variable_declaration(&mut self, declaration: &oxc_ast::ast::VariableDeclaration<'a>) {
        for item in &declaration.declarations {
            let BindingPattern::BindingIdentifier(id) = &item.id else {
                continue;
            };
            let Some(Expression::ArrayExpression(array)) = &item.init else {
                continue;
            };
            let Some(values) = array
                .elements
                .iter()
                .map(array_element)
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if !values.is_empty() {
                if let Some(symbol) = id.symbol_id.get() {
                    self.by_symbol.insert(symbol, values.clone());
                }
                self.arrays.insert(id.name.to_string(), values);
            }
        }
        walk::walk_variable_declaration(self, declaration);
    }
}

fn parse_semantically_allow_with(source: &str, mode: SafeSourceMode) -> Option<SourceType> {
    for source_type in source_type_candidates(mode).into_iter().flatten() {
        let allocator = Allocator::default();
        let Some(program) = parse_as(&allocator, source, source_type) else {
            continue;
        };
        let semantic = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if semantic.diagnostics.is_empty() {
            return Some(program.source_type);
        }
    }
    None
}

fn fragment(source: &str, span: Span) -> &str {
    source
        .get(span.start as usize..(span.end as usize).min(source.len()))
        .unwrap_or_default()
}

fn function_body<'a>(source: &'a str, function: &FunctionInfo) -> &'a str {
    let text = fragment(source, function.span);
    let Some(start) = text.find('{') else {
        return text;
    };
    let Some(end) = text.rfind('}') else {
        return text;
    };
    text.get(start + 1..end).unwrap_or(text)
}

fn function_scope_span(
    scoping: &Scoping,
    scope_spans: &HashMap<ScopeId, Span>,
    scope: ScopeId,
    source_len: usize,
) -> Option<(usize, usize)> {
    if scope == scoping.root_scope_id() {
        return Some((0, source_len));
    }
    scope_spans
        .get(&scope)
        .map(|span| (span.start as usize, span.end as usize))
}

fn rotator_matches(source: &str, function: &FunctionInfo) -> bool {
    let [array, count, ..] = function.params.as_slice() else {
        return false;
    };
    let compact = function_body(source, function)
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    compact.contains(&format!("{array}.push({array}.shift())"))
        && compact.contains(&format!("return{array}"))
        && compact.contains(&format!("<{count}"))
}

fn parse_number(text: &str) -> Option<i64> {
    let text = text.trim();
    if let Some(value) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        i64::from_str_radix(value, 16).ok()
    } else {
        text.parse().ok()
    }
}

fn value_text(value: &Value) -> Option<String> {
    value.render()
}

fn substitute_simple_array_literals(text: &str, arrays: &HashMap<String, Vec<Value>>) -> String {
    let mut out = text.to_string();
    for (name, values) in arrays {
        let Ok(pattern) = Regex::new(&format!(r"\b{}\s*\[\s*({NUM})\s*\]", regex::escape(name)))
        else {
            continue;
        };
        out = pattern
            .replace_all(&out, |captures: &Captures<'_>| {
                let Some(index) = captures
                    .get(1)
                    .and_then(|value| parse_number(value.as_str()))
                else {
                    return captures[0].to_string();
                };
                let Ok(index) = usize::try_from(index) else {
                    return captures[0].to_string();
                };
                values
                    .get(index)
                    .and_then(value_text)
                    .unwrap_or_else(|| captures[0].to_string())
            })
            .into_owned();
    }
    out
}

fn base91_signature_matches(text: &str) -> bool {
    let compact = text
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    SIGNATURE.iter().all(|fragment| compact.contains(fragment))
}

fn normalize_affine_signs(text: &str) -> String {
    let plus_minus = Regex::new(&format!(r"\+\s*-\s*({NUM})")).ok();
    let minus_minus = Regex::new(&format!(r"-\s*-\s*({NUM})")).ok();
    let out = plus_minus.as_ref().map_or_else(
        || text.to_string(),
        |re| re.replace_all(text, "-$1").into_owned(),
    );
    minus_minus
        .as_ref()
        .map_or(out.clone(), |re| re.replace_all(&out, "+$1").into_owned())
}

fn parse_affine_ref(text: &str) -> Option<(String, String, i64)> {
    let pattern = Regex::new(&format!(
        r"^\s*({IDENT})\s*\[\s*({IDENT})\s*(?:([+-])\s*({NUM}))?\s*\]\s*$"
    ))
    .ok()?;
    let captures = pattern.captures(text)?;
    let mut offset = captures
        .get(4)
        .and_then(|value| parse_number(value.as_str()))
        .unwrap_or(0);
    if captures.get(3).is_some_and(|value| value.as_str() == "-") {
        offset = -offset;
    }
    Some((captures[1].to_string(), captures[2].to_string(), offset))
}

fn substitute_affine_array_state(
    text: &str,
    array_name: &str,
    state_name: &str,
    base: i64,
    values: &[Value],
) -> String {
    let Ok(pattern) = Regex::new(&format!(
        r"\b{}\s*\[\s*{}\s*(?:([+-])\s*({NUM}))?\s*\]",
        regex::escape(array_name),
        regex::escape(state_name),
    )) else {
        return text.to_string();
    };
    pattern
        .replace_all(text, |captures: &Captures<'_>| {
            let mut offset = captures
                .get(2)
                .and_then(|value| parse_number(value.as_str()))
                .unwrap_or(0);
            if captures.get(1).is_some_and(|value| value.as_str() == "-") {
                offset = -offset;
            }
            let Some(index) = base
                .checked_add(offset)
                .and_then(|value| usize::try_from(value).ok())
            else {
                return captures[0].to_string();
            };
            values
                .get(index)
                .and_then(value_text)
                .unwrap_or_else(|| captures[0].to_string())
        })
        .into_owned()
}

fn semantic_affine_base91_signature_matches(
    text: &str,
    arrays: &HashMap<String, Vec<Value>>,
) -> bool {
    let normalized = normalize_affine_signs(text);
    let partial = substitute_simple_array_literals(&normalized, arrays);
    let affine = format!(r"{IDENT}\s*\[\s*{IDENT}\s*(?:[+-]\s*{NUM})?\s*\]");
    let mut constraints: HashMap<(String, String), HashSet<i64>> = HashMap::new();

    let mut constrain = |reference: &str, expected: i64| -> bool {
        let Some((array, state, offset)) = parse_affine_ref(reference) else {
            return false;
        };
        let Some(values) = arrays.get(&array) else {
            return false;
        };
        let candidates = values
            .iter()
            .enumerate()
            .filter_map(|(index, value)| {
                let expected = u32::try_from(expected).ok().map(f64::from);
                let matches = expected.is_some_and(|expected| {
                    value.number().is_some_and(|number| number == expected)
                });
                matches
                    .then(|| i64::try_from(index).ok()?.checked_sub(offset))
                    .flatten()
            })
            .collect::<HashSet<_>>();
        if candidates.is_empty() {
            return false;
        }
        let key = (array, state);
        let entry = constraints.entry(key).or_insert_with(|| candidates.clone());
        entry.retain(|candidate| candidates.contains(candidate));
        !entry.is_empty()
    };

    if let Ok(pattern) = Regex::new(&format!(
        r"&\s*({affine})\s*\)\s*>\s*88\s*\?\s*({affine})\s*:\s*14"
    )) {
        if let Some(captures) = pattern.captures(&partial) {
            if !constrain(&captures[1], 8191) || !constrain(&captures[2], 13) {
                return false;
            }
        }
    }
    if let Ok(pattern) = Regex::new(&format!(r"\.push\s*\([^()]*&\s*({affine})\s*\)")) {
        for captures in pattern.captures_iter(&partial) {
            if !constrain(&captures[1], 255) {
                return false;
            }
        }
    }
    if let Ok(pattern) = Regex::new(&format!(r">>=\s*({affine})")) {
        for captures in pattern.captures_iter(&partial) {
            if !constrain(&captures[1], 8) {
                return false;
            }
        }
    }
    if let Ok(pattern) = Regex::new(&format!(r"while\s*\([^)]*>\s*({affine})\s*\)")) {
        for captures in pattern.captures_iter(&partial) {
            if !constrain(&captures[1], 7) {
                return false;
            }
        }
    }
    if constraints.is_empty() || constraints.values().any(|values| values.len() != 1) {
        return false;
    }
    let mut resolved = normalized;
    for ((array, state), candidates) in constraints {
        let Some(base) = candidates.iter().next().copied() else {
            return false;
        };
        let Some(values) = arrays.get(&array) else {
            return false;
        };
        resolved = substitute_affine_array_state(&resolved, &array, &state, base, values);
    }
    base91_signature_matches(&substitute_simple_array_literals(&resolved, arrays))
}

fn affine_base91_signature_matches(body: &str, arrays: &HashMap<String, Vec<Value>>) -> bool {
    let Some(index_of) = body.find(".indexOf") else {
        return false;
    };
    let start = index_of.saturating_sub(900);
    let end = (index_of + 1800).min(body.len());
    let Some(window) = body.get(start..end) else {
        return false;
    };
    semantic_affine_base91_signature_matches(window, arrays)
}

fn looks_like_base91_decoder(
    body: &str,
    alphabet: &str,
    arrays: &HashMap<String, Vec<Value>>,
) -> bool {
    if alphabet.chars().count() != 91 || alphabet.chars().collect::<HashSet<_>>().len() != 91 {
        return false;
    }
    let resolved = substitute_simple_array_literals(body, arrays);
    base91_signature_matches(&resolved) || affine_base91_signature_matches(body, arrays)
}

#[derive(Debug, Clone)]
struct StringValue {
    span: Span,
    value: String,
}

#[derive(Default)]
struct StringValueCollector {
    values: Vec<StringValue>,
}

impl<'a> Visit<'a> for StringValueCollector {
    fn visit_string_literal(&mut self, literal: &oxc_ast::ast::StringLiteral<'a>) {
        if let Some(value) = string_literal_value(literal) {
            self.values.push(StringValue {
                span: literal.span,
                value,
            });
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct WrapperLink {
    scope: ScopeId,
    provider_symbol: SymbolId,
    transform_symbol: SymbolId,
}

struct WrapperLinkCollector<'s> {
    scoping: &'s Scoping,
    links: Vec<WrapperLink>,
}

impl<'a> Visit<'a> for WrapperLinkCollector<'_> {
    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        if !call.optional && !call.arguments.is_empty() {
            if let Expression::Identifier(transform) = &call.callee {
                if let Some(Argument::ComputedMemberExpression(member)) = call.arguments.first() {
                    if !member.optional {
                        if let Expression::Identifier(provider) = &member.object {
                            let transform_reference = transform.reference_id.get();
                            let transform_symbol = transform_reference.and_then(|reference| {
                                statically_resolved_symbol(self.scoping, reference)
                            });
                            let scope = transform_reference
                                .map(|reference| self.scoping.get_reference(reference).scope_id());
                            let provider_symbol =
                                provider.reference_id.get().and_then(|reference| {
                                    statically_resolved_symbol(self.scoping, reference)
                                });
                            if let (Some(transform_symbol), Some(provider_symbol), Some(scope)) =
                                (transform_symbol, provider_symbol, scope)
                            {
                                self.links.push(WrapperLink {
                                    scope,
                                    provider_symbol,
                                    transform_symbol,
                                });
                            }
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

#[derive(Debug, Clone)]
struct DecoderCandidate {
    decoder: String,
    decoder_symbol: SymbolId,
    provider: ProviderTable,
    transform: String,
    alphabet: String,
    declaration_start: usize,
    scope_start: usize,
    scope_end: usize,
}

struct DecoderDiscoveryContext<'a> {
    source: &'a str,
    scoping: &'a Scoping,
    scope_spans: &'a HashMap<ScopeId, Span>,
    functions: &'a [FunctionInfo],
    calls: &'a HashMap<ScopeId, HashSet<SymbolId>>,
    wrapper_links: &'a [WrapperLink],
    string_values: &'a [StringValue],
    arrays: &'a HashMap<String, Vec<Value>>,
}

fn discover_decoders(
    context: &DecoderDiscoveryContext<'_>,
    providers: &[ProviderTable],
) -> Vec<DecoderCandidate> {
    let mut out = Vec::new();
    for provider in providers {
        let Some(_rotator) = context.functions.iter().find(|function| {
            function.symbol == provider.rotator_symbol && rotator_matches(context.source, function)
        }) else {
            continue;
        };
        for decoder in context.functions {
            let declaration_start = decoder.span.start as usize;
            let Some((scope_start, scope_end)) = function_scope_span(
                context.scoping,
                context.scope_spans,
                decoder.owner_scope,
                context.source.len(),
            ) else {
                continue;
            };
            if decoder.owner_scope == provider.owner_scope {
                // The canonical generated scaffold hoists same-scope decoder
                // helpers before the rotated table is initialized. A helper
                // declared after that initialization is not attributed to the
                // table merely because it happens to share its binding.
                if declaration_start >= provider.assignment_start {
                    continue;
                }
            } else {
                if !scope_is_descendant_of(
                    context.scoping,
                    decoder.owner_scope,
                    provider.owner_scope,
                ) || scope_start <= provider.assignment_end
                {
                    continue;
                }
            }
            let body = function_body(context.source, decoder);
            if body.len() > 4096 || !body.contains("typeof") || !body.contains("return") {
                continue;
            }
            let implementation_scopes = reachable_nested_function_scopes(
                context.scoping,
                decoder,
                context.functions,
                context.calls,
            );
            let transforms = context
                .wrapper_links
                .iter()
                .filter(|link| {
                    link.provider_symbol == provider.provider_symbol
                        && implementation_scopes
                            .contains(&owning_function_scope(context.scoping, link.scope))
                })
                .map(|link| link.transform_symbol)
                .collect::<HashSet<_>>();
            if transforms.len() != 1 {
                continue;
            }
            let Some(transform_symbol) = transforms.iter().next().copied() else {
                continue;
            };
            let Some(transform_fn) = context.functions.iter().find(|function| {
                function.symbol == transform_symbol
                    && function.span.start < decoder.span.start
                    && function.owner_scope == decoder.owner_scope
            }) else {
                continue;
            };
            let transform_body = function_body(context.source, transform_fn);
            let Some(alphabet) = context
                .string_values
                .iter()
                .filter(|literal| {
                    transform_fn.span.start <= literal.span.start
                        && literal.span.end <= transform_fn.span.end
                })
                .map(|literal| literal.value.clone())
                .find(|candidate| {
                    looks_like_base91_decoder(transform_body, candidate, context.arrays)
                })
            else {
                continue;
            };
            let mut rotated = provider.clone();
            rotated.values.rotate_left(rotated.rotation);
            out.push(DecoderCandidate {
                decoder: decoder.name.clone(),
                decoder_symbol: decoder.symbol,
                provider: rotated,
                transform: transform_fn.name.clone(),
                alphabet,
                declaration_start,
                scope_start,
                scope_end,
            });
        }
    }
    out.sort_by_key(|decoder| {
        (
            decoder.declaration_start,
            decoder.scope_start,
            decoder.decoder.clone(),
        )
    });
    out.dedup_by(|left, right| {
        left.declaration_start == right.declaration_start
            && left.scope_start == right.scope_start
            && left.decoder_symbol == right.decoder_symbol
            && left.provider.provider_symbol == right.provider.provider_symbol
    });
    out
}

struct Base91CallCollector<'s, 'd> {
    scoping: &'s Scoping,
    decoders: &'d HashMap<SymbolId, &'d DecoderCandidate>,
    arrays: &'d HashMap<SymbolId, Vec<Value>>,
    replacements: Vec<Replacement>,
    counts: HashMap<SymbolId, usize>,
}

impl Base91CallCollector<'_, '_> {
    fn raw_argument(&self, argument: &Argument<'_>) -> Option<usize> {
        match argument {
            Argument::NumericLiteral(value) => crate::exact_usize(value.value),
            Argument::ComputedMemberExpression(member) if !member.optional => {
                let Expression::Identifier(array) = &member.object else {
                    return None;
                };
                let array_symbol = array
                    .reference_id
                    .get()
                    .and_then(|reference| statically_resolved_symbol(self.scoping, reference))?;
                let values = self.arrays.get(&array_symbol)?;
                let index = crate::value_eval::eval(&member.expression)
                    .and_then(|value| value.number())
                    .and_then(crate::exact_usize)?;
                values
                    .get(index)
                    .and_then(Value::number)
                    .and_then(crate::exact_usize)
            }
            _ => None,
        }
    }
}

impl<'a> Visit<'a> for Base91CallCollector<'_, '_> {
    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        if !call.optional && call.arguments.len() == 1 && !call.arguments[0].is_spread() {
            if let Expression::Identifier(callee) = &call.callee {
                let decoder_symbol = callee
                    .reference_id
                    .get()
                    .and_then(|reference| statically_resolved_symbol(self.scoping, reference));
                if let Some(decoder) = decoder_symbol.and_then(|symbol| self.decoders.get(&symbol))
                {
                    if let Some(raw) = self.raw_argument(&call.arguments[0]) {
                        if let Some(encoded) = decoder.provider.values.get(raw) {
                            if let Some(decoded) = decode_base91_ascii(encoded, &decoder.alphabet) {
                                if let Ok(text) = serde_json::to_string(&decoded) {
                                    self.replacements.push(Replacement {
                                        start: call.span.start as usize,
                                        end: call.span.end as usize,
                                        text,
                                        kind: "base91_decoder_call",
                                        arithmetic_state_proof: None,
                                    });
                                    *self.counts.entry(decoder.decoder_symbol).or_default() += 1;
                                    return;
                                }
                            }
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn expose_static_strings_allow_with(
    source: &str,
    source_type: SourceType,
) -> Option<(String, BTreeMap<String, usize>)> {
    let mut current = source.to_string();
    let mut total = BTreeMap::<String, usize>::new();
    for iteration in 1..=8 {
        let allocator = Allocator::default();
        let program = parse_as(&allocator, &current, source_type)?;
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if !semantic_ret.diagnostics.is_empty() {
            return None;
        }
        let replacements = static_string_exposure_pass(&program, semantic_ret.semantic.scoping());
        if replacements.is_empty() {
            break;
        }
        let mut counts = Counts::default();
        let next = apply(
            &current,
            replacements,
            &mut counts,
            &mut Vec::new(),
            iteration,
        )?;
        for (kind, count) in counts.into_inner() {
            *total.entry(kind).or_default() += count;
        }
        if next == current {
            break;
        }
        current = next;
    }
    Some((current, total))
}

#[must_use]
pub fn recover_base91_strings_with_source_mode(
    source: &str,
    max_iterations: usize,
    source_mode: SafeSourceMode,
) -> Option<Base91RecoveryResult> {
    let source_type = parse_semantically_allow_with(source, source_mode)?;
    let mut current = source.to_string();
    let mut proofs = Vec::new();
    let mut iterations = Vec::new();
    let mut transforms = BTreeMap::<String, usize>::new();
    let mut total_replacements = 0usize;

    for iteration in 1..=max_iterations.min(4) {
        let allocator = Allocator::default();
        let program = parse_as(&allocator, &current, source_type)?;
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&program);
        if !semantic_ret.diagnostics.is_empty() {
            return None;
        }
        let mut string_collector = StringValueCollector::default();
        string_collector.visit_program(&program);
        let preflight = string_collector.values.iter().any(|literal| {
            literal.value.chars().count() == 91
                && literal.value.chars().collect::<HashSet<_>>().len() == 91
        });
        if !preflight {
            iterations.push(Base91Iteration {
                iteration,
                preflight_skipped: true,
                decoder_calls: 0,
                immutable_string_table_replacements: 0,
                literal_concat_folds: 0,
            });
            break;
        }
        let scoping = semantic_ret.semantic.scoping();
        let mut function_collector = FunctionCollector {
            scoping,
            functions: Vec::new(),
            scope_spans: HashMap::new(),
        };
        function_collector.visit_program(&program);
        let mut call_collector = FunctionCallCollector {
            scoping,
            calls: HashMap::new(),
        };
        call_collector.visit_program(&program);
        let mut provider_collector = ProviderCollector {
            scoping,
            providers: Vec::new(),
        };
        provider_collector.visit_program(&program);
        let mut array_collector = SimpleArrayCollector::default();
        array_collector.visit_program(&program);
        let mut wrapper_collector = WrapperLinkCollector {
            scoping,
            links: Vec::new(),
        };
        wrapper_collector.visit_program(&program);
        let discovery = DecoderDiscoveryContext {
            source: &current,
            scoping,
            scope_spans: &function_collector.scope_spans,
            functions: &function_collector.functions,
            calls: &call_collector.calls,
            wrapper_links: &wrapper_collector.links,
            string_values: &string_collector.values,
            arrays: &array_collector.arrays,
        };
        let decoders = discover_decoders(&discovery, &provider_collector.providers);
        let mut decoder_map = HashMap::new();
        let mut ambiguous = HashSet::new();
        for decoder in &decoders {
            if decoder_map
                .insert(decoder.decoder_symbol, decoder)
                .is_some()
            {
                ambiguous.insert(decoder.decoder_symbol);
            }
        }
        for symbol in ambiguous {
            decoder_map.remove(&symbol);
        }
        let mut call_collector = Base91CallCollector {
            scoping,
            decoders: &decoder_map,
            arrays: &array_collector.by_symbol,
            replacements: Vec::new(),
            counts: HashMap::new(),
        };
        call_collector.visit_program(&program);
        let mut iteration_proofs = Vec::new();
        for decoder in &decoders {
            let count = call_collector
                .counts
                .get(&decoder.decoder_symbol)
                .copied()
                .unwrap_or(0);
            if count > 0 || iteration == 1 {
                iteration_proofs.push(Base91DecoderProof {
                    decoder: decoder.decoder.clone(),
                    provider: decoder.provider.provider.clone(),
                    transform: decoder.transform.clone(),
                    rotation: decoder.provider.rotation,
                    table_entries: decoder.provider.values.len(),
                    scope_start: decoder.scope_start,
                    scope_end: decoder.scope_end,
                    declaration_start: decoder.declaration_start,
                    replacements: count,
                    iteration,
                });
            }
        }
        let replacements = call_collector.replacements;
        let mut counts = Counts::default();
        let next = if replacements.is_empty() {
            current.clone()
        } else {
            apply(
                &current,
                replacements,
                &mut counts,
                &mut Vec::new(),
                iteration,
            )?
        };
        let decoder_calls = counts
            .into_inner()
            .get("base91_decoder_call")
            .copied()
            .unwrap_or(0);
        let (next, exposure) = expose_static_strings_allow_with(&next, source_type)?;
        let table_reads = exposure
            .get("static_string_table_lookup")
            .copied()
            .unwrap_or(0);
        let concat_folds = exposure.get("literal_string_concat").copied().unwrap_or(0);
        for (kind, count) in exposure {
            *transforms.entry(kind).or_default() += count;
        }
        if decoder_calls > 0 {
            *transforms.entry("base91_decoder_call".into()).or_default() += decoder_calls;
        }
        total_replacements += decoder_calls + table_reads + concat_folds;
        proofs.extend(iteration_proofs);
        iterations.push(Base91Iteration {
            iteration,
            preflight_skipped: false,
            decoder_calls,
            immutable_string_table_replacements: table_reads,
            literal_concat_folds: concat_folds,
        });
        if next == current {
            break;
        }
        current = next;
    }

    Some(Base91RecoveryResult {
        source: current,
        decoders: proofs,
        iterations,
        replacements: total_replacements,
        transforms,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn affine_signature_requires_unique_expected_constants() {
        let mut values = vec![Value::Undefined; 24];
        for (index, value) in [
            (2, 8.0),
            (3, 255.0),
            (14, 7.0),
            (17, 91.0),
            (18, 8191.0),
            (19, 88.0),
            (20, 13.0),
            (21, 14.0),
        ] {
            values[index] = Value::Number(value);
        }
        let arrays = HashMap::from([("c".to_string(), values.clone())]);
        let window = "alphabet.indexOf(ch); pending += index * 91; bits += (pending & c[s0 + 18]) > 88 ? c[s0 + 20] : 14; out.push(acc & c[s1 + 3]); acc >>= c[s2 + 2]; bits -= 8; pending = -1; while (bits > c[s2 + 14]); if (pending > -1) out.push(acc & 255);";
        assert!(semantic_affine_base91_signature_matches(window, &arrays));
        values[18] = Value::Number(8190.0);
        let broken = HashMap::from([("c".to_string(), values)]);
        assert!(!semantic_affine_base91_signature_matches(window, &broken));
    }
}
