//! Exact lexical-symbol property aliases for browseable source-tree views.
//!
//! A string assignment is not proof of a constant property key: its binding
//! may be overwritten along a conditional path. Instead of replacing a live
//! computed property, emit a *separate* annotated analysis view displaying
//! the actual literal candidates, dynamic writes, and their known guards.
//! Original and deobfuscated executable source files remain unchanged.
use anyhow::{ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    AssignmentExpression, AssignmentTarget, BindingPattern, ComputedMemberExpression, Expression,
    IfStatement, LogicalExpression, SimpleAssignmentTarget, UpdateExpression, VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType};
use oxc_syntax::symbol::SymbolId;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Serialize)]
pub struct AliasWrite {
    pub value: String,
    pub literal: Option<String>,
    pub when: Option<String>,
    pub offset: u32,
}

#[derive(Clone, Debug, Serialize)]
pub struct PropertyAlias {
    pub binding: String,
    pub reads: usize,
    pub writes: Vec<AliasWrite>,
    pub other_writes_possible: bool,
}

#[derive(Debug)]
pub struct AnnotatedAliases {
    pub source: String,
    pub aliases: Vec<PropertyAlias>,
    pub annotated_reads: usize,
}

struct Reader<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    guard: Vec<String>,
    writes: BTreeMap<SymbolId, Vec<AliasWrite>>,
    unmodeled_writes: BTreeSet<SymbolId>,
    property_reads: BTreeMap<SymbolId, Vec<u32>>,
}

/// A comma expression has the value of its last operand on every normal
/// completion, even if earlier expressions have effects or throw. This is
/// especially useful when an obfuscator embeds alias initialization in a
/// long effectful sequence. We record the final literal but NEVER discard
/// the prefixes or alter the original executable code.
fn final_literal_string(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::ParenthesizedExpression(paren) => final_literal_string(&paren.expression),
        Expression::SequenceExpression(sequence) => {
            final_literal_string(sequence.expressions.last()?)
        }
        Expression::StringLiteral(literal) => Some(literal.value.display().to_string()),
        _ => None,
    }
}

impl Reader<'_> {
    fn text(&self, start: u32, end: u32) -> Option<&str> {
        self.source.get(start as usize..end as usize)
    }

    fn guard_text(&self) -> Option<String> {
        (!self.guard.is_empty()).then(|| self.guard.join(" and "))
    }

    fn record_write(&mut self, symbol: SymbolId, expression: &Expression<'_>, offset: u32) {
        let mut expression = expression;
        while let Expression::ParenthesizedExpression(paren) = expression {
            expression = &paren.expression;
        }
        let literal = final_literal_string(expression);
        let value = self
            .text(expression.span().start, expression.span().end)
            .map(str::to_owned);
        let when = self.guard_text();
        if let Some(value) = value {
            self.writes.entry(symbol).or_default().push(AliasWrite {
                value,
                literal,
                when,
                offset,
            });
        }
    }
}

impl<'a> Visit<'a> for Reader<'_> {
    fn visit_assignment_expression(&mut self, it: &AssignmentExpression<'a>) {
        if let AssignmentTarget::AssignmentTargetIdentifier(id) = &it.left {
            if let Some(symbol) = id
                .reference_id
                .get()
                .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
            {
                if it.operator.as_str() == "=" {
                    self.record_write(symbol, &it.right, it.span.start);
                } else {
                    // Compound and short-circuit assignments do not merely
                    // assign their RHS expression value.
                    self.unmodeled_writes.insert(symbol);
                }
            }
        }
        walk::walk_assignment_expression(self, it);
    }

    fn visit_update_expression(&mut self, it: &UpdateExpression<'a>) {
        if let SimpleAssignmentTarget::AssignmentTargetIdentifier(id) = &it.argument {
            if let Some(symbol) = id
                .reference_id
                .get()
                .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
            {
                self.unmodeled_writes.insert(symbol);
            }
        }
        walk::walk_update_expression(self, it);
    }

    fn visit_variable_declarator(&mut self, it: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(id), Some(initializer)) = (&it.id, &it.init) {
            if let Some(symbol) = id.symbol_id.get() {
                self.record_write(symbol, initializer, it.span.start);
            }
        }
        walk::walk_variable_declarator(self, it);
    }

    fn visit_if_statement(&mut self, it: &IfStatement<'a>) {
        self.visit_expression(&it.test);
        let text = self
            .text(it.test.span().start, it.test.span().end)
            .filter(|text| text.len() <= 120)
            .map(str::to_owned);
        if let Some(text) = &text {
            self.guard.push(format!("({text}) truthy"));
        }
        self.visit_statement(&it.consequent);
        if text.is_some() {
            self.guard.pop();
        }
        if let Some(alternate) = &it.alternate {
            if let Some(text) = &text {
                self.guard.push(format!("({text}) falsy"));
            }
            self.visit_statement(alternate);
            if text.is_some() {
                self.guard.pop();
            }
        }
    }

    fn visit_logical_expression(&mut self, it: &LogicalExpression<'a>) {
        self.visit_expression(&it.left);
        let operator = match it.operator.as_str() {
            "&&" => "truthy",
            "||" => "falsy",
            "??" => "nullish",
            _ => "conditional",
        };
        let guard = self
            .text(it.left.span().start, it.left.span().end)
            .map(|text| {
                if text.len() <= 120 {
                    format!("({text}) {operator}")
                } else {
                    // Still record the real conditional dependency even when
                    // the controlling expression is a huge nested sequence.
                    // Do not imply it was unconditional just because its AST
                    // spelling exceeds the inline display budget.
                    let tail = text.chars().rev().take(90).collect::<String>();
                    let tail = tail.chars().rev().collect::<String>();
                    format!(
                        "(…{tail}) {operator} [left at byte {}]",
                        it.left.span().start
                    )
                }
            });
        let added = guard.is_some();
        if let Some(guard) = guard {
            self.guard.push(guard);
        }
        self.visit_expression(&it.right);
        if added {
            self.guard.pop();
        }
    }

    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        let mut key = &it.expression;
        while let Expression::ParenthesizedExpression(paren) = key {
            key = &paren.expression;
        }
        if let Expression::Identifier(id) = key {
            if let Some(symbol) = id
                .reference_id
                .get()
                .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
            {
                self.property_reads
                    .entry(symbol)
                    .or_default()
                    .push(id.span.end);
            }
        }
        walk::walk_computed_member_expression(self, it);
    }
}

fn comment_text(alias: &PropertyAlias) -> String {
    let literals = alias
        .writes
        .iter()
        .filter_map(|write| write.literal.as_ref())
        .collect::<BTreeSet<_>>();
    let mut parts = literals
        .into_iter()
        .map(|text| format!("{text:?}"))
        .collect::<Vec<_>>();
    for write in alias.writes.iter().filter(|write| write.literal.is_none()) {
        let dynamic = write.when.as_ref().map_or_else(
            || format!("other value {}", write.value),
            |condition| format!("{} when {condition}", write.value),
        );
        parts.push(dynamic);
    }
    if alias.other_writes_possible {
        parts.push("other writes possible".into());
    }
    // Comments must not allow input to end a JS comment. Use an abbreviated
    // source description when extremely long, while the manifest holds detail.
    let summary = parts.join("; ").replace("*/", "* /");
    let shortened = summary
        .replace(['\n', '\r'], " ")
        .chars()
        .take(180)
        .collect::<String>();
    format!(" /* property alias: {shortened} */")
}

/// Annotate only references resolved to the *same original AST SymbolId*.
/// Shadowed aliases and unrelated names are never joined by spelling.
pub fn explain_property_aliases(source: &str) -> Result<Option<AnnotatedAliases>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(
        parsed.is_clean(),
        "property-alias input is not valid JavaScript"
    );
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantic.semantic.scoping();
    let mut reader = Reader {
        source,
        scoping,
        guard: Vec::new(),
        writes: BTreeMap::new(),
        unmodeled_writes: BTreeSet::new(),
        property_reads: BTreeMap::new(),
    };
    reader.visit_program(&parsed.program);
    let mut insertions = Vec::new();
    let mut aliases = Vec::new();
    for (symbol, uses) in reader.property_reads {
        let Some(writes) = reader.writes.get(&symbol) else {
            continue;
        };
        if !writes.iter().any(|write| write.literal.is_some()) {
            continue;
        }
        let tracked_assignments = writes.len();
        let all_writes = scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .filter(|reference| scoping.get_reference(**reference).is_write())
            .count();
        let alias = PropertyAlias {
            binding: scoping.symbol_name(symbol).to_owned(),
            reads: uses.len(),
            writes: writes.clone(),
            other_writes_possible: reader.unmodeled_writes.contains(&symbol)
                || all_writes > tracked_assignments,
        };
        let comment = comment_text(&alias);
        for end in uses {
            insertions.push((end as usize, comment.clone()));
        }
        aliases.push(alias);
    }
    if insertions.is_empty() {
        return Ok(None);
    }
    insertions.sort_unstable_by_key(|(offset, _)| std::cmp::Reverse(*offset));
    let mut explained = source.to_owned();
    for (offset, comment) in &insertions {
        explained.insert_str(*offset, comment);
    }
    Ok(Some(AnnotatedAliases {
        source: explained,
        aliases,
        annotated_reads: insertions.len(),
    }))
}

#[cfg(test)]
mod tests {
    use super::explain_property_aliases;

    #[test]
    fn annotates_conditional_string_alias_but_keeps_property_access_executable(
    ) -> anyhow::Result<()> {
        let source = r#"function start(H,T,JM){
          T='push';JM='length';
          H.length<2 && (T=H);
          if(H.length<2){JM=H;}
          const closure=()=>{const out=[];out[T](1);return out[JM]};
          return closure();
        }"#;
        let result = explain_property_aliases(source)?
            .ok_or_else(|| anyhow::anyhow!("missing lexical aliases"))?;
        assert_eq!(result.annotated_reads, 2);
        assert!(result
            .source
            .contains("out[T /* property alias: \"push\"; H when"));
        assert!(result
            .source
            .contains("out[JM /* property alias: \"length\""));
        assert!(result.source.contains("H.length<2"));
        let length = result.aliases.iter().find(|a| a.binding == "JM");
        assert!(length.is_some_and(|a| a.writes.iter().any(|w| w
            .when
            .as_deref()
            .is_some_and(|when| when.contains("H.length<2")))));
        assert_eq!(result.aliases.len(), 2);
        Ok(())
    }

    #[test]
    fn finds_final_string_from_effectful_comma_initializer_without_discarding_prefix(
    ) -> anyhow::Result<()> {
        let source = r#"function f(obj,H,alias){alias=(touch(),H.length,"length");H.length<2&&(alias=H);return obj[alias];}"#;
        let explained = explain_property_aliases(source)?
            .ok_or_else(|| anyhow::anyhow!("missing sequence alias"))?;
        assert_eq!(
            explained.aliases[0].writes[0].literal.as_deref(),
            Some("length")
        );
        assert!(explained.source.contains("touch()"));
        assert!(explained.source.contains("obj[alias /* property alias:"));
        Ok(())
    }

    #[test]
    fn tracks_declaration_initializer_and_flags_compound_writes() -> anyhow::Result<()> {
        let source = "function f(obj){let key=('length');key+='suffix';return obj[(key)];}";
        let result = explain_property_aliases(source)?
            .ok_or_else(|| anyhow::anyhow!("expected declared property alias"))?;
        assert_eq!(result.annotated_reads, 1);
        assert_eq!(
            result.aliases[0].writes[0].literal.as_deref(),
            Some("length")
        );
        assert!(result.aliases[0].other_writes_possible);
        assert!(result.source.contains("key /* property alias:"));
        Ok(())
    }

    #[test]
    fn distinguishes_shadowed_binding_and_does_not_annotate_unproven_alias() -> anyhow::Result<()> {
        let source = r#"function f(T,obj){T='push';const a=obj[T];
            function g(T){return obj[T]};return a;}"#;
        let result = explain_property_aliases(source)?
            .ok_or_else(|| anyhow::anyhow!("missing lexical alias"))?;
        assert_eq!(result.annotated_reads, 1);
        assert!(result.source.contains("obj[T /* property alias:"));
        assert!(result.source.contains("return obj[T]"));
        assert!(explain_property_aliases("function f(T,obj){return obj[T];}")?.is_none());
        Ok(())
    }
}

/// A captured function can be linked to original lexical symbols only after
/// its source-span and source-hash provenance are checked against the *raw*
/// original program. Pretty-printed code has different offsets and must not
/// silently serve as the provenance source.
#[derive(Clone, Debug, Serialize)]
pub struct CapturedAlias {
    pub binding: String,
    pub declaration: [u32; 2],
    pub original_reads: usize,
    pub writes: Vec<AliasWrite>,
    pub other_writes_possible: bool,
}

#[derive(Debug)]
pub struct CapturedAliasView {
    pub input_path: String,
    pub original_span: [u32; 2],
    pub annotated_source: String,
    pub annotated_reads: usize,
    pub aliases: Vec<CapturedAlias>,
}

#[derive(Default)]
struct OriginalFunctions(BTreeSet<(u32, u32)>);

impl<'a> Visit<'a> for OriginalFunctions {
    fn visit_function(
        &mut self,
        function: &oxc_ast::ast::Function<'a>,
        flags: oxc_syntax::scope::ScopeFlags,
    ) {
        self.0.insert((function.span.start, function.span.end));
        walk::walk_function(self, function, flags);
    }

    fn visit_arrow_function_expression(
        &mut self,
        function: &oxc_ast::ast::ArrowFunctionExpression<'a>,
    ) {
        self.0.insert((function.span.start, function.span.end));
        walk::walk_arrow_function_expression(self, function);
    }
}

fn capture_origin(source: &str) -> Option<(String, [u32; 2])> {
    let line = source.lines().next()?;
    let hash =
        line.strip_prefix("// Readable, non-devirtualized provenance view. Original SHA-256: ")?;
    if hash.len() != 64 || !hash.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let line = source.lines().nth(1)?.trim();
    let (_, rest) = line.split_once("Original bytes: ")?;
    let (start, rest) = rest.split_once("..")?;
    let (end, _) = rest.split_once('.')?;
    Some((hash.to_owned(), [start.parse().ok()?, end.parse().ok()?]))
}

struct CapturedReads<'s> {
    scoping: &'s Scoping,
    candidates: &'s BTreeMap<String, CapturedAlias>,
    edits: Vec<(usize, String)>,
}

impl<'a> Visit<'a> for CapturedReads<'_> {
    fn visit_computed_member_expression(&mut self, it: &ComputedMemberExpression<'a>) {
        let mut expr = &it.expression;
        while let Expression::ParenthesizedExpression(paren) = expr {
            expr = &paren.expression;
        }
        if let Expression::Identifier(id) = expr {
            let unresolved = id.reference_id.get().is_some_and(|reference| {
                self.scoping.get_reference(reference).symbol_id().is_none()
            });
            if unresolved {
                if let Some(alias) = self.candidates.get(id.name.as_str()) {
                    let property = PropertyAlias {
                        binding: alias.binding.clone(),
                        reads: alias.original_reads,
                        writes: alias.writes.clone(),
                        other_writes_possible: alias.other_writes_possible,
                    };
                    let origin = alias.declaration[0];
                    let comment = comment_text(&property).replacen(
                        "property alias:",
                        &format!("property alias from original declaration byte {origin}:"),
                        1,
                    );
                    self.edits.push((id.span.end as usize, comment));
                }
            }
        }
        walk::walk_computed_member_expression(self, it);
    }
}

/// Produce handler-specific *browsing* views, not executable replacements.
/// The source hash, original function spans and external symbols are all
/// checked in the raw source AST. A same-named reference is annotated in a
/// transformed handler only if it remains unresolved *and* the original
/// capture had one uniquely resolved lexical symbol for that property name.
pub fn explain_captured_handler_origins(
    raw_original: &str,
    handlers: &[(String, String)],
) -> Result<Vec<CapturedAliasView>> {
    use crate::sha256_hex;
    let expected_hash = sha256_hex(raw_original.as_bytes());
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, raw_original, SourceType::unambiguous());
    ensure!(parsed.is_clean(), "raw origin is not valid JavaScript");
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantic.semantic.scoping();
    let mut functions = OriginalFunctions::default();
    functions.visit_program(&parsed.program);
    let mut reader = Reader {
        source: raw_original,
        scoping,
        guard: Vec::new(),
        writes: BTreeMap::new(),
        unmodeled_writes: BTreeSet::new(),
        property_reads: BTreeMap::new(),
    };
    reader.visit_program(&parsed.program);
    let mut output = Vec::new();
    for (path, source) in handlers {
        let Some((hash, span)) = capture_origin(source) else {
            continue;
        };
        ensure!(
            hash == expected_hash,
            "handler {path} has a different original source SHA-256"
        );
        ensure!(
            functions.0.contains(&(span[0], span[1])),
            "handler {path} original byte span is not an AST function"
        );
        let mut by_name: BTreeMap<String, (SymbolId, CapturedAlias)> = BTreeMap::new();
        let mut ambiguous = BTreeSet::new();
        for (symbol, reads) in &reader.property_reads {
            let count = reads
                .iter()
                .filter(|&&end| span[0] <= end && end <= span[1])
                .count();
            if count == 0 {
                continue;
            }
            let declaration = scoping.symbol_span(*symbol);
            if span[0] <= declaration.start && declaration.end <= span[1] {
                continue;
            }
            let Some(writes) = reader.writes.get(symbol) else {
                continue;
            };
            if !writes.iter().any(|write| write.literal.is_some()) {
                continue;
            }
            let name = scoping.symbol_name(*symbol).to_owned();
            let tracked = writes.len();
            let total_writes = scoping
                .get_resolved_reference_ids(*symbol)
                .iter()
                .filter(|reference| scoping.get_reference(**reference).is_write())
                .count();
            let alias = CapturedAlias {
                binding: name.clone(),
                declaration: [declaration.start, declaration.end],
                original_reads: count,
                writes: writes.clone(),
                other_writes_possible: reader.unmodeled_writes.contains(symbol)
                    || total_writes > tracked,
            };
            if let Some((previous, _)) = by_name.insert(name.clone(), (*symbol, alias)) {
                if previous != *symbol {
                    ambiguous.insert(name);
                }
            }
        }
        for name in &ambiguous {
            by_name.remove(name);
        }
        if by_name.is_empty() {
            continue;
        }
        let candidates = by_name
            .into_iter()
            .map(|(name, (_, alias))| (name, alias))
            .collect::<BTreeMap<_, _>>();
        let allocator = Allocator::default();
        let transformed = parse_program(&allocator, source, SourceType::unambiguous());
        ensure!(
            transformed.is_clean(),
            "captured handler {path} is not valid JavaScript"
        );
        let semantics = SemanticBuilder::new().build(&transformed.program);
        let mut reads = CapturedReads {
            scoping: semantics.semantic.scoping(),
            candidates: &candidates,
            edits: Vec::new(),
        };
        reads.visit_program(&transformed.program);
        if reads.edits.is_empty() {
            continue;
        }
        reads
            .edits
            .sort_unstable_by_key(|(pos, _)| std::cmp::Reverse(*pos));
        let mut annotated_source = source.clone();
        for (pos, comment) in &reads.edits {
            annotated_source.insert_str(*pos, comment);
        }
        output.push(CapturedAliasView {
            input_path: path.clone(),
            original_span: span,
            annotated_source,
            annotated_reads: reads.edits.len(),
            aliases: candidates.into_values().collect(),
        });
    }
    Ok(output)
}

#[cfg(test)]
mod provenance_tests {
    use super::explain_captured_handler_origins;
    use crate::sha256_hex;

    fn input() -> (String, Vec<(String, String)>) {
        let original = r#"function run(){
            const helper=function(H,alias){
                alias="push";
                H.length<2 && (alias=H);
                return function(value){const out=[];out[alias](value);return out;};
            };
        }"#;
        let start = original.find("function(value)").unwrap_or_default();
        let end = original[start..]
            .find("};")
            .map_or(start, |len| start + len + 1);
        let hash = sha256_hex(original.as_bytes());
        let captured = format!(
            "// Readable, non-devirtualized provenance view. Original SHA-256: {hash}\n\
             // Handler key: 1. Original bytes: {start}..{end}. Factory call: 0..1.\n\
             const capturedHandler = {};\n",
            &original[start..end]
        );
        (original.to_owned(), vec![("key-1.js".to_owned(), captured)])
    }

    #[test]
    fn joins_captured_function_span_to_exact_original_alias_binding() -> anyhow::Result<()> {
        let (original, captures) = input();
        let explained = explain_captured_handler_origins(&original, &captures)?;
        assert_eq!(explained.len(), 1, "{explained:?}");
        let view = &explained[0];
        assert_eq!(view.annotated_reads, 1);
        assert_eq!(view.aliases[0].binding, "alias");
        assert_eq!(view.aliases[0].writes[0].literal.as_deref(), Some("push"));
        assert!(view.aliases[0].writes[1].when.is_some());
        assert!(view
            .annotated_source
            .contains("out[alias /* property alias from original declaration byte"));
        Ok(())
    }

    #[test]
    fn rejects_wrong_source_hash_and_forged_function_span() -> anyhow::Result<()> {
        let (original, mut captures) = input();
        captures[0].1 = captures[0]
            .1
            .replacen("Original SHA-256: ", "Original SHA-256: 0", 1);
        // Malformed SHA or span cannot establish provenance and is skipped.
        assert!(explain_captured_handler_origins(&original, &captures)?.is_empty());
        let (_, mut captures) = input();
        captures[0].1 =
            captures[0]
                .1
                .replacen("Original bytes: ", "Original bytes: 1..2. Fake: ", 1);
        assert!(explain_captured_handler_origins(&original, &captures).is_err());
        Ok(())
    }
}
