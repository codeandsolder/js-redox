//! Navigable lexical source context for extracted JavaScript functions.
//!
//! An extracted closure can refer to definitions in its original program.
//! Recover actual source for those bindings, including their transitive
//! lexical dependencies, without running the original code or pretending
//! that the extracted snippets form an independently executable module.
use anyhow::{ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, Expression, Function, IdentifierReference, Statement, VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType, Span};
use oxc_syntax::scope::ScopeFlags;
use oxc_syntax::symbol::SymbolId;
use rolldown_redox::ecmascript::parse_program;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Debug, Clone)]
struct Definition {
    name: String,
    symbol: SymbolId,
    value_span: Span,
    declaration: bool,
}

#[derive(Default)]
struct DefinitionVisitor {
    definitions: Vec<Definition>,
}

impl<'a> Visit<'a> for DefinitionVisitor {
    fn visit_variable_declarator(&mut self, it: &VariableDeclarator<'a>) {
        if let (BindingPattern::BindingIdentifier(id), Some(init)) = (&it.id, &it.init) {
            if let Some(symbol) = id.symbol_id.get() {
                self.definitions.push(Definition {
                    name: id.name.to_string(),
                    symbol,
                    value_span: init.span(),
                    declaration: false,
                });
            }
        }
        walk::walk_variable_declarator(self, it);
    }

    fn visit_function(&mut self, it: &Function<'a>, flags: ScopeFlags) {
        if it.is_declaration() {
            if let Some(id) = &it.id {
                if let Some(symbol) = id.symbol_id.get() {
                    self.definitions.push(Definition {
                        name: id.name.to_string(),
                        symbol,
                        value_span: it.span,
                        declaration: true,
                    });
                }
            }
        }
        walk::walk_function(self, it, flags);
    }
}

struct ReferenceVisitor<'s> {
    scoping: &'s Scoping,
    references: Vec<(Span, Option<SymbolId>, String)>,
}

impl<'a> Visit<'a> for ReferenceVisitor<'_> {
    fn visit_identifier_reference(&mut self, id: &IdentifierReference<'a>) {
        let symbol = id
            .reference_id
            .get()
            .and_then(|reference| self.scoping.get_reference(reference).symbol_id());
        self.references.push((id.span, symbol, id.name.to_string()));
    }
}

#[derive(Debug, Clone)]
pub struct ContextHelper {
    pub name: String,
    pub file: String,
    pub source: String,
    pub references: Vec<String>,
    /// This binding receives a later resolved write in the original program.
    pub mutable_binding: bool,
}

#[derive(Debug, Clone)]
pub struct HandlerContext {
    pub path: String,
    pub linked_helpers: Vec<String>,
    pub unresolved_references: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct ContextSourceTree {
    pub helpers: Vec<ContextHelper>,
    pub handlers: Vec<HandlerContext>,
    pub unmatched_names: BTreeSet<String>,
}

fn handler_free_references(source: &str) -> Result<BTreeSet<String>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(
        parsed.is_clean(),
        "extracted handler has invalid JavaScript syntax"
    );
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantic.semantic.scoping();
    let mut visitor = ReferenceVisitor {
        scoping,
        references: Vec::new(),
    };
    visitor.visit_program(&parsed.program);
    Ok(visitor
        .references
        .into_iter()
        .filter_map(|(_, symbol, name)| symbol.is_none().then_some(name))
        .collect())
}

/// Bind references from extracted handlers to uniquely named original source
/// declarations, and follow *exact* resolved symbols inside those declarations.
///
/// The entrypoint matches by unique name because a standalone extracted
/// function no longer carries its old lexical IDs. After that initial join,
/// traversal stays inside the original semantic symbol graph.
pub fn reconstruct_context(
    original: &str,
    handler_sources: &[(String, String)],
) -> Result<ContextSourceTree> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, original, SourceType::unambiguous());
    ensure!(
        parsed.is_clean(),
        "original context is not valid JavaScript"
    );
    let semantic = SemanticBuilder::new().build(&parsed.program);
    let scoping = semantic.semantic.scoping();

    let mut definitions = DefinitionVisitor::default();
    definitions.visit_program(&parsed.program);
    let mut by_name: BTreeMap<String, Vec<Definition>> = BTreeMap::new();
    let mut by_symbol = BTreeMap::new();
    for definition in definitions.definitions {
        by_symbol.insert(definition.symbol, definition.clone());
        by_name
            .entry(definition.name.clone())
            .or_default()
            .push(definition);
    }

    let mut references = ReferenceVisitor {
        scoping,
        references: Vec::new(),
    };
    references.visit_program(&parsed.program);

    let mut queue = VecDeque::new();
    let mut handlers = Vec::new();
    let mut unmatched_names = BTreeSet::new();
    for (path, source) in handler_sources {
        let mut linked_helpers = Vec::new();
        let mut unresolved_references = Vec::new();
        for name in handler_free_references(source)? {
            let matches = by_name.get(&name);
            if let Some([definition]) = matches.map(Vec::as_slice) {
                linked_helpers.push(name);
                queue.push_back(definition.symbol);
            } else {
                if matches.is_none() {
                    unmatched_names.insert(name.clone());
                }
                unresolved_references.push(name);
            }
        }
        handlers.push(HandlerContext {
            path: path.clone(),
            linked_helpers,
            unresolved_references,
        });
    }

    let mut visited = BTreeSet::new();
    let mut helpers = Vec::new();
    while let Some(symbol) = queue.pop_front() {
        if !visited.insert(symbol) {
            continue;
        }
        let Some(definition) = by_symbol.get(&symbol) else {
            continue;
        };
        let mut dependencies = BTreeSet::new();
        for (span, target, name) in &references.references {
            if definition.value_span.start <= span.start && span.end <= definition.value_span.end {
                if let Some(other) = target {
                    if *other != symbol && by_symbol.contains_key(other) {
                        queue.push_back(*other);
                        dependencies.insert(name.clone());
                    }
                }
            }
        }
        let Some(value) =
            original.get(definition.value_span.start as usize..definition.value_span.end as usize)
        else {
            continue;
        };
        let source = if definition.declaration {
            format!("{value}\n")
        } else {
            format!("const {} = {value};\n", definition.name)
        };
        let mutable_binding = scoping
            .get_resolved_reference_ids(symbol)
            .iter()
            .any(|reference_id| scoping.get_reference(*reference_id).is_write());
        helpers.push(ContextHelper {
            name: definition.name.clone(),
            file: format!(
                "helpers/{}-{}.js",
                definition.name, definition.value_span.start
            ),
            source,
            references: dependencies.into_iter().collect(),
            mutable_binding,
        });
    }
    helpers.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(ContextSourceTree {
        helpers,
        handlers,
        unmatched_names,
    })
}

/// An executable-looking, but presentation-only, copy of an extracted handler.
/// Every annotation is attached to an *unresolved lexical call* in the
/// extracted AST and to a uniquely resolved original-source helper. This is
/// not a replacement for the captured handler or proof-checked JS.
#[derive(Debug)]
pub struct AnnotatedHandlerCalls {
    pub source: String,
    pub call_count: usize,
    pub helpers: Vec<String>,
}

/// A recovered, source-backed primitive-argument specialization. The path is
/// relative to the lexical-context directory; it is a browsing view, not a
/// drop-in replacement for the original helper.
#[derive(Clone, Debug)]
pub struct SpecializedHelperCall {
    pub helper: String,
    pub constants: Vec<(usize, String)>,
    pub file: String,
}

/// Preserve the exact expression of a tiny, single-return original helper.
/// Longer or effectful function bodies are linked instead of summarized.
fn single_return_from_original(helper: &ContextHelper) -> Option<String> {
    if helper.mutable_binding {
        return None;
    }
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &helper.source, SourceType::unambiguous());
    if !parsed.is_clean() {
        return None;
    }
    let function = match parsed.program.body.first()? {
        Statement::VariableDeclaration(declaration) => {
            let Expression::FunctionExpression(function) =
                declaration.declarations.first()?.init.as_ref()?
            else {
                return None;
            };
            function
        }
        Statement::FunctionDeclaration(function) => function,
        _ => return None,
    };
    let statements = &function.body.as_ref()?.statements;
    let [Statement::ReturnStatement(ret)] = statements.as_slice() else {
        return None;
    };
    let expression = ret.argument.as_ref()?;
    let text = helper
        .source
        .get(expression.span().start as usize..expression.span().end as usize)?
        .trim();
    (text.len() <= 140 && !text.contains('\n') && !text.contains('\r') && !text.contains("*/"))
        .then(|| text.to_owned())
}

type LiteralArguments = Vec<(usize, String)>;
type KnownSpecializations = BTreeMap<(String, LiteralArguments), String>;
type LiteralCallSites = BTreeMap<u32, (String, LiteralArguments)>;

struct HandlerCallAnnotator<'s> {
    scoping: &'s Scoping,
    helpers: &'s BTreeMap<String, &'s ContextHelper>,
    specialized: &'s KnownSpecializations,
    call_constants: &'s LiteralCallSites,
    helper_prefix: String,
    seen: BTreeSet<String>,
    edits: Vec<(usize, String)>,
}

impl<'a> Visit<'a> for HandlerCallAnnotator<'_> {
    fn visit_call_expression(&mut self, call: &oxc_ast::ast::CallExpression<'a>) {
        if !call.optional {
            let mut callee = &call.callee;
            while let Expression::ParenthesizedExpression(inner) = callee {
                callee = &inner.expression;
            }
            if let Expression::Identifier(identifier) = callee {
                let external = identifier.reference_id.get().is_some_and(|reference| {
                    self.scoping.get_reference(reference).symbol_id().is_none()
                });
                let name = identifier.name.as_str();
                if external {
                    if let Some(helper) = self.helpers.get(name) {
                        let mut details = Vec::new();
                        if self.seen.insert(name.to_owned()) {
                            let link = format!("{}{}", self.helper_prefix, helper.file);
                            let detail = if helper.mutable_binding {
                                format!("initial definition {link}; original binding reassigned")
                            } else if let Some(expression) = single_return_from_original(helper) {
                                format!("return {expression}; original definition {link}")
                            } else {
                                format!("original definition {link}")
                            };
                            details.push(detail);
                        }
                        if !helper.mutable_binding {
                            if let Some((callee, constants)) =
                                self.call_constants.get(&call.span.start)
                            {
                                if callee == name {
                                    if let Some(path) =
                                        self.specialized.get(&(name.to_owned(), constants.clone()))
                                    {
                                        details.push(format!(
                                            "specialized at {} => {}{}",
                                            constants
                                                .iter()
                                                .map(|(index, value)| format!("arg{index}={value}"))
                                                .collect::<Vec<_>>()
                                                .join(", "),
                                            self.helper_prefix,
                                            path
                                        ));
                                    }
                                }
                            }
                        }
                        if !details.is_empty() {
                            self.edits.push((
                                identifier.span.end as usize,
                                format!(
                                    " /* lexical helper {name}: {} */",
                                    details
                                        .join("; ")
                                        .replace("*/", "*\\/")
                                        .replace('\n', "\\n")
                                        .replace('\r', "\\r")
                                ),
                            ));
                        }
                    }
                }
            }
        }
        walk::walk_call_expression(self, call);
    }
}

/// Generate local, inline provenance at direct helper calls, preserving the
/// original program's binding distinction (including shadowed parameters).
/// The context extractor supplies the unique original-name join, while this
/// handler's own Oxc scoping checks the actual reference at each call.
pub fn annotate_handler_helper_calls(
    source: &str,
    context: &ContextSourceTree,
    handler: &HandlerContext,
) -> Result<Option<AnnotatedHandlerCalls>> {
    annotate_handler_helper_calls_with_specializations(source, context, handler, &[])
}

pub fn annotate_handler_helper_calls_with_specializations(
    source: &str,
    context: &ContextSourceTree,
    handler: &HandlerContext,
    specialized_calls: &[SpecializedHelperCall],
) -> Result<Option<AnnotatedHandlerCalls>> {
    let call_constants = crate::source_tree_specialize::literal_calls(source)?
        .into_iter()
        .map(|call| (call.span.start, (call.helper, call.constants)))
        .collect::<BTreeMap<_, _>>();
    let specialized = specialized_calls
        .iter()
        .map(|item| {
            (
                (item.helper.clone(), item.constants.clone()),
                item.file.clone(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, source, SourceType::unambiguous());
    ensure!(
        parsed.is_clean(),
        "readable handler is not valid JavaScript"
    );
    let semantic = SemanticBuilder::new().build(&parsed.program);

    let mut counts = BTreeMap::<&str, usize>::new();
    for helper in &context.helpers {
        *counts.entry(&helper.name).or_default() += 1;
    }
    let linked = handler
        .linked_helpers
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let helpers = context
        .helpers
        .iter()
        .filter(|helper| {
            linked.contains(helper.name.as_str()) && counts.get(helper.name.as_str()) == Some(&1)
        })
        .map(|helper| (helper.name.clone(), helper))
        .collect::<BTreeMap<_, _>>();
    let mut annotator = HandlerCallAnnotator {
        scoping: semantic.semantic.scoping(),
        helpers: &helpers,
        specialized: &specialized,
        call_constants: &call_constants,
        // The emitted file is under annotated-handlers/<handler path>,
        // while definitions live under sibling helpers/. Account for
        // handlers originally located in arbitrarily nested folders.
        helper_prefix: "../".repeat(handler.path.bytes().filter(|b| *b == b'/').count() + 1),
        seen: BTreeSet::new(),
        edits: Vec::new(),
    };
    annotator.visit_program(&parsed.program);
    if annotator.edits.is_empty() {
        return Ok(None);
    }
    let mut output = source.to_owned();
    for (offset, comment) in annotator.edits.iter().rev() {
        if !output.is_char_boundary(*offset) {
            anyhow::bail!("original handler call span is not UTF-8 aligned");
        }
        output.insert_str(*offset, comment);
    }
    Ok(Some(AnnotatedHandlerCalls {
        source: output,
        call_count: annotator.edits.len(),
        helpers: annotator.seen.into_iter().collect(),
    }))
}

#[cfg(test)]
mod tests {
    use super::{annotate_handler_helper_calls, reconstruct_context};
    use anyhow::{Context as _, Result};
    use oxc_allocator::Allocator;
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    #[test]
    fn inline_call_context_uses_only_unique_unresolved_lexical_helpers() -> Result<()> {
        let original = r#"
            function parent() {
                const AM = function(J) { return J.Y ? fast(J) : slow(J); };
                const O = function(J, Q) { const v=read(J); return choose(v,Q); };
                let mutable = function(J) { return J; };
                mutable = function(J) { return J + 1; };
                function one() { const duplicate = function(J) {return J;}; }
                function two() { const duplicate = function(J) {return J+1;}; }
            }
        "#;
        let source = r#"const capturedHandler = function(input) {
            AM(input);
            O(input, 24);
            mutable(input);
            duplicate(input);
            function shadow(AM) { return AM(input); }
            return AM(input);
        };"#;
        let context =
            reconstruct_context(original, &[("nested/handler.js".into(), source.into())])?;
        let handler = context.handlers.first().context("missing handler")?;
        let output =
            annotate_handler_helper_calls(source, &context, handler)?.context("no annotation")?;
        assert_eq!(output.call_count, 3);
        assert_eq!(output.helpers, ["AM", "O", "mutable"]);
        assert!(
            output.source.contains("AM /* lexical helper AM: return J.Y ? fast(J) : slow(J); original definition ../../helpers/AM-"),
            "{}",
            output.source
        );
        assert!(
            output
                .source
                .contains("O /* lexical helper O: original definition ../../helpers/O-"),
            "{}",
            output.source
        );
        assert!(
            output.source.contains(
                "mutable /* lexical helper mutable: initial definition ../../helpers/mutable-"
            ) && output.source.contains("original binding reassigned"),
            "{}",
            output.source
        );
        assert!(
            output.source.contains("duplicate(input)"),
            "{}",
            output.source
        );
        assert!(
            output.source.contains("return AM(input)"),
            "{}",
            output.source
        );
        assert!(
            output.source.contains("return AM(input);"),
            "{}",
            output.source
        );
        let allocator = Allocator::default();
        assert!(parse_program(&allocator, &output.source, SourceType::unambiguous()).is_clean());
        Ok(())
    }

    #[test]
    fn inline_call_context_links_each_proven_mode_specific_body() -> Result<()> {
        let original = "function parent(){const O=function(input, mode){return mode === 24 ? input + 1 : input;};}";
        let source = r#"const capturedHandler=function(input,mode){
            O(input,24);
            O(input,16);
            O(input,24);
            O(input,"*/");
            O(input,mode);
            function inner(O){ return O(input,24); }
        };"#;
        let context =
            reconstruct_context(original, &[("nested/handler.js".into(), source.into())])?;
        let specializations = [
            super::SpecializedHelperCall {
                helper: "O".into(),
                constants: vec![(1, "24".into())],
                file: "specializations/O-24.js".into(),
            },
            super::SpecializedHelperCall {
                helper: "O".into(),
                constants: vec![(1, "16".into())],
                file: "specializations/O-16.js".into(),
            },
            super::SpecializedHelperCall {
                helper: "O".into(),
                constants: vec![(1, "\"*/\"".into())],
                file: "specializations/O-comment.js".into(),
            },
        ];
        let result = super::annotate_handler_helper_calls_with_specializations(
            source,
            &context,
            &context.handlers[0],
            &specializations,
        )?
        .context("expected source-backed annotations")?;
        assert_eq!(result.call_count, 4);
        assert_eq!(result.helpers, ["O"]);
        assert_eq!(
            result
                .source
                .matches("specialized at arg1=24 => ../../specializations/O-24.js")
                .count(),
            2,
            "{}",
            result.source
        );
        assert!(result
            .source
            .contains("specialized at arg1=16 => ../../specializations/O-16.js"));
        assert!(
            result.source.contains("specializations/O-comment.js")
                && result.source.contains("*\\/"),
            "{}",
            result.source
        );
        assert!(result.source.contains("O(input,mode)"), "{}", result.source);
        assert!(
            result.source.contains("return O(input,24)"),
            "{}",
            result.source
        );
        let allocator = Allocator::default();
        assert!(parse_program(&allocator, &result.source, SourceType::unambiguous()).is_clean());
        Ok(())
    }

    #[test]
    fn inline_call_context_skips_unresolved_without_confirmed_definition() -> Result<()> {
        let source = "const capturedHandler=function(x){return missing(x)};";
        let context = reconstruct_context(
            "function original() { const helper = function(x) {return x}; }",
            &[("handler.js".into(), source.into())],
        )?;
        assert!(annotate_handler_helper_calls(source, &context, &context.handlers[0])?.is_none());
        Ok(())
    }

    #[test]
    fn traverses_exact_lexical_helpers_not_shadowed_parameters() {
        let original = r#"
            function originalProgram() {
                const varint = function(input) { return byte(input) + 1; };
                const byte = function(input) { return input.value; };
                const table = { get(key) { return key + 4; } };
                const mutable = function() { return 4; };
                mutable = function() { return 8; };
            }
        "#;
        let handlers = vec![
            (
                "alpha.js".into(),
                "const capturedHandler=function(input){return varint(input)+table.get(2)+missing(input);};"
                    .into(),
            ),
            (
                "beta.js".into(),
                "const capturedHandler=function(varint){return varint(3);};".into(),
            ),
            (
                "gamma.js".into(),
                "const capturedHandler=function(){return mutable();};".into(),
            ),
        ];
        let context = reconstruct_context(original, &handlers);
        assert!(context.is_ok());
        if let Ok(context) = context {
            let names = context
                .helpers
                .iter()
                .map(|item| item.name.as_str())
                .collect::<Vec<_>>();
            assert!(names.contains(&"varint"));
            assert!(names.contains(&"byte"));
            assert!(names.contains(&"table"));
            assert!(names.contains(&"mutable"));
            assert_eq!(context.handlers[0].linked_helpers.len(), 2);
            assert!(context.handlers[1].linked_helpers.is_empty());
            assert!(context.unmatched_names.contains("missing"));
            let varint = context.helpers.iter().find(|item| item.name == "varint");
            assert!(varint.is_some());
            if let Some(varint) = varint {
                assert!(varint.references.contains(&"byte".to_owned()));
                assert!(varint.source.contains("function(input)"));
            }
            let mutable = context.helpers.iter().find(|item| item.name == "mutable");
            assert!(mutable.is_some_and(|item| item.mutable_binding));
        }
    }

    #[test]
    fn ambiguous_names_cannot_be_guessed_from_extracted_handler() {
        let original = r#"
            function a() { let helper = function() { return 1; }; }
            function b() { let helper = function() { return 2; }; }
        "#;
        let handler = vec![(
            "handler.js".into(),
            "const capturedHandler=()=>helper();".into(),
        )];
        let context = reconstruct_context(original, &handler);
        assert!(context.is_ok());
        if let Ok(context) = context {
            assert!(context.helpers.is_empty());
            assert_eq!(
                context.handlers[0].unresolved_references,
                vec!["helper".to_owned()]
            );
        }
    }
}
