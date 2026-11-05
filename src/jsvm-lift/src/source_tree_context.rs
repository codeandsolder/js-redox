//! Navigable lexical source context for extracted JavaScript functions.
//!
//! An extracted closure can refer to definitions in its original program.
//! Recover actual source for those bindings, including their transitive
//! lexical dependencies, without running the original code or pretending
//! that the extracted snippets form an independently executable module.
use anyhow::{ensure, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{BindingPattern, Function, IdentifierReference, VariableDeclarator};
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

#[cfg(test)]
mod tests {
    use super::reconstruct_context;

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
