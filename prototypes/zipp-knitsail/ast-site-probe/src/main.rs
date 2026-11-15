use anyhow::{bail, Context, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{BindingPattern, CallExpression, Expression, Function, VariableDeclarator};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
use serde::Serialize;
use std::{
    collections::HashMap,
    env, fs,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct Frame {
    binding: Option<String>,
    params: Vec<String>,
    start: u32,
    end: u32,
    #[serde(skip)]
    symbols: Vec<Option<SymbolId>>,
}

#[derive(Debug, Clone, Serialize)]
struct Site {
    start: u32,
    end: u32,
    line: usize,
    argument: String,
    eval_is_unresolved: bool,
    argument_is_bound_to_nearest_parameter: bool,
    frames: Vec<Frame>,
}

#[derive(Debug, Serialize)]
struct Candidate {
    path: String,
    site: Site,
    relation: &'static str,
}

struct Scan<'s> {
    source: &'s str,
    scoping: &'s Scoping,
    bindings: HashMap<(u32, u32), String>,
    frames: Vec<Frame>,
    calls: Vec<Site>,
}

impl<'s> Scan<'s> {
    fn new(source: &'s str, scoping: &'s Scoping) -> Self {
        Self {
            source,
            scoping,
            bindings: HashMap::new(),
            frames: Vec::new(),
            calls: Vec::new(),
        }
    }
}

impl<'a> Visit<'a> for Scan<'_> {
    fn visit_variable_declarator(&mut self, decl: &VariableDeclarator<'a>) {
        if let (
            BindingPattern::BindingIdentifier(binding),
            Some(Expression::FunctionExpression(func)),
        ) = (&decl.id, &decl.init)
        {
            self.bindings
                .insert((func.span.start, func.span.end), binding.name.to_string());
        }
        walk::walk_variable_declarator(self, decl);
    }

    fn visit_function(&mut self, function: &Function<'a>, flags: ScopeFlags) {
        let params = function
            .params
            .items
            .iter()
            .map(|param| match &param.pattern {
                BindingPattern::BindingIdentifier(id) => id.name.to_string(),
                _ => "<pattern>".to_owned(),
            })
            .collect();
        let symbols = function
            .params
            .items
            .iter()
            .map(|param| match &param.pattern {
                BindingPattern::BindingIdentifier(id) => id.symbol_id.get(),
                _ => None,
            })
            .collect();
        let binding = function
            .id
            .as_ref()
            .map(|id| id.name.to_string())
            .or_else(|| {
                self.bindings
                    .get(&(function.span.start, function.span.end))
                    .cloned()
            });
        self.frames.push(Frame {
            binding,
            params,
            start: function.span.start,
            end: function.span.end,
            symbols,
        });
        walk::walk_function(self, function, flags);
        self.frames.pop();
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional
            && call.arguments.len() == 1
            && matches!(&call.callee, Expression::Identifier(id) if id.name == "eval")
        {
            let arg = call.arguments[0].as_expression();
            if let Some(Expression::Identifier(id)) = arg {
                let reference_symbol = id
                    .reference_id
                    .get()
                    .and_then(|reference| self.scoping.get_reference(reference).symbol_id());
                let eval_unresolved = if let Expression::Identifier(callee) = &call.callee {
                    callee
                        .reference_id
                        .get()
                        .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                        .is_none()
                } else {
                    false
                };
                let bound = reference_symbol.is_some_and(|symbol| {
                    self.frames.last().is_some_and(|frame| {
                        frame
                            .symbols
                            .iter()
                            .zip(&frame.params)
                            .any(|(declared, name)| {
                                declared == &Some(symbol) && name == id.name.as_str()
                            })
                    })
                });
                self.calls.push(Site {
                    start: call.span.start,
                    end: call.span.end,
                    line: 1 + self
                        .source
                        .get(..call.span.start as usize)
                        .unwrap_or_default()
                        .bytes()
                        .filter(|byte| *byte == b'\n')
                        .count(),
                    argument: id.name.to_string(),
                    eval_is_unresolved: eval_unresolved,
                    argument_is_bound_to_nearest_parameter: bound,
                    frames: self.frames.clone(),
                });
            }
        }
        walk::walk_call_expression(self, call);
    }
}

fn parse_sites(source: &str) -> Result<Vec<Site>> {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, SourceType::cjs()).parse();
    if !parsed.diagnostics.is_empty() || parsed.fatal_error {
        bail!(
            "JavaScript parse failed with {} errors",
            parsed.diagnostics.len()
        );
    }
    let sem = SemanticBuilder::new().build(&parsed.program);
    if !sem.diagnostics.is_empty() {
        bail!(
            "JavaScript semantic analysis failed: {}",
            sem.diagnostics.len()
        );
    }
    let mut scan = Scan::new(source, sem.semantic.scoping());
    scan.visit_program(&parsed.program);
    Ok(scan.calls)
}

fn utf16_to_bytes(text: &str, offset: usize) -> Result<u32> {
    let mut units = 0;
    for (index, ch) in text.char_indices() {
        if units == offset {
            return Ok(index.try_into()?);
        }
        units += ch.len_utf16();
        if units > offset {
            bail!("UTF-16 offset falls inside a surrogate pair");
        }
    }
    if units == offset {
        return Ok(text.len().try_into()?);
    }
    bail!("UTF-16 offset exceeds source length");
}

fn js_files(root: &Path) -> Result<Vec<PathBuf>> {
    fn visit(dir: &Path, files: &mut Vec<PathBuf>) -> Result<()> {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let kind = entry.file_type()?;
            if kind.is_symlink() {
                bail!("Symlink in static source tree: {}", entry.path().display());
            }
            if kind.is_dir() {
                visit(&entry.path(), files)?;
            } else if kind.is_file() && entry.path().extension().is_some_and(|e| e == "js") {
                files.push(entry.path());
            }
        }
        Ok(())
    }
    let mut result = Vec::new();
    visit(root, &mut result)?;
    result.sort();
    Ok(result)
}

fn stable_named_scope(frames: &[Frame]) -> &[Frame] {
    // Extracted helper files omit the outer VM loader and anonymous IIFEs.
    // Normalize at the nearest named function binding, retaining inner lexical structure.
    let start = frames
        .iter()
        .rposition(|frame| frame.binding.is_some())
        .unwrap_or(0);
    &frames[start..]
}

fn same_lexical_structure(a: &Site, b: &Site) -> bool {
    a.argument == b.argument
        && a.eval_is_unresolved
        && b.eval_is_unresolved
        && a.argument_is_bound_to_nearest_parameter
        && b.argument_is_bound_to_nearest_parameter
        && stable_named_scope(&a.frames).len() == stable_named_scope(&b.frames).len()
        && stable_named_scope(&a.frames)
            .iter()
            .zip(stable_named_scope(&b.frames))
            .all(|(left, right)| left.binding == right.binding && left.params == right.params)
}

fn main() -> Result<()> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 4 {
        bail!("usage: knitsail-ast-site-probe ORIGINAL_VM START_UTF16 END_UTF16 STATIC_TREE");
    }
    let original =
        fs::read_to_string(&args[0]).with_context(|| format!("read original JS: {}", args[0]))?;
    let start: usize = args[1].parse()?;
    let end: usize = args[2].parse()?;
    let start_byte = utf16_to_bytes(&original, start)?;
    let end_byte = utf16_to_bytes(&original, end)?;
    let original_sites = parse_sites(&original)?;
    let site = original_sites
        .iter()
        .find(|site| site.start == start_byte && site.end == end_byte)
        .cloned()
        .with_context(|| {
            format!(
                "No matching direct eval(D) at UTF-16 offsets; byte target={start_byte}..{end_byte}, candidates={:?}",
                original_sites.iter().map(|s| (s.start, s.end, s.argument.as_str())).collect::<Vec<_>>()
            )
        })?;
    if !site.argument_is_bound_to_nearest_parameter || !site.eval_is_unresolved {
        bail!("Original call does not resolve to direct global eval(nearest function parameter)");
    }
    let root = Path::new(&args[3]);
    let mut candidates = Vec::new();
    let mut parse_failures = Vec::new();
    for filepath in js_files(root)? {
        let rel = filepath
            .strip_prefix(root)?
            .to_string_lossy()
            .replace('\\', "/");
        let text = fs::read_to_string(&filepath)?;
        let calls = match parse_sites(&text) {
            Ok(calls) => calls,
            Err(error) => {
                parse_failures.push(serde_json::json!({"path": rel, "reason":error.to_string()}));
                continue;
            }
        };
        for c in calls {
            if same_lexical_structure(&site, &c) {
                candidates.push(Candidate {
                    path: rel.clone(),
                    site: c,
                    relation: "ast-lexical-structure-match",
                });
            }
        }
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "schema":"js-redox/ast-site-probe/v1",
            "original":{
                "startUtf16":start,
                "endUtf16":end,
                "startByte":start_byte,
                "endByte":end_byte,
                "site":site,
            },
            "matches":candidates,
            "parseFailures":parse_failures,
        }))?
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parameter_binding_and_outer_wrapper_normalization() {
        let original =
            "(function(){const oU=function(A,D){return function(D){return eval(D)}}})();";
        let extracted = "const oU = function(A, D) { return function(D) { return eval ( D ); }; };";
        let original_site = parse_sites(original).expect("parse original");
        let extracted_site = parse_sites(extracted).expect("parse extracted");
        assert_eq!(original_site.len(), 1);
        assert_eq!(extracted_site.len(), 1);
        assert!(original_site[0].eval_is_unresolved);
        assert!(original_site[0].argument_is_bound_to_nearest_parameter);
        assert!(same_lexical_structure(
            &original_site[0],
            &extracted_site[0]
        ));
    }

    #[test]
    fn shadowed_eval_or_unbound_argument_is_not_a_match() {
        let canonical = "const oU=function(D){return eval(D)}";
        let shadowed_eval = "const oU=function(D){const eval=(x)=>x;return eval(D)}";
        let shadowed_arg = "const oU=function(D){const E=D;return eval(E)}";
        let original = parse_sites(canonical).unwrap().remove(0);
        let evil = parse_sites(shadowed_eval).unwrap().remove(0);
        assert!(!evil.eval_is_unresolved);
        assert!(!same_lexical_structure(&original, &evil));
        let alias = parse_sites(shadowed_arg).unwrap().remove(0);
        assert!(!alias.argument_is_bound_to_nearest_parameter);
        assert!(!same_lexical_structure(&original, &alias));
    }

    #[test]
    fn utf16_offsets_are_not_assumed_to_be_utf8_byte_offsets() {
        let text = "a💡eval(D)";
        assert_eq!(utf16_to_bytes(text, 0).unwrap(), 0);
        assert_eq!(utf16_to_bytes(text, 1).unwrap(), 1);
        assert!(utf16_to_bytes(text, 2).is_err());
        assert_eq!(utf16_to_bytes(text, 3).unwrap(), 5);
        assert_eq!(utf16_to_bytes(text, 10).unwrap(), 12);
    }
}
