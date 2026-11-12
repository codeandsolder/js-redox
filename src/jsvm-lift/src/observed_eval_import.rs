//! Execution-conditioned, AST-linked source evidence for static source trees.
use crate::sha256_hex;
use anyhow::{bail, Context, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrowFunctionExpression, BindingPattern, CallExpression, Expression, Function,
    IdentifierReference, VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_codegen::Codegen;
use oxc_parser::Parser;
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use oxc_syntax::{
    scope::ScopeFlags,
    symbol::{SymbolFlags, SymbolId},
};
use serde::Deserialize;
use serde::Serialize;
use serde_json::json;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct Frame {
    binding: Option<String>,
    kind: &'static str,
    params: Vec<String>,
    start: u32,
    end: u32,
    #[serde(skip)]
    symbols: Vec<Option<SymbolId>>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
struct Site {
    start: u32,
    end: u32,
    line: usize,
    /// Codegen-normalized argument expressions, including any spread operands.
    argument: String,
    /// Preserve arity and spread shape: a sequence argument is not two arguments.
    argument_shapes: Vec<ArgumentShape>,
    /// Semantic binding roles for every referenced identifier in argument AST order.
    argument_references: Vec<ArgumentReference>,
    eval_is_unresolved: bool,
    argument_uses_nearest_formal_parameter: bool,
    frames: Vec<Frame>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ArgumentShape {
    spread: bool,
    expression: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct ArgumentReference {
    name: String,
    /// Distinguish unresolved global, lexical-local, and frame-formal uses.
    role: String,
}

struct ArgumentReferences<'s> {
    scoping: &'s Scoping,
    frames: &'s [Frame],
    references: Vec<ArgumentReference>,
}

impl<'a> Visit<'a> for ArgumentReferences<'_> {
    fn visit_identifier_reference(&mut self, identifier: &IdentifierReference<'a>) {
        let symbol = identifier
            .reference_id
            .get()
            .and_then(|reference| self.scoping.get_reference(reference).symbol_id());
        let role = match symbol {
            None => "unresolved".to_owned(),
            Some(symbol) => self
                .frames
                .iter()
                .rev()
                .enumerate()
                .find_map(|(depth, frame)| {
                    frame
                        .symbols
                        .iter()
                        .position(|param| *param == Some(symbol))
                        .map(|position| format!("formal:{depth}:{position}"))
                })
                .unwrap_or_else(|| {
                    let flags = self.scoping.symbol_flags(symbol);
                    let kind = if flags.intersects(SymbolFlags::Import | SymbolFlags::TypeImport) {
                        "import"
                    } else if flags.contains(SymbolFlags::CatchVariable) {
                        "catch"
                    } else if flags.contains(SymbolFlags::ConstVariable) {
                        "const"
                    } else if flags.contains(SymbolFlags::BlockScopedVariable) {
                        "let"
                    } else if flags.contains(SymbolFlags::FunctionScopedVariable) {
                        "var"
                    } else if flags.contains(SymbolFlags::Function) {
                        "function"
                    } else if flags.contains(SymbolFlags::Class) {
                        "class"
                    } else {
                        "lexical"
                    };
                    kind.to_owned()
                }),
        };
        self.references.push(ArgumentReference {
            name: identifier.name.to_string(),
            role,
        });
    }
}

fn canonical_argument(expression: &Expression<'_>) -> String {
    let mut printer = Codegen::new();
    printer.print_expression(expression);
    printer.into_source_text()
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
        if let BindingPattern::BindingIdentifier(binding) = &decl.id {
            let span = match decl.init.as_ref() {
                Some(Expression::FunctionExpression(function)) => Some(function.span),
                Some(Expression::ArrowFunctionExpression(arrow)) => Some(arrow.span),
                _ => None,
            };
            if let Some(span) = span {
                self.bindings
                    .insert((span.start, span.end), binding.name.to_string());
            }
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
            kind: "function",
            params,
            start: function.span.start,
            end: function.span.end,
            symbols,
        });
        walk::walk_function(self, function, flags);
        self.frames.pop();
    }

    fn visit_arrow_function_expression(&mut self, arrow: &ArrowFunctionExpression<'a>) {
        let params = arrow
            .params
            .items
            .iter()
            .map(|param| match &param.pattern {
                BindingPattern::BindingIdentifier(id) => id.name.to_string(),
                _ => "<pattern>".to_owned(),
            })
            .collect();
        let symbols = arrow
            .params
            .items
            .iter()
            .map(|param| match &param.pattern {
                BindingPattern::BindingIdentifier(id) => id.symbol_id.get(),
                _ => None,
            })
            .collect();
        let binding = self
            .bindings
            .get(&(arrow.span.start, arrow.span.end))
            .cloned();
        self.frames.push(Frame {
            binding,
            kind: "arrow",
            params,
            start: arrow.span.start,
            end: arrow.span.end,
            symbols,
        });
        walk::walk_arrow_function_expression(self, arrow);
        self.frames.pop();
    }

    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if !call.optional
            && !call.arguments.is_empty()
            && matches!(&call.callee, Expression::Identifier(id) if id.name == "eval")
        {
            let eval_unresolved = if let Expression::Identifier(callee) = &call.callee {
                callee
                    .reference_id
                    .get()
                    .and_then(|reference| self.scoping.get_reference(reference).symbol_id())
                    .is_none()
            } else {
                false
            };
            let mut parts = Vec::new();
            let mut shapes = Vec::new();
            let mut refs = ArgumentReferences {
                scoping: self.scoping,
                frames: &self.frames,
                references: Vec::new(),
            };
            for arg in &call.arguments {
                match arg {
                    Argument::SpreadElement(spread) => {
                        let expression = canonical_argument(&spread.argument);
                        parts.push(format!("...{expression}"));
                        shapes.push(ArgumentShape {
                            spread: true,
                            expression,
                        });
                        refs.visit_expression(&spread.argument);
                    }
                    _ => {
                        if let Some(expression) = arg.as_expression() {
                            let text = canonical_argument(expression);
                            parts.push(text.clone());
                            shapes.push(ArgumentShape {
                                spread: false,
                                expression: text,
                            });
                            refs.visit_expression(expression);
                        }
                    }
                }
            }
            // The original runtime only guarantees the observed eval operand;
            // the additional argument list is still part of the static site.
            let bound = refs
                .references
                .iter()
                .any(|reference| reference.role.starts_with("formal:0:"));
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
                argument: parts.join(","),
                argument_shapes: shapes,
                argument_references: refs.references,
                eval_is_unresolved: eval_unresolved,
                argument_uses_nearest_formal_parameter: bound,
                frames: self.frames.clone(),
            });
        }
        walk::walk_call_expression(self, call);
    }
}

fn parse_sites_with_type(source: &str, source_type: SourceType) -> Result<Vec<Site>> {
    let allocator = Allocator::default();
    let parsed = Parser::new(&allocator, source, source_type).parse();
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

fn parse_sites(source: &str) -> Result<Vec<Site>> {
    // Generated loader source is commonly a script/CJS, while real static
    // source files may contain ESM syntax. Preserve the first fully valid parse.
    parse_sites_with_type(source, SourceType::cjs()).or_else(|script_error| {
        parse_sites_with_type(source, SourceType::mjs())
            .with_context(|| format!("JavaScript script/CJS parse also failed: {script_error}"))
    })
}

fn parse_sites_file(source: &str, path: &Path) -> Result<Vec<Site>> {
    match path.extension().and_then(|value| value.to_str()) {
        Some("mjs" | "mts") => parse_sites_with_type(
            source,
            SourceType::from_path(path).context("invalid module source type")?,
        ),
        Some("cjs" | "cts") => parse_sites_with_type(
            source,
            SourceType::from_path(path).context("invalid CommonJS source type")?,
        ),
        Some("jsx" | "tsx" | "ts") => parse_sites_with_type(
            source,
            SourceType::from_path(path).context("invalid source type")?,
        ),
        _ => parse_sites(source),
    }
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
            } else if kind.is_file()
                && entry
                    .path()
                    .extension()
                    .and_then(|e| e.to_str())
                    .is_some_and(|ext| {
                        matches!(
                            ext,
                            "js" | "cjs" | "mjs" | "jsx" | "ts" | "cts" | "mts" | "tsx"
                        )
                    })
            {
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
    a.argument_shapes == b.argument_shapes
        && a.argument_references == b.argument_references
        && a.eval_is_unresolved
        && b.eval_is_unresolved
        && a.argument_uses_nearest_formal_parameter == b.argument_uses_nearest_formal_parameter
        && stable_named_scope(&a.frames).len() == stable_named_scope(&b.frames).len()
        && stable_named_scope(&a.frames)
            .iter()
            .zip(stable_named_scope(&b.frames))
            .all(|(left, right)| {
                left.binding == right.binding
                    && left.kind == right.kind
                    && left.params == right.params
            })
}

/// One independently captured execution and both exact original source layers.
#[derive(Clone, Debug)]
pub struct ObservedEvalInput {
    pub observed_tree: PathBuf,
    /// One original file for direct execution, two for a decoded loader.
    pub source_files: Vec<PathBuf>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Manifest {
    schema_version: u32,
    #[serde(default)]
    html_sha256: Option<String>,
    #[serde(default)]
    capture_sha256: Option<String>,
    source_provenance: SourceProvenance,
    truncated: bool,
    event_count: usize,
    unique_source_count: usize,
    entries: Vec<ObservedEntry>,
}

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
struct SourceProvenance {
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    outer_loader: Option<OuterLoader>,
    #[serde(default)]
    inner_executable: Option<InnerExecutable>,
    #[serde(default)]
    executable: Option<DirectExecutable>,
}

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
struct DirectExecutable {
    sha256: String,
    eval_site: SourceSite,
}

#[derive(Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
struct OuterLoader {
    sha256: String,
    indirect_eval_site: SourceSite,
    decoded_by: String,
}

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
struct InnerExecutable {
    sha256: String,
    eval_site: SourceSite,
    stripped_leading_newline_code_units: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
struct SourceSite {
    start: usize,
    end: usize,
    expression: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ObservedEntry {
    sha256: String,
    utf16_length: usize,
    first_event: usize,
    occurrences: usize,
    returned: usize,
    threw: usize,
    returned_types: BTreeMap<String, usize>,
    thrown_types: BTreeMap<String, usize>,
    /// Optional original event order within a multi-site execution, retained
    /// even when each site is exported as a separate source witness.
    #[serde(default)]
    global_event_indices: Option<Vec<usize>>,
    raw_file: String,
    readable_file: Option<String>,
    readable_status: String,
}

struct SourceEntry {
    meta: ObservedEntry,
    raw: Vec<u8>,
    readable: Option<Vec<u8>>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct AstMatch {
    path: String,
    line: usize,
    byte_span: [u32; 2],
    relation: &'static str,
    lexical_frames: Vec<Frame>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DirectBundle {
    schema_version: u32,
    kind: String,
    executable_sha256: String,
    capture_sha256: String,
    sites: Vec<BundleSite>,
    captures: Vec<BundleCapture>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BundleSite {
    site_index: usize,
    eval_site: SourceSite,
    event_count: usize,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BundleCapture {
    site_index: usize,
    directory: String,
    eval_site: SourceSite,
    event_count: usize,
}

/// Expand one already exported multi-site run into independently validated
/// per-site captures. No fabricated loader or cross-site source attribution.
pub fn expand_observed_direct_bundle(
    bundle_root: &Path,
    executable: &Path,
) -> Result<Vec<ObservedEvalInput>> {
    let descriptor: DirectBundle =
        serde_json::from_slice(&read_observed_file(bundle_root, "bundle.json")?)?;
    anyhow::ensure!(
        descriptor.schema_version == 1 && descriptor.kind == "direct-eval-export-bundle",
        "unrecognized direct-eval export bundle"
    );
    anyhow::ensure!(
        is_sha256(&descriptor.executable_sha256) && is_sha256(&descriptor.capture_sha256),
        "invalid bundle original-source or capture SHA-256"
    );
    anyhow::ensure!(
        sha256_hex(&read_regular(executable)?) == descriptor.executable_sha256,
        "bundle executable SHA-256 mismatch"
    );
    anyhow::ensure!(
        !descriptor.sites.is_empty(),
        "direct-eval bundle has no source sites"
    );
    for (index, site) in descriptor.sites.iter().enumerate() {
        anyhow::ensure!(
            site.site_index == index,
            "nonsequential bundle source-site index"
        );
        anyhow::ensure!(
            site.eval_site.start < site.eval_site.end
                && site.eval_site.end - site.eval_site.start
                    == site.eval_site.expression.encode_utf16().count(),
            "invalid bundle source-site UTF-16 interval"
        );
    }
    let mut result = Vec::new();
    let mut previous = None;
    let mut global_event_indices = BTreeSet::new();
    let mut expected_event_count = 0usize;
    for capture in &descriptor.captures {
        anyhow::ensure!(
            previous.is_none_or(|prior| capture.site_index > prior),
            "duplicate or unordered observed source site"
        );
        previous = Some(capture.site_index);
        let site = descriptor
            .sites
            .get(capture.site_index)
            .context("observed site index outside configured source sites")?;
        anyhow::ensure!(
            capture.directory == format!("site-{:04}", capture.site_index)
                && capture.event_count > 0
                && site.event_count == capture.event_count
                && site.eval_site == capture.eval_site,
            "observed bundle site metadata mismatch"
        );
        let relative = format!("{}/manifest.json", capture.directory);
        let witness: Manifest =
            serde_json::from_slice(&read_observed_file(bundle_root, &relative)?)?;
        anyhow::ensure!(
            witness.schema_version == 3
                && witness.capture_sha256.as_deref() == Some(descriptor.capture_sha256.as_str())
                && witness.event_count == capture.event_count
                && witness.source_provenance.kind.as_deref() == Some("direct-executable")
                && witness
                    .source_provenance
                    .executable
                    .as_ref()
                    .is_some_and(|exe| exe.sha256 == descriptor.executable_sha256
                        && exe.eval_site == capture.eval_site),
            "direct-eval site witness disagrees with bundle"
        );
        expected_event_count = expected_event_count
            .checked_add(capture.event_count)
            .context("direct-eval event count overflow")?;
        let mut witnessed = 0usize;
        for entry in &witness.entries {
            let indices = entry
                .global_event_indices
                .as_deref()
                .context("multi-site witness missing global event indices")?;
            anyhow::ensure!(
                indices.len() == entry.occurrences
                    && indices.windows(2).all(|pair| pair[0] < pair[1]),
                "invalid multi-site source event ordering"
            );
            witnessed = witnessed
                .checked_add(entry.occurrences)
                .context("multi-site witness event count overflow")?;
            for index in indices {
                anyhow::ensure!(
                    global_event_indices.insert(*index),
                    "duplicate global event index across direct source sites"
                );
            }
        }
        anyhow::ensure!(
            witnessed == capture.event_count,
            "multi-site witness event counts do not account for the site"
        );
        result.push(ObservedEvalInput {
            observed_tree: bundle_root.join(&capture.directory),
            source_files: vec![executable.to_path_buf()],
        });
    }
    anyhow::ensure!(
        descriptor
            .sites
            .iter()
            .filter(|site| site.event_count > 0)
            .count()
            == result.len(),
        "bundle omits a source site with observed events"
    );
    anyhow::ensure!(
        !result.is_empty(),
        "direct-eval bundle contains no observed source events"
    );
    anyhow::ensure!(
        global_event_indices.len() == expected_event_count
            && global_event_indices
                .iter()
                .copied()
                .eq(0..expected_event_count),
        "multi-site witness global events are not a complete contiguous execution"
    );
    Ok(result)
}

struct PreparedCapture {
    manifest: Manifest,
    original_manifest: Vec<u8>,
    original_site: Site,
    capture_id: String,
    executable_sha256: String,
    executable_site: SourceSite,
    outer_loader: Option<OuterLoader>,
    stripped_leading_newline: Option<usize>,
    relative: String,
    entries: Vec<SourceEntry>,
    matches: Vec<AstMatch>,
    parse_failures: Vec<String>,
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

fn read_regular(path: &Path) -> Result<Vec<u8>> {
    let file_type = fs::symlink_metadata(path)
        .with_context(|| format!("checking {}", path.display()))?
        .file_type();
    anyhow::ensure!(
        file_type.is_file() && !file_type.is_symlink(),
        "expected a regular file: {}",
        path.display()
    );
    fs::read(path).with_context(|| format!("reading {}", path.display()))
}

/// Read one untrusted capture artifact without traversing symlinked
/// intermediate directories. The relative paths are content-derived names.
fn read_observed_file(root: &Path, relative: &str) -> Result<Vec<u8>> {
    use std::path::Component;
    let root_type = fs::symlink_metadata(root)
        .with_context(|| format!("checking observed source root {}", root.display()))?
        .file_type();
    anyhow::ensure!(
        root_type.is_dir() && !root_type.is_symlink(),
        "observed source root must be a real directory: {}",
        root.display()
    );
    let components = Path::new(relative).components().collect::<Vec<_>>();
    anyhow::ensure!(
        !components.is_empty() && components.iter().all(|c| matches!(c, Component::Normal(_))),
        "invalid observed artifact relative path"
    );
    let mut current = root.to_path_buf();
    for (index, component) in components.iter().enumerate() {
        current.push(component);
        if index + 1 == components.len() {
            return read_regular(&current);
        }
        let kind = fs::symlink_metadata(&current)
            .with_context(|| format!("checking observed directory {}", current.display()))?
            .file_type();
        anyhow::ensure!(
            kind.is_dir() && !kind.is_symlink(),
            "symlink or non-directory inside observed source tree: {}",
            current.display()
        );
    }
    anyhow::bail!("empty observed artifact path")
}

fn exact_site<'a>(code: &'a str, site: &SourceSite, expected: &str) -> Result<&'a str> {
    anyhow::ensure!(
        site.expression == expected,
        "unrecognized original source expression"
    );
    let start = utf16_to_bytes(code, site.start)? as usize;
    let end = utf16_to_bytes(code, site.end)? as usize;
    let observed = code
        .get(start..end)
        .context("source site is not a valid UTF-8 slice")?;
    anyhow::ensure!(observed == expected, "original source site mismatch");
    Ok(observed)
}

fn relative_link(from_file: &str, to_file: &str) -> String {
    let parent = Path::new(from_file)
        .parent()
        .unwrap_or_else(|| Path::new(""));
    let from = parent.components().collect::<Vec<_>>();
    let to = Path::new(to_file).components().collect::<Vec<_>>();
    let prefix = from.iter().zip(&to).take_while(|(a, b)| a == b).count();
    let mut parts = vec!["..".to_owned(); from.len() - prefix];
    parts.extend(
        to[prefix..]
            .iter()
            .map(|v| v.as_os_str().to_string_lossy().to_string()),
    );
    parts.join("/")
}

fn write_file(root: &Path, name: &str, bytes: &[u8]) -> Result<()> {
    let dest = root.join(name);
    if let Some(parent) = dest.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&dest, bytes).with_context(|| format!("writing {}", dest.display()))
}

fn scan_matches(output: &Path, original: &Site) -> Result<(Vec<AstMatch>, Vec<String>)> {
    let mut matches = Vec::new();
    let mut failures = Vec::new();
    for source in js_files(output)? {
        let relative = source
            .strip_prefix(output)?
            .to_string_lossy()
            .replace('\\', "/");
        let result = fs::read_to_string(&source)
            .with_context(|| format!("reading {}", source.display()))
            .and_then(|code| parse_sites_file(&code, &source));
        match result {
            Ok(sites) => {
                for site in sites {
                    if same_lexical_structure(original, &site) {
                        matches.push(AstMatch {
                            path: relative.clone(),
                            line: site.line,
                            byte_span: [site.start, site.end],
                            relation: "ast-lexical-structure-match",
                            lexical_frames: site.frames,
                        });
                    }
                }
            }
            Err(error) => failures.push(format!("{relative}: {error}")),
        }
    }
    Ok((matches, failures))
}

fn prepare_capture(output: &Path, input: &ObservedEvalInput) -> Result<PreparedCapture> {
    let original_manifest = read_observed_file(&input.observed_tree, "manifest.json")?;
    let mut manifest: Manifest = serde_json::from_slice(&original_manifest)?;
    anyhow::ensure!(
        matches!(manifest.schema_version, 2 | 3),
        "unsupported observed-eval provenance schema"
    );
    let p = &manifest.source_provenance;
    let direct = manifest.schema_version == 3;
    let capture_id = if direct {
        anyhow::ensure!(
            p.kind.as_deref() == Some("direct-executable")
                && p.executable.is_some()
                && p.outer_loader.is_none()
                && p.inner_executable.is_none()
                && manifest.html_sha256.is_none(),
            "invalid direct executable provenance"
        );
        manifest.capture_sha256.as_ref()
    } else {
        anyhow::ensure!(
            p.kind.is_none()
                && p.outer_loader.is_some()
                && p.inner_executable.is_some()
                && p.executable.is_none()
                && manifest.capture_sha256.is_none(),
            "invalid two-stage executable provenance"
        );
        manifest.html_sha256.as_ref()
    }
    .context("missing capture identity SHA-256")?
    .clone();
    anyhow::ensure!(is_sha256(&capture_id), "invalid capture identity SHA-256");
    anyhow::ensure!(
        manifest.entries.len() == manifest.unique_source_count,
        "unique observed-source count mismatch"
    );
    let expected_files = if direct { 1 } else { 2 };
    anyhow::ensure!(
        input.source_files.len() == expected_files,
        "observed source file count does not match provenance kind"
    );
    let (outer, executable_sha256, executable_site, stripped) = if direct {
        let exe = p
            .executable
            .as_ref()
            .context("missing original direct executable")?;
        (None, exe.sha256.clone(), exe.eval_site.clone(), None)
    } else {
        let outer = p.outer_loader.as_ref().context("missing outer loader")?;
        let inner = p
            .inner_executable
            .as_ref()
            .context("missing inner executable")?;
        anyhow::ensure!(
            outer.decoded_by == "observed-first-indirect-eval",
            "unrecognized loader decode provenance"
        );
        (
            Some(outer),
            inner.sha256.clone(),
            inner.eval_site.clone(),
            Some(inner.stripped_leading_newline_code_units),
        )
    };
    anyhow::ensure!(is_sha256(&executable_sha256), "invalid executable SHA-256");
    if let Some(outer) = outer {
        anyhow::ensure!(is_sha256(&outer.sha256), "invalid outer-loader SHA-256");
        let outer_bytes = read_regular(&input.source_files[0])?;
        anyhow::ensure!(
            sha256_hex(&outer_bytes) == outer.sha256,
            "outer-loader SHA-256 mismatch"
        );
        let code = String::from_utf8(outer_bytes)?;
        exact_site(&code, &outer.indirect_eval_site, "(0,eval)(")?;
    }
    let executable_path = input
        .source_files
        .last()
        .context("missing executable path")?;
    let bytes = read_regular(executable_path)?;
    anyhow::ensure!(
        sha256_hex(&bytes) == executable_sha256,
        "original executable SHA-256 mismatch"
    );
    let code = String::from_utf8(bytes)?;
    anyhow::ensure!(
        !executable_site.expression.is_empty(),
        "empty eval site expression"
    );
    exact_site(&code, &executable_site, &executable_site.expression)?;
    let start = utf16_to_bytes(&code, executable_site.start)?;
    let end = utf16_to_bytes(&code, executable_site.end)?;
    let original = parse_sites_file(&code, executable_path)?
        .into_iter()
        .find(|site| site.start == start && site.end == end)
        .context("source site is not an executable direct-eval AST node")?;
    anyhow::ensure!(
        original.eval_is_unresolved,
        "eval does not invoke the unresolved direct eval binding"
    );
    let (matches, parse_failures) = scan_matches(output, &original)?;

    let mut seen = BTreeSet::new();
    let mut counted = 0usize;
    let mut entries = Vec::new();
    for entry in std::mem::take(&mut manifest.entries) {
        anyhow::ensure!(is_sha256(&entry.sha256), "invalid generated-source SHA-256");
        anyhow::ensure!(
            seen.insert(entry.sha256.clone()),
            "duplicate observed source"
        );
        anyhow::ensure!(
            entry.raw_file == format!("raw/{}.txt", entry.sha256),
            "unexpected generated raw-source path"
        );
        anyhow::ensure!(
            entry
                .readable_file
                .as_deref()
                .is_none_or(|f| f == format!("readable/{}.js", entry.sha256)),
            "unexpected generated readable-source path"
        );
        anyhow::ensure!(
            entry.returned.saturating_add(entry.threw) == entry.occurrences,
            "invalid returned/thrown occurrence counts"
        );
        anyhow::ensure!(
            entry.first_event < manifest.event_count,
            "invalid observed event index"
        );
        if let Some(indices) = &entry.global_event_indices {
            anyhow::ensure!(
                indices.len() == entry.occurrences
                    && indices.windows(2).all(|pair| pair[0] < pair[1]),
                "invalid per-source global event sequence"
            );
        }
        counted = counted.saturating_add(entry.occurrences);
        let raw = read_observed_file(&input.observed_tree, &entry.raw_file)?;
        anyhow::ensure!(
            sha256_hex(&raw) == entry.sha256,
            "generated source SHA-256 mismatch"
        );
        anyhow::ensure!(
            std::str::from_utf8(&raw)?.encode_utf16().count() == entry.utf16_length,
            "generated source UTF-16 length mismatch"
        );
        let readable = entry
            .readable_file
            .as_ref()
            .map(|f| read_observed_file(&input.observed_tree, f))
            .transpose()?;
        entries.push(SourceEntry {
            meta: entry,
            raw,
            readable,
        });
    }
    anyhow::ensure!(
        counted == manifest.event_count,
        "observed event count mismatch"
    );
    let prefix = if let Some(loader) = outer {
        format!(
            "runtime-observed/loader-{}/executable-{}",
            loader.sha256, executable_sha256
        )
    } else {
        format!("runtime-observed/direct-{}", executable_sha256)
    };
    let relative = format!(
        "{prefix}/eval-{}-{}/capture-{}",
        executable_site.start, executable_site.end, capture_id
    );
    let outer_loader = outer.cloned();
    Ok(PreparedCapture {
        manifest,
        original_manifest,
        original_site: original,
        capture_id,
        executable_sha256,
        executable_site,
        outer_loader,
        stripped_leading_newline: stripped,
        relative,
        entries,
        matches,
        parse_failures,
    })
}

/// Attach verified observed source evidence without running sample JavaScript.
pub fn attach_observed_eval_sources(output: &Path, inputs: &[ObservedEvalInput]) -> Result<()> {
    if inputs.is_empty() {
        return Ok(());
    }
    anyhow::ensure!(output.is_dir(), "static source-tree output does not exist");
    anyhow::ensure!(
        !output.join("runtime-observed").exists(),
        "runtime-observed already exists"
    );
    let mut captures = Vec::new();
    let mut identities = BTreeSet::new();
    for input in inputs {
        let capture = prepare_capture(output, input)?;
        anyhow::ensure!(
            identities.insert(capture.relative.clone()),
            "duplicate observed capture"
        );
        captures.push(capture);
    }
    let staging = tempfile::tempdir_in(output)?;
    let mut index = String::from(
        "# Runtime-observed source\n\nExecution evidence only, not universal static recovery.\n\n",
    );
    let mut backlinks = BTreeMap::<String, Vec<(String, usize)>>::new();
    let mut records = Vec::new();
    for capture in &captures {
        let m = &capture.manifest;
        let outer = capture.outer_loader.as_ref();
        let executable_sha = &capture.executable_sha256;
        let site = &capture.executable_site;
        let origin = format!("{}/origin.md", capture.relative);
        let readme = format!("{}/README.md", capture.relative);
        let meta = json!({
            "schema":"js-redox/runtime-origin/v3",
            "evidence":"execution-observed, AST lexical site match, not full equivalence",
            "captureSha256":capture.capture_id,
            "sourceProvenance":m.source_provenance,
            "outerLoader":outer,
            "innerExecutable":m.source_provenance.inner_executable,
            "directExecutable":m.source_provenance.executable,
            "staticAstStructuralMatches":capture.matches,
            "originalEvalSite":capture.original_site,
            "staticParseFailures":capture.parse_failures,
            "eventCount":m.event_count,
            "uniqueSourceCount":m.unique_source_count,
            "truncated":m.truncated
        });
        write_file(
            staging.path(),
            &format!("{}/origin.json", capture.relative),
            serde_json::to_string_pretty(&meta)?.as_bytes(),
        )?;
        let mut origin_text = format!(
            "# Verified executable eval site\n\n\
             Execution-observed only; matches do not imply whole-function equivalence.\n\n\
             - Capture SHA-256: {}\n\
             - Original executable SHA-256: {}\n\
             - Executable direct eval interval: {}..{}\n",
            capture.capture_id, executable_sha, site.start, site.end,
        );
        if let Some(loader) = outer {
            origin_text.push_str(&format!(
                "- Outer loader SHA-256: {}\n\
                 - Loader indirect eval source interval: {}..{}\n\
                 - Stripped leading newline units: {}\n",
                loader.sha256,
                loader.indirect_eval_site.start,
                loader.indirect_eval_site.end,
                capture.stripped_leading_newline.unwrap_or(0)
            ));
        }
        origin_text.push_str("\n## AST lexical matches\n\n");
        for found in &capture.matches {
            origin_text.push_str(&format!(
                "- [{}]({}) (line {}, AST lexical structure)\n",
                found.path,
                relative_link(&origin, &found.path),
                found.line
            ));
            backlinks
                .entry(found.path.clone())
                .or_default()
                .push((origin.clone(), found.line));
        }
        if !capture.parse_failures.is_empty() {
            origin_text.push_str(&format!(
                "\nIncomplete static scan: {} files could not be parsed; see origin.json.\n",
                capture.parse_failures.len()
            ));
        }
        if capture.matches.is_empty() {
            origin_text.push_str("\nNo matching static lexical site was found.\n");
        }
        write_file(staging.path(), &origin, origin_text.as_bytes())?;
        let mut listing = String::from(
            "# Captured dynamic eval operands\n\n\
             Execution evidence, not static proofs. Callable values may be lexical lookups.\n\n\
             [Executable origin](origin.md) | [Machine-readable origin](origin.json)\n\n",
        );
        for entry in &capture.entries {
            let e = &entry.meta;
            let raw_name = format!("{}/raw/{}.txt", capture.relative, e.sha256);
            let page = format!("{}/entries/{}.md", capture.relative, e.sha256);
            write_file(staging.path(), &raw_name, &entry.raw)?;
            let mut details = format!(
                "# Captured eval input {}\n\nExecution evidence only.\n\n\
                 - [Executable eval origin]({})\n- [Exact raw source]({})\n\
                 - Source SHA-256: {}\n- UTF-16 length: {}\n\
                 - First observed event: {}\n- Occurrences: {} ({} returns, {} throws)\n\
                 - Returned types: {}\n- Thrown types: {}\n",
                &e.sha256[..16],
                relative_link(&page, &origin),
                relative_link(&page, &raw_name),
                e.sha256,
                e.utf16_length,
                e.first_event,
                e.occurrences,
                e.returned,
                e.threw,
                serde_json::to_string(&e.returned_types)?,
                serde_json::to_string(&e.thrown_types)?
            );
            if let Some(indices) = &e.global_event_indices {
                details.push_str(&format!(
                    "- Global execution event indices: {}\n",
                    serde_json::to_string(indices)?
                ));
            }
            if let Some(bytes) = &entry.readable {
                let fmt = format!("{}/readable/{}.js", capture.relative, e.sha256);
                write_file(staging.path(), &fmt, bytes)?;
                details.push_str(&format!(
                    "- [Readable analyst view]({})\n",
                    relative_link(&page, &fmt)
                ));
            } else {
                details.push_str(&format!(
                    "- Standalone formatter status: {}\n",
                    e.readable_status
                ));
            }
            write_file(staging.path(), &page, details.as_bytes())?;
            listing.push_str(&format!(
                "- [{}]({}) - {} source units, {} event(s)\n",
                &e.sha256[..16],
                relative_link(&readme, &page),
                e.utf16_length,
                e.occurrences
            ));
        }
        write_file(staging.path(), &readme, listing.as_bytes())?;
        // Preserve the complete externally captured manifest byte-for-byte:
        // parsed typed fields validate it, while upstream may carry additional
        // provenance fields such as environment and evidenceKind.
        write_file(
            staging.path(),
            &format!("{}/manifest.json", capture.relative),
            &capture.original_manifest,
        )?;
        let label = if let Some(loader) = outer {
            format!(
                "Outer {} / executable {}",
                &loader.sha256[..12],
                &executable_sha[..12]
            )
        } else {
            format!("Direct executable {}", &executable_sha[..12])
        };
        index.push_str(&format!(
            "- [{label} / eval {}..{} / capture {}]({}) - {} calls, {} strings\n",
            site.start,
            site.end,
            &capture.capture_id[..12],
            relative_link("runtime-observed/README.md", &readme),
            m.event_count,
            m.unique_source_count
        ));
        let mut record = json!({
            "captureSha256":capture.capture_id,
            "executableSha256":executable_sha,
            "directory":capture.relative,
            "executableSite":[site.start,site.end],
            "calls":m.event_count,
            "sources":m.unique_source_count,
            "staticAstMatches":capture.matches.len(),
            "staticParseFailures":capture.parse_failures.len(),
            "truncated":m.truncated,
            "provenanceKind":if outer.is_some() {"two-stage"} else {"direct"},
        });
        if let Some(loader) = outer {
            record["outerLoaderSha256"] = json!(loader.sha256);
            record["loaderSite"] = json!([
                loader.indirect_eval_site.start,
                loader.indirect_eval_site.end
            ]);
            record["innerExecutableSha256"] = json!(executable_sha);
        } else {
            record["directExecutableSha256"] = json!(executable_sha);
        }
        records.push(record);
    }
    write_file(
        staging.path(),
        "runtime-observed/README.md",
        index.as_bytes(),
    )?;
    write_file(
        staging.path(),
        "runtime-observed/index.json",
        serde_json::to_string_pretty(&json!({
            "schema":"js-redox/linked-runtime-source-tree/v3",
            "staticJavaScriptAndReconstructionUnmodified":true,
            "captures":records
        }))?
        .as_bytes(),
    )?;
    let mut sidecars = Vec::new();
    for (source, refs) in backlinks {
        let sidecar = format!("{source}.runtime-evidence.md");
        let mut text = format!(
            "# AST-linked runtime observations for {source}\n\n\
             Lexical structural matches, not whole-function equivalence.\n\n"
        );
        for (origin, line) in refs {
            text.push_str(&format!(
                "- Line {}: [verified observed eval origin]({})\n",
                line,
                relative_link(&sidecar, &origin)
            ));
        }
        sidecars.push((sidecar, text));
    }
    fs::rename(
        staging.path().join("runtime-observed"),
        output.join("runtime-observed"),
    )?;
    for (name, bytes) in sidecars {
        write_file(output, &name, bytes.as_bytes())?;
    }
    let root_index = output.join("README.md");
    let mut source_index = fs::read_to_string(&root_index)?;
    source_index.push_str(
        "\n## Execution-observed generated JavaScript\n\n\
         [Browse AST-linked runtime evidence](runtime-observed/README.md). \
         This does not replace universally valid static source.\n",
    );
    fs::write(root_index, source_index)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(root: &Path) -> Result<(PathBuf, ObservedEvalInput)> {
        let output = root.join("static");
        fs::create_dir_all(&output)?;
        fs::write(output.join("README.md"), "# Static source\n")?;
        fs::write(output.join("reconstruction.json"), "{\"source_count\":1}\n")?;
        let static_code = "const oU = function(D) { return eval( D ); };\n";
        fs::write(output.join("original.js"), static_code)?;

        let outer_code = "const x=(0,eval)(payload);\n";
        let inner_code = "const oU=function(D){return eval(D)};\n";
        let outer_source = root.join("outer.js");
        let inner_source = root.join("inner.js");
        fs::write(&outer_source, outer_code)?;
        fs::write(&inner_source, inner_code)?;
        let outer_start = outer_code
            .find("(0,eval)(")
            .context("missing outer invocation")?;
        let inner_start = inner_code
            .find("eval(D)")
            .context("missing inner invocation")?;

        let observed_tree = root.join("observed");
        fs::create_dir_all(observed_tree.join("raw"))?;
        fs::create_dir_all(observed_tree.join("readable"))?;
        let raw = "0,(function(x){return x+1})";
        let hash = sha256_hex(raw.as_bytes());
        fs::write(observed_tree.join(format!("raw/{hash}.txt")), raw)?;
        fs::write(
            observed_tree.join(format!("readable/{hash}.js")),
            "0, (function(x) { return x + 1; });\n",
        )?;
        let manifest = json!({
            "schemaVersion":2,
            "evidenceKind":"execution-observed",
            "environment":{"model":"archived browser replay","runner":"node"},
            "htmlSha256":"a".repeat(64),
            "sourceProvenance":{
                "outerLoader":{
                    "sha256":sha256_hex(outer_code.as_bytes()),
                    "decodedBy":"observed-first-indirect-eval",
                    "indirectEvalSite":{
                        "start":outer_start,"end":outer_start+9,"expression":"(0,eval)("
                    }
                },
                "innerExecutable":{
                    "sha256":sha256_hex(inner_code.as_bytes()),
                    "strippedLeadingNewlineCodeUnits":42,
                    "evalSite":{
                        "start":inner_start,"end":inner_start+7,"expression":"eval(D)"
                    }
                }
            },
            "truncated":false,
            "eventCount":2,
            "uniqueSourceCount":1,
            "entries":[{
                "sha256":hash,
                "utf16Length":raw.len(),
                "firstEvent":0,"occurrences":2,"returned":2,"threw":0,
                "returnedTypes":{"function":2},"thrownTypes":{},
                "rawFile":format!("raw/{hash}.txt"),
                "readableFile":format!("readable/{hash}.js"),
                "readableStatus":"formatted"
            }]
        });
        fs::write(
            observed_tree.join("manifest.json"),
            serde_json::to_string(&manifest)?,
        )?;
        Ok((
            output,
            ObservedEvalInput {
                observed_tree,
                source_files: vec![outer_source, inner_source],
            },
        ))
    }

    #[test]
    fn direct_bundle_expansion_checks_site_identity_and_complete_coverage() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let (_out, input) = sample(tmp.path())?;
        let original = input.source_files[1].clone();
        let root = tmp.path().join("bundle");
        fs::create_dir_all(root.join("site-0000"))?;
        let old: serde_json::Value =
            serde_json::from_slice(&fs::read(input.observed_tree.join("manifest.json"))?)?;
        let exe = old["sourceProvenance"]["innerExecutable"].clone();
        let capture_id = "c".repeat(64);
        let witness = json!({
            "schemaVersion":3,
            "captureSha256":capture_id,
            "sourceProvenance":{
                "kind":"direct-executable",
                "executable":{"sha256":exe["sha256"],"evalSite":exe["evalSite"]}
            },
            "truncated":false,"eventCount":2,"uniqueSourceCount":1,
            "entries":[{
                "sha256":"f".repeat(64),"utf16Length":2,"firstEvent":0,
                "occurrences":2,"returned":2,"threw":0,
                "returnedTypes":{"number":2},"thrownTypes":{},
                "rawFile":"raw/".to_owned() + &"f".repeat(64) + ".txt",
                "readableFile":null,"readableStatus":"standalone-parse-rejected",
                "globalEventIndices":[0,1]
            }]
        });
        fs::write(
            root.join("site-0000/manifest.json"),
            serde_json::to_vec(&witness)?,
        )?;
        let descriptor = json!({
            "schemaVersion":1,
            "kind":"direct-eval-export-bundle",
            "captureSha256":capture_id,
            "executableSha256":exe["sha256"],
            "sites":[
                {"siteIndex":0,"evalSite":exe["evalSite"],"eventCount":2},
                {"siteIndex":1,"evalSite":{"start":0,"end":7,"expression":"eval(D)"},
                 "eventCount":0}
            ],
            "captures":[
                {"siteIndex":0,"directory":"site-0000",
                 "evalSite":exe["evalSite"],"eventCount":2}
            ],
        });
        let bundle = root.join("bundle.json");
        fs::write(&bundle, serde_json::to_vec(&descriptor)?)?;
        let expanded = expand_observed_direct_bundle(&root, &original)?;
        assert_eq!(expanded.len(), 1);
        assert_eq!(expanded[0].observed_tree, root.join("site-0000"));
        assert_eq!(expanded[0].source_files, vec![original.clone()]);

        let mut altered = descriptor.clone();
        altered["captures"][0]["siteIndex"] = json!(1);
        fs::write(&bundle, serde_json::to_vec(&altered)?)?;
        assert!(expand_observed_direct_bundle(&root, &original).is_err());
        altered = descriptor.clone();
        altered["sites"][1]["eventCount"] = json!(1);
        fs::write(&bundle, serde_json::to_vec(&altered)?)?;
        assert!(expand_observed_direct_bundle(&root, &original).is_err());
        altered = descriptor.clone();
        altered["captures"][0]["directory"] = json!("../escape");
        fs::write(&bundle, serde_json::to_vec(&altered)?)?;
        assert!(expand_observed_direct_bundle(&root, &original).is_err());
        altered = descriptor.clone();
        altered["captures"][0]["eventCount"] = json!(999);
        fs::write(&bundle, serde_json::to_vec(&altered)?)?;
        assert!(expand_observed_direct_bundle(&root, &original).is_err());
        Ok(())
    }

    #[test]
    fn direct_executable_v3_links_single_original_source() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let (out, mut input) = sample(tmp.path())?;
        let old_original = fs::read(out.join("original.js"))?;
        let old_reconstruction = fs::read(out.join("reconstruction.json"))?;
        input.source_files.remove(0);
        let manifest_path = input.observed_tree.join("manifest.json");
        let mut manifest: serde_json::Value = serde_json::from_slice(&fs::read(&manifest_path)?)?;
        let exe = manifest["sourceProvenance"]["innerExecutable"].clone();
        manifest["schemaVersion"] = json!(3);
        manifest["captureSha256"] = manifest["htmlSha256"].take();
        manifest
            .as_object_mut()
            .context("not an object")?
            .remove("htmlSha256");
        manifest["sourceProvenance"] = json!({
            "kind":"direct-executable",
            "executable":{"sha256":exe["sha256"],"evalSite":exe["evalSite"]}
        });
        fs::write(&manifest_path, serde_json::to_vec(&manifest)?)?;
        let original_manifest = fs::read(&manifest_path)?;

        attach_observed_eval_sources(&out, std::slice::from_ref(&input))?;
        assert_eq!(old_original, fs::read(out.join("original.js"))?);
        assert_eq!(
            old_reconstruction,
            fs::read(out.join("reconstruction.json"))?
        );
        let index: serde_json::Value =
            serde_json::from_slice(&fs::read(out.join("runtime-observed/index.json"))?)?;
        assert_eq!(index["schema"], "js-redox/linked-runtime-source-tree/v3");
        assert_eq!(index["captures"][0]["provenanceKind"], "direct");
        assert_eq!(index["captures"][0]["calls"], 2);
        assert_eq!(index["captures"][0]["staticAstMatches"], 1);
        let directory = index["captures"][0]["directory"]
            .as_str()
            .context("missing direct capture path")?;
        assert!(directory.starts_with("runtime-observed/direct-"));
        assert_eq!(
            original_manifest,
            fs::read(out.join(directory).join("manifest.json"))?
        );
        let origin: serde_json::Value =
            serde_json::from_slice(&fs::read(out.join(directory).join("origin.json"))?)?;
        assert_eq!(origin["sourceProvenance"]["kind"], "direct-executable");
        assert!(origin["outerLoader"].is_null());
        assert!(origin["staticAstStructuralMatches"]
            .as_array()
            .is_some_and(|a| !a.is_empty()));
        Ok(())
    }

    #[test]
    fn direct_manifest_rejects_fake_loader_and_wrong_source_count() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let (out, mut input) = sample(tmp.path())?;
        let file = input.observed_tree.join("manifest.json");
        let mut manifest: serde_json::Value = serde_json::from_slice(&fs::read(&file)?)?;
        let exe = manifest["sourceProvenance"]["innerExecutable"].clone();
        manifest["schemaVersion"] = json!(3);
        manifest["captureSha256"] = manifest["htmlSha256"].take();
        manifest
            .as_object_mut()
            .context("not an object")?
            .remove("htmlSha256");
        manifest["sourceProvenance"] = json!({
            "kind":"direct-executable",
            "executable":{"sha256":exe["sha256"],"evalSite":exe["evalSite"]}
        });
        fs::write(&file, serde_json::to_vec(&manifest)?)?;
        assert!(attach_observed_eval_sources(&out, std::slice::from_ref(&input)).is_err());
        input.source_files.remove(0);
        manifest["sourceProvenance"]["outerLoader"] = json!({"sha256":"f".repeat(64)});
        fs::write(&file, serde_json::to_vec(&manifest)?)?;
        assert!(attach_observed_eval_sources(&out, std::slice::from_ref(&input)).is_err());
        assert!(!out.join("runtime-observed").exists());
        Ok(())
    }

    #[test]
    fn source_overlay_has_dual_provenance_and_preserves_static_output() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let (out, input) = sample(tmp.path())?;
        let original = fs::read(out.join("original.js"))?;
        let reconstruction = fs::read(out.join("reconstruction.json"))?;
        let witness_manifest = fs::read(input.observed_tree.join("manifest.json"))?;

        attach_observed_eval_sources(&out, std::slice::from_ref(&input))?;
        assert_eq!(original, fs::read(out.join("original.js"))?);
        assert_eq!(reconstruction, fs::read(out.join("reconstruction.json"))?);

        let root_index: serde_json::Value =
            serde_json::from_slice(&fs::read(out.join("runtime-observed/index.json"))?)?;
        assert_eq!(
            root_index["schema"],
            "js-redox/linked-runtime-source-tree/v3"
        );
        assert_eq!(root_index["captures"][0]["staticAstMatches"], 1);
        assert_eq!(root_index["captures"][0]["sources"], 1);
        let rel = root_index["captures"][0]["directory"]
            .as_str()
            .context("missing captured source directory")?;
        assert_eq!(
            witness_manifest,
            fs::read(out.join(rel).join("manifest.json"))?
        );
        let relative = root_index["captures"][0]["directory"]
            .as_str()
            .context("missing generated capture directory")?;
        let origin: serde_json::Value =
            serde_json::from_slice(&fs::read(out.join(relative).join("origin.json"))?)?;
        assert_eq!(
            origin["innerExecutable"]["evalSite"]["expression"],
            "eval(D)"
        );
        assert_eq!(
            origin["staticAstStructuralMatches"][0]["path"],
            "original.js"
        );
        assert!(out.join("original.js.runtime-evidence.md").exists());
        assert!(fs::read_to_string(out.join("README.md"))?.contains("runtime-observed/README.md"));
        let error = attach_observed_eval_sources(&out, &[input]);
        assert!(error.is_err(), "output overwrite must not succeed");
        Ok(())
    }

    #[test]
    fn invalid_provenance_is_rejected_without_publishing_overlay() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let (out, input) = sample(tmp.path())?;
        fs::write(&input.source_files[1], "tampered VM source")?;
        let result = attach_observed_eval_sources(&out, std::slice::from_ref(&input));
        assert!(
            result.is_err(),
            "mismatched executable source must be rejected"
        );
        assert!(!out.join("runtime-observed").exists());

        let (_, another) = sample(tmp.path())?;
        let manifest_file = another.observed_tree.join("manifest.json");
        let mut manifest: serde_json::Value = serde_json::from_slice(&fs::read(&manifest_file)?)?;
        manifest["schemaVersion"] = json!(1);
        fs::write(&manifest_file, serde_json::to_vec(&manifest)?)?;
        let result = attach_observed_eval_sources(&out, &[another]);
        assert!(result.is_err(), "legacy v1 manifest must be rejected");
        assert!(!out.join("runtime-observed").exists());
        Ok(())
    }

    #[test]
    fn count_mismatch_is_rejected_without_emitting_evidence() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let (output, input) = sample(temp.path())?;
        let manifest_path = input.observed_tree.join("manifest.json");
        let mut manifest: serde_json::Value = serde_json::from_slice(&fs::read(&manifest_path)?)?;
        manifest["eventCount"] = json!(3);
        fs::write(&manifest_path, serde_json::to_vec(&manifest)?)?;
        assert!(attach_observed_eval_sources(&output, &[input]).is_err());
        assert!(!output.join("runtime-observed").exists());
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn observed_source_directory_symlinks_are_not_followed() -> Result<()> {
        use std::os::unix::fs::symlink;
        let temp = tempfile::tempdir()?;
        let (output, input) = sample(temp.path())?;
        let real = temp.path().join("original-raw");
        fs::rename(input.observed_tree.join("raw"), &real)?;
        symlink(&real, input.observed_tree.join("raw"))?;
        assert!(attach_observed_eval_sources(&output, &[input]).is_err());
        assert!(!output.join("runtime-observed").exists());
        Ok(())
    }

    #[test]
    fn arrow_parameter_is_a_first_class_lexical_eval_binding() -> Result<()> {
        let original = "const oU = (D) => eval(D);";
        let formatted = "const oU = D => { return eval ( D ); };";
        let original_sites = parse_sites(original)?;
        let formatted_sites = parse_sites(formatted)?;
        assert_eq!(original_sites.len(), 1);
        assert_eq!(formatted_sites.len(), 1);
        let a = &original_sites[0];
        let b = &formatted_sites[0];
        assert!(a.eval_is_unresolved && a.argument_uses_nearest_formal_parameter);
        assert_eq!(a.frames.len(), 1);
        assert_eq!(a.frames[0].kind, "arrow");
        assert_eq!(a.frames[0].binding.as_deref(), Some("oU"));
        assert!(same_lexical_structure(a, b));
        Ok(())
    }

    #[test]
    fn nested_arrows_preserve_nearest_parameter_and_function_kind() -> Result<()> {
        let original = "const oU = (A) => (D) => eval(D);";
        let formatted = "const oU = A => { return D => eval(D); };";
        let sites = parse_sites(original)?;
        let formatted_sites = parse_sites(formatted)?;
        assert_eq!(sites.len(), 1);
        assert!(sites[0].argument_uses_nearest_formal_parameter);
        assert_eq!(sites[0].frames.len(), 2);
        assert!(sites[0].frames.iter().all(|frame| frame.kind == "arrow"));
        assert!(same_lexical_structure(&sites[0], &formatted_sites[0]));

        let captured_outer = parse_sites("const oU = (D) => { return () => eval(D); };")?;
        assert_eq!(captured_outer.len(), 1);
        assert!(!captured_outer[0].argument_uses_nearest_formal_parameter);
        assert!(!same_lexical_structure(&sites[0], &captured_outer[0]));
        Ok(())
    }

    #[test]
    fn arrow_and_function_expressions_are_not_the_same_lexical_structure() -> Result<()> {
        let arrow = parse_sites("const oU = (D) => eval(D);")?;
        let function = parse_sites("const oU = function(D) { return eval(D); };")?;
        assert!(arrow[0].argument_uses_nearest_formal_parameter);
        assert!(function[0].argument_uses_nearest_formal_parameter);
        assert!(!same_lexical_structure(&arrow[0], &function[0]));

        let shadowed = parse_sites("const oU = D => { const eval = x => x; return eval(D); };")?;
        assert_eq!(shadowed.len(), 1);
        assert!(!shadowed[0].eval_is_unresolved);
        assert!(!same_lexical_structure(&arrow[0], &shadowed[0]));

        let indirect = parse_sites("const oU = D => (0,eval)(D);")?;
        assert!(
            indirect.is_empty(),
            "indirect eval is not a direct eval callsite"
        );
        Ok(())
    }

    #[test]
    fn full_observed_import_supports_an_arrow_lexical_site() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let (output, input) = sample(tmp.path())?;
        let inner = "const oU = (D) => eval(D);\n";
        fs::write(&input.source_files[1], inner)?;
        fs::write(
            output.join("original.js"),
            "const oU = D => { return eval(D); };\n",
        )?;
        let manifest_file = input.observed_tree.join("manifest.json");
        let mut manifest: serde_json::Value = serde_json::from_slice(&fs::read(&manifest_file)?)?;
        manifest["sourceProvenance"]["innerExecutable"]["sha256"] =
            json!(sha256_hex(inner.as_bytes()));
        let start = inner
            .find("eval(D)")
            .context("missing eval in arrow source")?;
        manifest["sourceProvenance"]["innerExecutable"]["evalSite"]["start"] = json!(start);
        manifest["sourceProvenance"]["innerExecutable"]["evalSite"]["end"] = json!(start + 7);
        fs::write(&manifest_file, serde_json::to_vec(&manifest)?)?;

        attach_observed_eval_sources(&output, &[input])?;
        let index: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join("runtime-observed/index.json"))?)?;
        assert_eq!(index["captures"][0]["staticAstMatches"], 1);
        let relative = index["captures"][0]["directory"]
            .as_str()
            .context("missing observed capture directory")?;
        let origin: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join(relative).join("origin.json"))?)?;
        assert_eq!(
            origin["staticAstStructuralMatches"][0]["lexicalFrames"][0]["kind"],
            "arrow"
        );
        assert_eq!(
            origin["staticAstStructuralMatches"][0]["path"],
            "original.js"
        );
        Ok(())
    }

    #[test]
    fn arbitrary_eval_arguments_are_compared_by_expression_and_lexical_roles() -> Result<()> {
        let original = parse_sites("const oU = (D) => eval(D + String(D) + suffix);")?;
        let formatted = parse_sites("const oU = D => { return eval( D+String( D )+suffix ); };")?;
        assert_eq!(original.len(), 1);
        assert_eq!(formatted.len(), 1);
        assert!(original[0].eval_is_unresolved);
        assert!(original[0].argument_uses_nearest_formal_parameter);
        assert!(same_lexical_structure(&original[0], &formatted[0]));
        assert_eq!(original[0].argument_references.len(), 4);
        assert_eq!(original[0].argument_references[0].role, "formal:0:0");
        assert_eq!(original[0].argument_references[1].role, "unresolved");
        assert_eq!(original[0].argument_references[2].role, "formal:0:0");
        assert_eq!(original[0].argument_references[3].role, "unresolved");

        let shadowed =
            parse_sites("const suffix = 'x'; const oU = D => eval(D + String(D) + suffix);")?;
        assert!(!same_lexical_structure(&original[0], &shadowed[0]));

        let changed = parse_sites("const oU = D => eval(D + String(D) + another);")?;
        assert!(!same_lexical_structure(&original[0], &changed[0]));

        let simple = parse_sites("const oU = D => eval(D);")?;
        assert!(!same_lexical_structure(&simple[0], &original[0]));
        Ok(())
    }

    #[test]
    fn eval_argument_cardinality_and_spread_shape_affect_site_identity() -> Result<()> {
        let one = parse_sites("const oU = D => eval(D);")?;
        let two = parse_sites("const oU = D => eval(D, 1);")?;
        let other = parse_sites("const oU = D => eval(D, 2);")?;
        let spread = parse_sites("const oU = D => eval(...D);")?;
        assert_eq!(one.len(), 1);
        assert_eq!(two.len(), 1);
        assert_eq!(spread.len(), 1);
        assert!(!same_lexical_structure(&one[0], &two[0]));
        assert!(!same_lexical_structure(&two[0], &other[0]));
        assert!(!same_lexical_structure(&one[0], &spread[0]));
        let sequence = parse_sites("const oU = D => eval((D, extra));")?;
        let multiple = parse_sites("const oU = D => eval(D, extra);")?;
        assert_eq!(sequence[0].argument_shapes.len(), 1);
        assert_eq!(multiple[0].argument_shapes.len(), 2);
        assert!(!same_lexical_structure(&sequence[0], &multiple[0]));

        let optional = parse_sites("const oU = D => eval?.(D);")?;
        assert!(optional.is_empty(), "optional eval is not direct eval");
        Ok(())
    }

    #[test]
    fn script_and_module_sources_are_parsed_with_their_own_source_types() -> Result<()> {
        let module =
            "import { prefix } from './strings.mjs'; export const oU = (D) => eval(prefix + D);";
        let module_sites = parse_sites_file(module, Path::new("original.mjs"))?;
        assert_eq!(module_sites.len(), 1);
        assert_eq!(module_sites[0].argument_references.len(), 2);
        assert_eq!(module_sites[0].argument_references[0].role, "import");
        assert_eq!(module_sites[0].argument_references[1].role, "formal:0:0");

        let js = "import { prefix } from './strings.js'; export const oU = (D) => eval(prefix+D);";
        let js_sites = parse_sites_file(js, Path::new("original.js"))?;
        assert!(same_lexical_structure(&module_sites[0], &js_sites[0]));
        let locally_defined = "const prefix = 'x'; export const oU = (D) => eval(prefix+D);";
        let local_sites = parse_sites_file(locally_defined, Path::new("local.mjs"))?;
        assert_eq!(local_sites[0].argument_references[0].role, "const");
        assert!(!same_lexical_structure(&module_sites[0], &local_sites[0]));

        let cjs = "const oU = (D) => eval(D);";
        assert_eq!(parse_sites_file(cjs, Path::new("original.cjs"))?.len(), 1);
        assert_eq!(parse_sites_file(cjs, Path::new("original.js"))?.len(), 1);
        Ok(())
    }

    #[test]
    fn utf16_source_offsets_reject_surrogate_midpoints() -> Result<()> {
        let source = "const marker = '🦀'; const oU = D => eval(D);";
        let position = source.find('🦀').context("missing non-BMP fixture")?;
        let start = source[..position].encode_utf16().count();
        assert_eq!(utf16_to_bytes(source, start)? as usize, position);
        assert!(utf16_to_bytes(source, start + 1).is_err());
        assert_eq!(
            utf16_to_bytes(source, start + 2)? as usize,
            position + '🦀'.len_utf8()
        );
        Ok(())
    }

    #[test]
    fn full_v2_import_works_with_complex_module_eval_source() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let (output, input) = sample(temp.path())?;
        let module = "const emoji = '🦀'; export const oU = D => eval(D + String(D));\n";
        let static_module = "export const oU = (D) => eval( D+String( D ) );\n";
        fs::write(&input.source_files[1], module)?;
        fs::remove_file(output.join("original.js"))?;
        fs::write(output.join("original.mjs"), static_module)?;

        let manifest_file = input.observed_tree.join("manifest.json");
        let mut manifest: serde_json::Value = serde_json::from_slice(&fs::read(&manifest_file)?)?;
        manifest["sourceProvenance"]["innerExecutable"]["sha256"] =
            json!(sha256_hex(module.as_bytes()));
        let expression = "eval(D + String(D))";
        let byte_start = module
            .find(expression)
            .context("missing complex eval callsite")?;
        let start = module[..byte_start].encode_utf16().count();
        assert!(
            byte_start > start,
            "non-BMP prefix must change UTF-16 versus UTF-8 offsets"
        );
        manifest["sourceProvenance"]["innerExecutable"]["evalSite"]["start"] = json!(start);
        manifest["sourceProvenance"]["innerExecutable"]["evalSite"]["end"] =
            json!(start + expression.encode_utf16().count());
        manifest["sourceProvenance"]["innerExecutable"]["evalSite"]["expression"] =
            json!(expression);
        fs::write(&manifest_file, serde_json::to_vec(&manifest)?)?;

        attach_observed_eval_sources(&output, &[input])?;
        let index: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join("runtime-observed/index.json"))?)?;
        assert_eq!(index["captures"][0]["staticAstMatches"], 1);
        let relative = index["captures"][0]["directory"]
            .as_str()
            .context("missing combined source-tree capture")?;
        let origin: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join(relative).join("origin.json"))?)?;
        assert_eq!(
            origin["staticAstStructuralMatches"][0]["path"],
            "original.mjs"
        );
        assert!(origin["originalEvalSite"]["argument"]
            .as_str()
            .context("missing argument canonical form")?
            .contains("String"));
        assert_eq!(
            origin["originalEvalSite"]["argumentReferences"][0]["role"],
            "formal:0:0"
        );
        Ok(())
    }

    #[test]
    fn structural_match_needs_original_lexical_binding() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let (out, input) = sample(tmp.path())?;
        fs::write(
            out.join("original.js"),
            "const oU=function(D){const eval=x=>x;return eval(D)};",
        )?;
        attach_observed_eval_sources(&out, &[input])?;
        let index: serde_json::Value =
            serde_json::from_slice(&fs::read(out.join("runtime-observed/index.json"))?)?;
        assert_eq!(index["captures"][0]["staticAstMatches"], 0);
        Ok(())
    }
}
