//! Execution-conditioned, AST-linked source evidence for static source trees.
use crate::sha256_hex;
use anyhow::{bail, Context, Result};
use oxc_allocator::Allocator;
use oxc_ast::ast::{BindingPattern, CallExpression, Expression, Function, VariableDeclarator};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::SourceType;
use oxc_syntax::{scope::ScopeFlags, symbol::SymbolId};
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

/// One independently captured execution and both exact original source layers.
#[derive(Clone, Debug)]
pub struct ObservedEvalInput {
    pub observed_tree: PathBuf,
    pub outer_source: PathBuf,
    pub inner_source: PathBuf,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Manifest {
    schema_version: u32,
    html_sha256: String,
    source_provenance: SourceProvenance,
    truncated: bool,
    event_count: usize,
    unique_source_count: usize,
    entries: Vec<ObservedEntry>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SourceProvenance {
    outer_loader: OuterLoader,
    inner_executable: InnerExecutable,
}

#[derive(Deserialize, Serialize)]
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

#[derive(Deserialize, Serialize)]
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

struct PreparedCapture {
    manifest: Manifest,
    original_manifest: Vec<u8>,
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
            .and_then(|code| parse_sites(&code));
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
        manifest.schema_version == 2,
        "only dual-layer observed-eval manifest v2 is accepted"
    );
    anyhow::ensure!(
        is_sha256(&manifest.html_sha256),
        "invalid capture HTML SHA-256"
    );
    anyhow::ensure!(
        manifest.entries.len() == manifest.unique_source_count,
        "unique observed-source count mismatch"
    );
    let outer = &manifest.source_provenance.outer_loader;
    let inner = &manifest.source_provenance.inner_executable;
    anyhow::ensure!(
        is_sha256(&outer.sha256) && is_sha256(&inner.sha256),
        "invalid outer/inner code SHA-256"
    );
    anyhow::ensure!(
        outer.decoded_by == "observed-first-indirect-eval",
        "unrecognized loader decode provenance"
    );
    let outer_bytes = read_regular(&input.outer_source)?;
    let inner_bytes = read_regular(&input.inner_source)?;
    anyhow::ensure!(
        sha256_hex(&outer_bytes) == outer.sha256,
        "outer loader SHA-256 mismatch"
    );
    anyhow::ensure!(
        sha256_hex(&inner_bytes) == inner.sha256,
        "inner executable SHA-256 mismatch"
    );
    let outer_code = String::from_utf8(outer_bytes)?;
    let inner_code = String::from_utf8(inner_bytes)?;
    exact_site(&outer_code, &outer.indirect_eval_site, "(0,eval)(")?;
    exact_site(&inner_code, &inner.eval_site, "eval(D)")?;
    let start = utf16_to_bytes(&inner_code, inner.eval_site.start)?;
    let end = utf16_to_bytes(&inner_code, inner.eval_site.end)?;
    let original = parse_sites(&inner_code)?
        .into_iter()
        .find(|site| site.start == start && site.end == end)
        .context("inner source position is not an executable direct-eval AST node")?;
    anyhow::ensure!(
        original.eval_is_unresolved && original.argument_is_bound_to_nearest_parameter,
        "inner eval is not an unresolved direct eval of its own formal parameter"
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
    let relative = format!(
        "runtime-observed/loader-{}/inner-{}/eval-{}-{}/capture-{}",
        outer.sha256,
        inner.sha256,
        inner.eval_site.start,
        inner.eval_site.end,
        manifest.html_sha256
    );
    Ok(PreparedCapture {
        manifest,
        original_manifest,
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
        let outer = &m.source_provenance.outer_loader;
        let inner = &m.source_provenance.inner_executable;
        let origin = format!("{}/origin.md", capture.relative);
        let readme = format!("{}/README.md", capture.relative);
        let meta = json!({
            "schema":"js-redox/runtime-origin/v2",
            "evidence":"execution-observed, AST lexical site match, not full equivalence",
            "htmlSha256":m.html_sha256,
            "outerLoader":outer,
            "innerExecutable":inner,
            "staticAstStructuralMatches":capture.matches,
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
             - HTML SHA-256: {}\n- Outer loader SHA-256: {}\n\
             - Loader indirect eval source interval: {}..{}\n\
             - Inner executable SHA-256: {}\n\
             - Executable direct eval interval: {}..{}\n\
             - Normalized leading newline code units: {}\n\n\
             ## AST lexical matches\n\n",
            m.html_sha256,
            outer.sha256,
            outer.indirect_eval_site.start,
            outer.indirect_eval_site.end,
            inner.sha256,
            inner.eval_site.start,
            inner.eval_site.end,
            inner.stripped_leading_newline_code_units
        );
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
        index.push_str(&format!(
            "- [Outer {} / inner {} / eval {}..{} / capture {}]({}) - {} calls, {} strings\n",
            &outer.sha256[..12],
            &inner.sha256[..12],
            inner.eval_site.start,
            inner.eval_site.end,
            &m.html_sha256[..12],
            relative_link("runtime-observed/README.md", &readme),
            m.event_count,
            m.unique_source_count
        ));
        records.push(json!({
            "outerLoaderSha256":outer.sha256,"innerExecutableSha256":inner.sha256,
            "htmlSha256":m.html_sha256,"directory":capture.relative,
            "loaderSite":[outer.indirect_eval_site.start,outer.indirect_eval_site.end],
            "executableSite":[inner.eval_site.start,inner.eval_site.end],
            "calls":m.event_count,"sources":m.unique_source_count,
            "staticAstMatches":capture.matches.len(),
            "staticParseFailures":capture.parse_failures.len(),
            "truncated":m.truncated
        }));
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
            "schema":"js-redox/linked-runtime-source-tree/v2",
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
                outer_source,
                inner_source,
            },
        ))
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
            "js-redox/linked-runtime-source-tree/v2"
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
        fs::write(&input.inner_source, "tampered VM source")?;
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
