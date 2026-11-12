use anyhow::{Context, Result};
use clap::{Args as ClapArgs, Parser, Subcommand, ValueEnum};
use jsvm_lift::{
    analysis_artifacts::{load_artifact, DEOBFUSCATION, JS_REFERENCES, SOURCE_INDEX},
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    project_deob::{materialize_project_deobfuscation, ProjectDeobOptions},
    project_import_names::propagate_imported_names,
    safe_deob::{deobfuscate_source, SourceMode},
    sha256_hex,
    source_tree_aliases::{explain_captured_handler_origins, explain_property_aliases},
    source_tree_callflow::{reconstruct_caller_views, CallerView},
    source_tree_context::{
        annotate_handler_helper_calls_with_specializations, reconstruct_context,
        SpecializedHelperCall,
    },
    source_tree_inline::expand_helper_returns,
    source_tree_reflow::reflow_single_trip_loops,
    source_tree_return_flow::recover_terminal_returns,
    source_tree_specialize::{specialize_calls, specialize_resolved_call_graph},
};
use serde_json::json;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

#[derive(Parser, Debug)]
#[command(
    version,
    about = "Proof-oriented static JavaScript deobfuscation; never executes sample code"
)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Deobfuscate one source file and optionally emit a proof report.
    Source(SourceArgs),
    /// Materialize an entire directory of ordinary JavaScript source files as a readable tree.
    SourceTree(SourceTreeArgs),
    /// Trace lexical call chains and parameter origins in a standalone JS program.
    CallerViews(CallerViewsArgs),
    /// Materialize safe source recovery/deobfuscation for a normalized capture project.
    Project(ProjectArgs),
    /// Reapply captured ESM export/import name linking to existing analyst-only readable files.
    /// Does not reacquire or deobfuscate sources, and never touches exact captured output.
    ProjectNames(ProjectNamesArgs),
}

#[derive(ClapArgs, Debug)]
struct SourceArgs {
    input: PathBuf,
    output: PathBuf,
    #[arg(long)]
    report: Option<PathBuf>,
    #[arg(long, default_value_t = 16)]
    max_iterations: usize,
    /// Override JavaScript source mode instead of inferring it from the input suffix.
    #[arg(long, value_enum)]
    source_mode: Option<SourceModeArg>,
    /// Pretty-print the final analyst view. This is intentionally opt-in:
    /// Function#toString and related self-defending code can observe formatting.
    #[arg(long)]
    format_output: bool,
}

#[derive(ClapArgs, Debug)]
struct CallerViewsArgs {
    /// Original JS source (prefer the already formatted source for readable excerpts).
    input: PathBuf,
    /// Directory containing browsable Markdown and compact machine-readable paths.
    output: PathBuf,
    /// Optional member-assigned entrypoint, such as aoF_.
    #[arg(long)]
    entry_member: Option<String>,
    /// Generate readable, callsite-specific helper bodies from original
    /// lexical call edges (opt-in because it can produce many variants).
    #[arg(long)]
    specialize: bool,
    #[arg(long, default_value_t = 12)]
    max_iterations: usize,
}

#[derive(ClapArgs, Debug)]
struct ProjectArgs {
    project: PathBuf,
    #[arg(long)]
    jobs: Option<usize>,
    #[arg(long, default_value_t = 16)]
    max_iterations: usize,
}

#[derive(ClapArgs, Debug)]
struct ProjectNamesArgs {
    /// Normalized capture project with existing source/index and deobfuscation artifacts.
    project: PathBuf,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum SourceModeArg {
    Auto,
    Module,
    Commonjs,
}

impl From<SourceModeArg> for SourceMode {
    fn from(value: SourceModeArg) -> Self {
        match value {
            SourceModeArg::Auto => Self::Auto,
            SourceModeArg::Module => Self::Module,
            SourceModeArg::Commonjs => Self::CommonJs,
        }
    }
}

fn source_mode(args: &SourceArgs) -> SourceMode {
    args.source_mode
        .map(SourceMode::from)
        .unwrap_or_else(|| SourceMode::for_path(&args.input))
}

#[derive(ClapArgs, Debug)]
struct SourceTreeArgs {
    /// Root folder containing .js/.mjs/.cjs source files, scanned recursively.
    input: PathBuf,
    /// Separate output directory for transformed files and a navigable README.
    output: PathBuf,
    #[arg(long, default_value_t = 16)]
    max_iterations: usize,
    /// Pretty-print the analyst source view. Reformatting may alter Function#toString.
    #[arg(long)]
    format_output: bool,
    /// Original full JavaScript program enclosing extracted functions.
    /// Materializes lexical helper implementations alongside the readable tree.
    #[arg(long)]
    context_source: Option<PathBuf>,
    /// Raw original source, byte-for-byte matching source hashes and spans
    /// in captured-handler provenance headers. Pretty-printed source does
    /// not have the same offsets and must not be substituted here.
    #[arg(long, requires = "context_source")]
    origin_source: Option<PathBuf>,
    /// Optional AST property name of a member-assigned function entrypoint.
    /// Produces exact lexical direct-call argument-forwarding browsing views.
    /// Does not modify executable JS or infer dynamic method dispatch.
    #[arg(long, requires = "context_source")]
    caller_view_entry: Option<String>,
}

fn collect_js_sources(root: &Path) -> Result<Vec<PathBuf>> {
    let mut queued = vec![root.to_path_buf()];
    let mut sources = Vec::new();
    while let Some(dir) = queued.pop() {
        let mut entries = fs::read_dir(&dir)
            .with_context(|| format!("listing {}", dir.display()))?
            .map(|entry| entry.map(|entry| entry.path()))
            .collect::<std::io::Result<Vec<_>>>()?;
        entries.sort();
        for path in entries {
            let ty = fs::symlink_metadata(&path)
                .with_context(|| format!("checking {}", path.display()))?
                .file_type();
            if ty.is_symlink() {
                // No directory traversal outside the requested source tree.
                continue;
            }
            if ty.is_dir() {
                queued.push(path);
            } else if ty.is_file()
                && path
                    .extension()
                    .and_then(|extension| extension.to_str())
                    .is_some_and(|ext| {
                        matches!(ext.to_ascii_lowercase().as_str(), "js" | "mjs" | "cjs")
                    })
            {
                sources.push(path);
            }
        }
    }
    sources.sort();
    Ok(sources)
}

struct PolishedHelperView {
    source: String,
    single_trip_loops_reflowed: usize,
    subsequent_transforms: BTreeMap<String, usize>,
    post_reflow_error: Option<String>,
    adjacent_returns: usize,
    labeled_return_joins: usize,
    guarded_return_joins: usize,
    post_return_error: Option<String>,
}

/// Re-run the existing static pass after loop structure has become explicit.
/// This allows its proven dead-branch and block reductions to see through
/// former single-trip loops without introducing another JS evaluator.
fn polish_lexical_helper_view(
    source: String,
    label: &str,
    max_iterations: usize,
    format_output: bool,
    budgets: &AnalysisBudgets,
) -> Result<PolishedHelperView> {
    let reflowed = reflow_single_trip_loops(&source)?;
    let (source, mut subsequent_transforms, post_reflow_error) = if reflowed.rewritten_loops == 0 {
        (source, BTreeMap::new(), None)
    } else {
        let budget = budgets.operation(
            AnalysisOperation::SafeDeobfuscation,
            format!("post-reflow {label}"),
        );
        match deobfuscate_source(
            &reflowed.source,
            format!("post-reflow {label}"),
            SourceMode::Auto,
            max_iterations,
            format_output,
            &budget,
        ) {
            Ok(outcome) => (outcome.source, outcome.report.transforms, None),
            Err(error) => (reflowed.source, BTreeMap::new(), Some(error.to_string())),
        }
    };

    let returns = recover_terminal_returns(&source)?;
    let adjacent_returns = returns.adjacent_returns;
    let labeled_return_joins = returns.labeled_joins;
    let guarded_return_joins = returns.guarded_joins;
    let (source, post_return_error) =
        if adjacent_returns + labeled_return_joins + guarded_return_joins == 0 {
            (returns.source, None)
        } else {
            let budget = budgets.operation(
                AnalysisOperation::SafeDeobfuscation,
                format!("post-return-flow {label}"),
            );
            match deobfuscate_source(
                &returns.source,
                format!("post-return-flow {label}"),
                SourceMode::Auto,
                max_iterations,
                format_output,
                &budget,
            ) {
                Ok(outcome) => {
                    for (kind, count) in outcome.report.transforms {
                        *subsequent_transforms.entry(kind).or_default() += count;
                    }
                    (outcome.source, None)
                }
                Err(error) => (returns.source, Some(error.to_string())),
            }
        };
    Ok(PolishedHelperView {
        source,
        single_trip_loops_reflowed: reflowed.rewritten_loops,
        subsequent_transforms,
        post_reflow_error,
        adjacent_returns,
        labeled_return_joins,
        guarded_return_joins,
        post_return_error,
    })
}

fn run_source_tree(args: SourceTreeArgs) -> Result<()> {
    let root = args
        .input
        .canonicalize()
        .with_context(|| format!("source tree does not exist: {}", args.input.display()))?;
    anyhow::ensure!(root.is_dir(), "source tree must be a directory");
    fs::create_dir_all(&args.output)
        .with_context(|| format!("creating {}", args.output.display()))?;
    let out = args.output.canonicalize()?;
    anyhow::ensure!(
        !out.starts_with(&root) && !root.starts_with(&out),
        "source and output trees must be disjoint"
    );
    let sources = collect_js_sources(&root)?;
    anyhow::ensure!(
        !sources.is_empty(),
        "source tree contains no JavaScript files"
    );
    let budgets = AnalysisBudgets::standard("deobfuscate-safe-source-tree");
    let mut total_transforms = BTreeMap::<String, usize>::new();
    let mut semantically_changed = 0usize;
    let mut presentation_only = 0usize;
    let mut failed = 0usize;
    let mut rows = Vec::new();
    let mut md = String::from("# Reconstructed JavaScript source tree\n\n");
    md.push_str("The files below are actual transformed JavaScript, not just source inventories. ");
    md.push_str(
        "Conditional paths remain conditional and external references retain their names. ",
    );
    if args.format_output {
        md.push_str("Formatting is for analysis; JavaScript that observes Function#toString may behave differently.\n\n");
    } else {
        md.push_str("Original source formatting is preserved where possible.\n\n");
    }
    md.push_str("| Source | Transformations | State |\n|---|---:|---|\n");
    for path in sources {
        let relative = path.strip_prefix(&root)?;
        let label = relative.to_string_lossy().replace('\\', "/");
        let dest = out.join(relative);
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent)?;
        }
        let input =
            fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
        let budget = budgets.operation(
            AnalysisOperation::SafeDeobfuscation,
            path.display().to_string(),
        );
        let result = deobfuscate_source(
            &input,
            label.clone(),
            SourceMode::for_path(&path),
            args.max_iterations,
            args.format_output,
            &budget,
        );
        let (output, transforms, status, error): (
            String,
            BTreeMap<String, usize>,
            &str,
            Option<String>,
        ) = match result {
            Ok(outcome) => {
                let had_semantic_rewrite = outcome
                    .report
                    .transforms
                    .iter()
                    .any(|(kind, count)| kind != "presentation_codegen" && *count > 0);
                let status = if had_semantic_rewrite {
                    semantically_changed += 1;
                    "transformed"
                } else if outcome.report.changed {
                    presentation_only += 1;
                    "formatted"
                } else {
                    "unchanged"
                };
                (outcome.source, outcome.report.transforms, status, None)
            }
            Err(error) => {
                failed += 1;
                (
                    input,
                    BTreeMap::new(),
                    "unrecovered",
                    Some(error.to_string()),
                )
            }
        };
        fs::write(&dest, output.as_bytes())
            .with_context(|| format!("writing {}", dest.display()))?;
        for (kind, count) in &transforms {
            *total_transforms.entry(kind.to_owned()).or_default() += count;
        }
        let n: usize = transforms.values().sum();
        md.push_str(&format!("| [{label}]({label}) | {n} | {status} |\n"));
        rows.push(json!({
            "path": label,
            "status": status,
            "input_bytes": fs::metadata(&path)?.len(),
            "output_bytes": output.len(),
            "transforms": transforms,
            "error": error
        }));
    }
    let summary = json!({
        "schema": "jsvm-source-tree-reconstruction/v1",
        "source_count": rows.len(),
        "semantically_changed_count": semantically_changed,
        "presentation_only_count": presentation_only,
        "unrecovered_count": failed,
        "transforms": total_transforms,
        "files": rows,
        "presentation_formatted": args.format_output,
    });
    let mut summary_text = serde_json::to_string_pretty(&summary)?;
    summary_text.push('\n');
    fs::write(out.join("reconstruction.json"), summary_text)?;
    md.push_str("\nMachine-readable summary: [reconstruction.json](reconstruction.json).\n");
    if let Some(context_path) = &args.context_source {
        let original = fs::read_to_string(context_path)
            .with_context(|| format!("reading context {}", context_path.display()))?;
        let source_inputs = collect_js_sources(&root)?
            .into_iter()
            .map(|path| {
                Ok((
                    path.strip_prefix(&root)?
                        .to_string_lossy()
                        .replace('\\', "/"),
                    fs::read_to_string(&path)?,
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        let context = reconstruct_context(&original, &source_inputs)?;
        let folder = out.join("lexical-context");
        anyhow::ensure!(
            !folder.exists(),
            "output already has a lexical-context directory"
        );
        fs::create_dir_all(folder.join("helpers"))?;
        fs::write(folder.join("original.js"), &original)?;
        let mut explained_rows = Vec::new();
        let mut explained_index = String::from(
            "# Path-sensitive property-alias explanations\n\nThese are alternate annotated browsing views, \
             not replacements for the original executable JavaScript. An alias can be \
             conditionally overwritten: annotations retain the actual dynamic property lookup \
             and show assignment values and branch conditions instead of guessing.\n\n",
        );
        let mut helper_rows = Vec::new();
        let mut helper_index = String::from("# Actual lexical helper implementations\n\n");
        helper_index.push_str("These definitions come from the supplied original program. ");
        helper_index.push_str(
            "They are browsing views of closure-scoped code, not independent runnable modules. ",
        );
        helper_index.push_str(
            "The [original lexical program](original.js) preserves the full binding context.\n\n",
        );
        let helper_files = context
            .helpers
            .iter()
            .map(|helper| (helper.name.as_str(), helper.file.as_str()))
            .collect::<BTreeMap<_, _>>();
        for helper in &context.helpers {
            let relative = &helper.file;
            let label = format!("original helper {}", helper.name);
            let budget = budgets.operation(AnalysisOperation::SafeDeobfuscation, label.clone());
            let outcome = deobfuscate_source(
                &helper.source,
                label.clone(),
                SourceMode::Auto,
                args.max_iterations,
                args.format_output,
                &budget,
            );
            let (code, mut transforms, error) = match outcome {
                Ok(rewritten) => (rewritten.source, rewritten.report.transforms, None),
                Err(error) => (
                    helper.source.clone(),
                    BTreeMap::new(),
                    Some(error.to_string()),
                ),
            };
            // The original program remains byte-exact in lexical-context/original.js.
            // Improve only the independently readable helper projection.
            let polished = polish_lexical_helper_view(
                code,
                &label,
                args.max_iterations,
                args.format_output,
                &budgets,
            )?;
            let code = polished.source;
            let rewritten_loops = polished.single_trip_loops_reflowed;
            let post_reflow_error = polished.post_reflow_error;
            let adjacent_returns = polished.adjacent_returns;
            let labeled_return_joins = polished.labeled_return_joins;
            let guarded_return_joins = polished.guarded_return_joins;
            let post_return_error = polished.post_return_error;
            for (kind, count) in polished.subsequent_transforms {
                *transforms.entry(kind).or_default() += count;
            }
            if adjacent_returns > 0 {
                *transforms
                    .entry("source_adjacent_return_flow".to_owned())
                    .or_default() += adjacent_returns;
            }
            if guarded_return_joins > 0 {
                *transforms
                    .entry("source_guarded_return_flow".to_owned())
                    .or_default() += guarded_return_joins;
            }
            if labeled_return_joins > 0 {
                *transforms
                    .entry("source_labeled_return_flow".to_owned())
                    .or_default() += labeled_return_joins;
            }
            if rewritten_loops > 0 {
                *transforms
                    .entry("source_single_trip_reflow".to_owned())
                    .or_default() += rewritten_loops;
            }
            fs::write(folder.join(relative), &code)?;
            // Annotate references only where the helper's *own* AST resolves
            // the property key to the same symbol as its prior assignments.
            // Never join independent functions by spelling (T, JM, etc.).
            if let Some(explained) = explain_property_aliases(&code)? {
                let explained_relative = relative.replacen("helpers/", "explained/", 1);
                if let Some(parent) = folder.join(&explained_relative).parent() {
                    fs::create_dir_all(parent)?;
                }
                fs::write(folder.join(&explained_relative), &explained.source)?;
                explained_index.push_str(&format!(
                    "- [{}]({}) — {} explained accesses across {} bindings\n",
                    helper.name,
                    explained_relative.trim_start_matches("explained/"),
                    explained.annotated_reads,
                    explained.aliases.len()
                ));
                explained_rows.push(json!({
                    "helper": helper.name,
                    "source_path": relative,
                    "annotated_path": explained_relative,
                    "annotated_accesses": explained.annotated_reads,
                    "aliases": explained.aliases,
                }));
            }
            helper_index.push_str(&format!("- [{}]({})", helper.name, relative));
            if helper.mutable_binding {
                helper_index.push_str(" — **binding reassigned in original program**");
            }
            if !helper.references.is_empty() {
                helper_index.push_str(&format!(" — uses {}", helper.references.join(", ")));
            }
            helper_index.push('\n');
            helper_rows.push(json!({
                "name": helper.name,
                "path": relative,
                "binding_mutable": helper.mutable_binding,
                "references": helper.references,
                "single_trip_loops_reflowed": rewritten_loops,
                "post_reflow_error": post_reflow_error,
                "adjacent_return_values": adjacent_returns,
                "labeled_return_joins": labeled_return_joins,
                "guarded_return_joins": guarded_return_joins,
                "post_return_error": post_return_error,
                "transforms": transforms,
                "error": error,
            }));
        }
        if !explained_rows.is_empty() {
            fs::write(folder.join("explained/README.md"), explained_index)?;
            helper_index
                .push_str("\n[Browse annotated lexical property aliases](explained/README.md). ");
            helper_index.push_str("These preserve conditional runtime property keys.\n");
            md.push_str("\n## Explained conditional property aliases\n\n");
            md.push_str("[Browse exact lexical-alias analysis views](lexical-context/explained/README.md). ");
            md.push_str("The original property expressions remain dynamic where needed.\n\n");
        }
        // A fixed-argument callsite can expose a more useful helper body than
        // its multipurpose definition. Materialize *both* source views.
        let helper_counts =
            context
                .helpers
                .iter()
                .fold(BTreeMap::<&str, usize>::new(), |mut counts, helper| {
                    *counts.entry(helper.name.as_str()).or_default() += 1;
                    counts
                });
        let helper_sources = context
            .helpers
            .iter()
            .filter(|helper| {
                !helper.mutable_binding && helper_counts.get(helper.name.as_str()) == Some(&1)
            })
            .map(|helper| (helper.name.clone(), helper.source.clone()))
            .collect::<BTreeMap<_, _>>();
        let specializations = specialize_calls(&source_inputs, &helper_sources)?;
        let specialized_links = specializations
            .iter()
            .map(|specialized| {
                let encoded_args = serde_json::to_string(&specialized.arguments)?;
                let suffix = &sha256_hex(encoded_args.as_bytes())[..12];
                let hint = specialized
                    .arguments
                    .iter()
                    .map(|(index, literal)| {
                        let literal = literal
                            .chars()
                            .filter(char::is_ascii_alphanumeric)
                            .take(15)
                            .collect::<String>();
                        format!("arg{index}-{literal}")
                    })
                    .collect::<Vec<_>>()
                    .join("_");
                Ok(SpecializedHelperCall {
                    helper: specialized.helper.clone(),
                    constants: specialized.arguments.clone(),
                    file: format!(
                        "specializations/{}-{}-{suffix}.js",
                        specialized.helper, hint
                    ),
                })
            })
            .collect::<Result<Vec<_>>>()?;
        // Show the original lexical behavior at *actual callsites* in a
        // separate, non-executable browsing copy of each recovered handler.
        // This never touches the semantic recovery file written above.
        let mut annotated_call_rows = Vec::new();
        let mut annotated_index = String::from(
            "# Source-backed lexical calls in recovered handlers\n\n\
             These are presentation-only copies of the recovered handlers. \
             Comments at direct calls identify uniquely resolved original \
             helpers; small single-return bodies are quoted verbatim, while \
             larger helpers link to their actual original definitions. \
             A proven literal-selector call links to its existing specialized \
             helper body at every matching callsite. Reassigned helpers \
             describe their *initial* definition only. Other closure \
             references remain unresolved, not guessed.\n\n",
        );
        for handler in &context.handlers {
            let code = fs::read_to_string(out.join(&handler.path))?;
            let Some(annotated) = annotate_handler_helper_calls_with_specializations(
                &code,
                &context,
                handler,
                &specialized_links,
            )?
            else {
                continue;
            };
            let relative = format!("annotated-handlers/{}", handler.path);
            if let Some(parent) = folder.join(&relative).parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(folder.join(&relative), &annotated.source)?;
            annotated_index.push_str(&format!(
                "- [{}]({}) — {} original lexical helper call annotations: {}\n",
                handler.path,
                handler.path,
                annotated.call_count,
                annotated.helpers.join(", ")
            ));
            annotated_call_rows.push(json!({
                "path": handler.path,
                "annotated_path": relative,
                "annotated_calls": annotated.call_count,
                "helpers": annotated.helpers,
            }));
        }
        if !annotated_call_rows.is_empty() {
            fs::write(folder.join("annotated-handlers/README.md"), annotated_index)?;
            helper_index.push_str(
                "\n[Browse recovered handlers with inline lexical helper context](annotated-handlers/README.md).\n",
            );
            md.push_str(
                "\n## Recovered handlers with original lexical helper call context\n\n\
                 [Read annotated handler code](lexical-context/annotated-handlers/README.md). \
                 The ordinary reconstructed handler files are unchanged.\n\n",
            );
        }
        // The ordinary recovered handler remains authoritative. This extra
        // view substitutes verified short original return expressions at
        // callsites, keeping larger/unsafe helper calls intact.
        let mut expanded_rows = Vec::new();
        let mut expanded_index = String::from(
            "# Source-backed expanded helper returns\n\n\
             These files substitute original short return expressions only \
             when the extracted handler's argument bindings, original helper \
             parameters, and lexical captures are statically compatible. \
             Nonmatching calls stay unchanged. This is an analyst-only \
             projection; the ordinary source tree remains the executable \
             recovery.\n\n",
        );
        for handler in &context.handlers {
            let code = fs::read_to_string(out.join(&handler.path))?;
            let Some(expanded) = expand_helper_returns(&code, &context, handler)? else {
                continue;
            };
            let relative = format!("expanded-handlers/{}", handler.path);
            if let Some(parent) = folder.join(&relative).parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(folder.join(&relative), expanded.source)?;
            expanded_index.push_str(&format!(
                "- [{}]({}) — {} original helper calls expanded: {}\n",
                handler.path,
                handler.path,
                expanded.expanded_calls,
                expanded.helpers.join(", ")
            ));
            expanded_rows.push(json!({
                "path": handler.path,
                "expanded_path": relative,
                "expanded_calls": expanded.expanded_calls,
                "helpers": expanded.helpers,
            }));
        }
        if !expanded_rows.is_empty() {
            fs::write(folder.join("expanded-handlers/README.md"), expanded_index)?;
            helper_index.push_str(
                "\n[Browse source-backed expanded helper return expressions](expanded-handlers/README.md).\n",
            );
            md.push_str(
                "\n## Short original helper returns expanded into analyst code\n\n\
                 [Read verified expression expansions](lexical-context/expanded-handlers/README.md). \
                 The ordinary reconstructed handler files remain unchanged.\n\n",
            );
        }
        fs::write(folder.join("README.md"), &helper_index)?;
        fs::create_dir_all(folder.join("specializations"))?;
        let mut specializations_md =
            String::from("# Constant-argument specialized helper code\n\n");
        specializations_md.push_str(
            "Each file substitutes exact constant call arguments into the original lexical \
             parameter references and applies static deobfuscation. Loops proven to run at \
             most once are reduced to conditional blocks without dropping the initializer \
             or condition evaluation. Original helpers remain available; these source-backed \
             derivatives are analysis views, not independently runnable modules.\n\n",
        );
        let mut specialization_rows = Vec::new();
        for (specialized, link) in specializations.into_iter().zip(&specialized_links) {
            let relative = link.file.clone();
            let budget = budgets.operation(
                AnalysisOperation::SafeDeobfuscation,
                format!("specialized {}", specialized.helper),
            );
            let (code, mut transforms, error) = match deobfuscate_source(
                &specialized.source,
                relative.clone(),
                SourceMode::Auto,
                args.max_iterations,
                args.format_output,
                &budget,
            ) {
                Ok(outcome) => (outcome.source, outcome.report.transforms, None),
                Err(error) => (
                    specialized.source.clone(),
                    BTreeMap::new(),
                    Some(error.to_string()),
                ),
            };
            let polished = polish_lexical_helper_view(
                code,
                &format!("specialized {}", specialized.helper),
                args.max_iterations,
                args.format_output,
                &budgets,
            )?;
            let code = polished.source;
            let rewritten_loops = polished.single_trip_loops_reflowed;
            let post_reflow_error = polished.post_reflow_error;
            let adjacent_returns = polished.adjacent_returns;
            let labeled_return_joins = polished.labeled_return_joins;
            let guarded_return_joins = polished.guarded_return_joins;
            let post_return_error = polished.post_return_error;
            for (kind, count) in polished.subsequent_transforms {
                *transforms.entry(kind).or_default() += count;
            }
            if adjacent_returns > 0 {
                *transforms
                    .entry("source_adjacent_return_flow".to_owned())
                    .or_default() += adjacent_returns;
            }
            if guarded_return_joins > 0 {
                *transforms
                    .entry("source_guarded_return_flow".to_owned())
                    .or_default() += guarded_return_joins;
            }
            if labeled_return_joins > 0 {
                *transforms
                    .entry("source_labeled_return_flow".to_owned())
                    .or_default() += labeled_return_joins;
            }
            if rewritten_loops > 0 {
                *transforms
                    .entry("source_single_trip_reflow".to_owned())
                    .or_default() += rewritten_loops;
            }
            fs::write(folder.join(&relative), &code)?;
            let actual_changes = code != specialized.original;
            let constants = specialized
                .arguments
                .iter()
                .map(|(index, literal)| format!("argument {index} = {literal}"))
                .collect::<Vec<_>>()
                .join(", ");
            let display_file = relative
                .strip_prefix("specializations/")
                .unwrap_or(relative.as_str());
            let caller_links = specialized
                .call_sites
                .iter()
                .filter_map(|site| {
                    let (path, offset) = site.rsplit_once(':')?;
                    Some(format!("[{path}:{offset}](../../{path})"))
                })
                .collect::<Vec<_>>()
                .join(", ");
            specializations_md.push_str(&format!(
                "- [{}]({display_file}) ({constants}), used at {caller_links}\n",
                specialized.helper
            ));
            specialization_rows.push(json!({
                "helper": specialized.helper,
                "arguments": specialized.arguments,
                "path": relative,
                "call_sites": specialized.call_sites,
                "specialized_source_changed": actual_changes,
                "single_trip_loops_reflowed": rewritten_loops,
                "post_reflow_error": post_reflow_error,
                "adjacent_return_values": adjacent_returns,
                "labeled_return_joins": labeled_return_joins,
                "guarded_return_joins": guarded_return_joins,
                "post_return_error": post_return_error,
                "transforms": transforms,
                "error": error,
            }));
        }
        fs::write(folder.join("specializations/README.md"), specializations_md)?;
        md.push_str("\n## Constant-argument specialized helper bodies\n\n");
        md.push_str(
            "[Browse helper code specialized at real handler callsites](lexical-context/specializations/README.md).\n\n"
        );
        md.push_str("\n## Original lexical context and helper code\n\n");
        md.push_str("[Browse linked helper implementations](lexical-context/README.md). ");
        md.push_str("These are actual original bindings, not guessed API names.\n\n");
        for handler in &context.handlers {
            if handler.linked_helpers.is_empty() {
                continue;
            }
            let links = handler
                .linked_helpers
                .iter()
                .filter_map(|name| {
                    helper_files
                        .get(name.as_str())
                        .map(|file| format!("[{}](lexical-context/{})", name, file))
                })
                .collect::<Vec<_>>()
                .join(", ");
            md.push_str(&format!(
                "- [{}]({}) — {}\n",
                handler.path, handler.path, links
            ));
        }
        // Only a *byte-identical raw* original allows the source spans and
        // the pre-existing SHA-256 headers to identify external lexical
        // bindings of captured handlers. The pretty-printed context is fine
        // for browsing helper definitions but is NOT a span provenance source.
        let mut origin_rows = Vec::new();
        let mut origin_source_sha256 = None;
        let mut raw_caller_views = Vec::new();
        if let Some(origin_path) = &args.origin_source {
            let raw_origin = fs::read_to_string(origin_path)
                .with_context(|| format!("reading raw capture origin {}", origin_path.display()))?;
            origin_source_sha256 = Some(sha256_hex(raw_origin.as_bytes()));
            if let Some(entry) = &args.caller_view_entry {
                raw_caller_views = reconstruct_caller_views(&raw_origin, Some(entry))?;
            }
            let transformed_handlers = source_inputs
                .iter()
                .map(|(path, _)| Ok((path.clone(), fs::read_to_string(out.join(path))?)))
                .collect::<Result<Vec<_>>>()?;
            let views = explain_captured_handler_origins(&raw_origin, &transformed_handlers)?;
            if !views.is_empty() {
                let origin_dir = folder.join("handler-origins");
                fs::create_dir_all(&origin_dir)?;
                let mut index = String::from(
                    "# Original-source-bound property aliases in captured handlers\n\nEvery listed property key is tied to the **original raw source SHA-256, \
                    original function byte span, and an exact original lexical SymbolId**. \
                    Dynamic and conditional alias writes remain possible. These are browsing views, \
                    not executable replacements. Ordinary transformed files are unchanged.\n\n",
                );
                for view in views {
                    let relative = Path::new(&view.input_path);
                    let destination = origin_dir.join(relative);
                    if let Some(parent) = destination.parent() {
                        fs::create_dir_all(parent)?;
                    }
                    fs::write(&destination, &view.annotated_source)?;
                    index.push_str(&format!(
                        "- [{}]({}) — {} explained accesses, original bytes {}..{}\n",
                        view.input_path,
                        view.input_path,
                        view.annotated_reads,
                        view.original_span[0],
                        view.original_span[1]
                    ));
                    origin_rows.push(json!({
                        "input_path": view.input_path,
                        "annotated_path": format!("handler-origins/{}", view.input_path),
                        "original_span": view.original_span,
                        "annotated_accesses": view.annotated_reads,
                        "aliases": view.aliases,
                    }));
                }
                fs::write(origin_dir.join("README.md"), index)?;
                helper_index.push_str(
                    "\n[Captured handler property-alias origins](handler-origins/README.md).\n",
                );
                fs::write(folder.join("README.md"), &helper_index)?;
                md.push_str("\n## Source-bound captured handler property aliases\n\n");
                md.push_str("[Browse property aliases in individual recovered handlers](lexical-context/handler-origins/README.md).\n\n");
            }
        }
        let mut caller_view_rows = Vec::new();
        let mut graph_specialization_rows = Vec::new();
        if let Some(entry) = &args.caller_view_entry {
            let views = reconstruct_caller_views(&original, Some(entry))?;
            if !views.is_empty() {
                let dir = folder.join("caller-views");
                fs::create_dir_all(&dir)?;
                // Same exact graph-based specialization writer as the
                // standalone caller-views CLI; no second extraction logic.
                for mut row in
                    write_callsite_specializations(&original, &views, &dir, args.max_iterations)?
                {
                    for key in ["path", "original_path"] {
                        if let Some(path) = row[key].as_str() {
                            row[key] = json!(format!("caller-views/{path}"));
                        }
                    }
                    graph_specialization_rows.push(row);
                }
                let mut index = String::from(
                    "# Caller-oriented direct argument forwarding\n\nThese are static \
                     lexical call paths and parameter-origin explanations, not new \
                     executable modules. Unknown or rewritten values remain dynamic.\n\n",
                );
                for (index_num, view) in views.into_iter().enumerate() {
                    let relative = format!("caller-views/entry-{index_num}.md");
                    let mut source = view.source.clone();
                    let helpers = view
                        .paths
                        .iter()
                        .flat_map(|path| &path.functions)
                        .filter_map(|name| helper_files.get(name.as_str()).map(|file| (name, file)))
                        .collect::<std::collections::BTreeSet<_>>();
                    if !helpers.is_empty() {
                        source.push_str("## Reconstructed helper implementations\n\n");
                        for (name, path) in helpers {
                            source.push_str(&format!("- [`{name}`](../{path})\n"));
                        }
                        source.push('\n');
                    }
                    // Original pretty/raw offsets differ. Use separately
                    // parsed exact raw function spans to connect only
                    // captured handlers whose *verified lexical declaration*
                    // belongs to an exact leaf function in this path.
                    let mut linked = std::collections::BTreeSet::new();
                    let mut focused_paths = std::collections::BTreeSet::new();
                    for (path_index, pretty_path) in view.paths.iter().enumerate() {
                        let matching = raw_caller_views
                            .iter()
                            .flat_map(|raw| &raw.paths)
                            .filter(|path| path.functions == pretty_path.functions)
                            .collect::<Vec<_>>();
                        let [raw_path] = matching.as_slice() else {
                            continue;
                        };
                        let Some(leaf) = raw_path.function_spans.last() else {
                            continue;
                        };
                        let bound_handlers = origin_rows
                            .iter()
                            .filter_map(|row| {
                                let aliases = row.get("aliases")?.as_array()?;
                                let attached = aliases.iter().any(|alias| {
                                    let declaration = alias
                                        .get("declaration")
                                        .and_then(serde_json::Value::as_array);
                                    declaration.is_some_and(|d| {
                                        d.len() == 2
                                            && d[0]
                                                .as_u64()
                                                .is_some_and(|start| start >= u64::from(leaf[0]))
                                            && d[1]
                                                .as_u64()
                                                .is_some_and(|end| end <= u64::from(leaf[1]))
                                    })
                                });
                                attached
                                    .then(|| row.get("annotated_path")?.as_str().map(str::to_owned))
                                    .flatten()
                            })
                            .collect::<Vec<_>>();
                        if !bound_handlers.is_empty() {
                            focused_paths.insert(path_index);
                            linked.extend(bound_handlers);
                        }
                    }
                    if !focused_paths.is_empty() && focused_paths.len() < view.paths.len() {
                        let complete = format!("caller-views/entry-{index_num}-all.md");
                        fs::write(folder.join(&complete), &view.source)?;
                        source = view.render_paths(&original, &focused_paths);
                        source
                            .push_str(&format!(
                            "[All {} directly resolved call paths](entry-{index_num}-all.md).\n\n",
                            view.paths.len()));
                    }
                    if !linked.is_empty() {
                        source.push_str(
                            "## Captured handlers from the original lexical function\n\n",
                        );
                        for path in &linked {
                            source.push_str(&format!(
                                "- [Original-bound `{}`](../{})\n",
                                Path::new(path)
                                    .file_name()
                                    .and_then(|name| name.to_str())
                                    .unwrap_or(path),
                                path
                            ));
                        }
                        source.push('\n');
                    }
                    fs::write(folder.join(&relative), &source)?;
                    index.push_str(&format!(
                        "- [{}](entry-{index_num}.md): {} resolved paths\n",
                        view.entry,
                        view.paths.len()
                    ));
                    caller_view_rows.push(json!({
                        "entry": view.entry,
                        "entry_span": view.entry_span,
                        "path": relative,
                        "linked_origin_handlers": linked.into_iter().collect::<Vec<_>>(),
                        "focused_path_count": focused_paths.len(),
                        "paths": view.paths,
                        "reachable_edges": view.reachable_edges,
                        "reachable_functions": view.reachable_functions,
                    }));
                }
                index.push_str(&format!(
                    "\n[Browse {} original callsite-specialized helper bodies](specializations/README.md).\n",
                    graph_specialization_rows.len()
                ));
                fs::write(dir.join("README.md"), index)?;
                helper_index.push_str(&format!(
                    "\n[{} source-resolved helper variants](caller-views/specializations/README.md).\n",
                    graph_specialization_rows.len()
                ));
                helper_index
                    .push_str("\n[Caller-oriented parameter origins](caller-views/README.md).\n");
                fs::write(folder.join("README.md"), &helper_index)?;
                md.push_str("\n## Caller-oriented source and argument forwarding\n\n");
                md.push_str("[Browse exact lexical call chains](lexical-context/caller-views/README.md).\n\n");
                md.push_str(&format!(
                    "[Browse {} callsite-specialized readable helper bodies](lexical-context/caller-views/specializations/README.md).\n\n",
                    graph_specialization_rows.len()
                ));
            }
        }
        let mut context_json = serde_json::to_string_pretty(&json!({
            "caller_view_count": caller_view_rows.len(),
            "caller_views": caller_view_rows,
            "graph_specialization_count": graph_specialization_rows.len(),
            "graph_specializations": graph_specialization_rows,
            "origin_source_sha256": origin_source_sha256,
            "origin_handler_count": origin_rows.len(),
            "origin_handlers": origin_rows,
            "schema": "jsvm-readable-lexical-context/v2",
            "annotated_handler_count": annotated_call_rows.len(),
            "annotated_handler_calls": annotated_call_rows,
            "expanded_handler_count": expanded_rows.len(),
            "expanded_handlers": expanded_rows,
            "explained_alias_count": explained_rows.len(),
            "explained_aliases": explained_rows,
            "source": "lexical-context/original.js",
            "helper_count": helper_rows.len(),
            "helpers": helper_rows,
            "specialization_count": specialization_rows.len(),
            "specializations": specialization_rows,
            "handlers": context.handlers.iter().map(|handler| json!({
                "path": handler.path,
                "linked_helpers": handler.linked_helpers,
                "unresolved_references": handler.unresolved_references,
            })).collect::<Vec<_>>(),
            "unmatched_names": context.unmatched_names,
        }))?;
        context_json.push('\n');
        fs::write(folder.join("context.json"), context_json)?;
    }
    fs::write(out.join("README.md"), md)?;
    println!(
        "{}",
        json!({
            "source_count": summary["source_count"],
            "semantically_changed_count": semantically_changed,
        "presentation_only_count": presentation_only,
            "unrecovered_count": failed,
            "transforms": summary["transforms"],
            "output": out.display().to_string(),
        })
    );
    Ok(())
}

fn run_source(args: SourceArgs) -> Result<()> {
    let original = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let budgets = AnalysisBudgets::standard("deobfuscate-safe");
    let budget = budgets.operation(
        AnalysisOperation::SafeDeobfuscation,
        args.input.display().to_string(),
    );
    let outcome = deobfuscate_source(
        &original,
        args.input.display().to_string(),
        source_mode(&args),
        args.max_iterations,
        args.format_output,
        &budget,
    )?;

    if let Some(parent) = args.output.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(&args.output, outcome.source.as_bytes())
        .with_context(|| format!("writing {}", args.output.display()))?;

    if let Some(path) = &args.report {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut encoded = serde_json::to_string_pretty(&outcome.report)?;
        encoded.push('\n');
        fs::write(path, encoded).with_context(|| format!("writing {}", path.display()))?;
    }

    println!(
        "safe deobfuscation changed={} iterations={} transforms={:?}",
        outcome.report.changed, outcome.report.iterations, outcome.report.transforms
    );
    Ok(())
}

fn run_project_names(args: ProjectNamesArgs) -> Result<()> {
    let project = args
        .project
        .canonicalize()
        .with_context(|| format!("project does not exist: {}", args.project.display()))?;
    // Unlike the optional post-pass in the full capture pipeline, a direct
    // request to relink names must reject missing or invalid graph artifacts.
    for artifact in [SOURCE_INDEX, DEOBFUSCATION, JS_REFERENCES] {
        let _ = load_artifact(&project, artifact, false)?;
    }
    let renamed = propagate_imported_names(&project)?;
    println!(
        "linked {renamed} imported lexical names in readable project {}",
        project.display()
    );
    Ok(())
}

fn run_project(args: ProjectArgs) -> Result<()> {
    let project = args
        .project
        .canonicalize()
        .with_context(|| format!("project does not exist: {}", args.project.display()))?;
    let summary = materialize_project_deobfuscation(
        &project,
        &ProjectDeobOptions {
            jobs: args.jobs,
            max_iterations: args.max_iterations,
            budgets: AnalysisBudgets::standard("deobfuscate-safe-project"),
        },
    )?;
    println!(
        "safe source recovery: {} JS occurrences / {} unique raw / {} unique pre-deob / {} unique safe outputs; {} changed, {} deob failures; string recovery={} units/{} replacements",
        summary.javascript_units,
        summary.unique_raw_inputs,
        summary.unique_pre_deob_inputs,
        summary.unique_deob_outputs,
        summary.changed_units,
        summary.failed_units,
        summary.string_recovery_changed_units,
        summary.string_recovery_replacements,
    );
    Ok(())
}

/// One shared writer for original-lexical, callsite-specific helper variants.
fn write_callsite_specializations(
    original: &str,
    views: &[CallerView],
    output: &Path,
    max_iterations: usize,
) -> Result<Vec<serde_json::Value>> {
    let mut specialization_rows = Vec::new();
    let candidates = specialize_resolved_call_graph(original, views)?;
    let depths = views
        .iter()
        .flat_map(|view| &view.reachable_functions)
        .fold(
            BTreeMap::<[u32; 2], usize>::new(),
            |mut depths, function| {
                depths
                    .entry(function.span)
                    .and_modify(|depth| *depth = (*depth).min(function.shortest_call_depth))
                    .or_insert(function.shortest_call_depth);
                depths
            },
        );
    let mut ranked = Vec::<(isize, usize, usize, String)>::new();
    let mut grouped = BTreeMap::<(String, [u32; 2]), Vec<String>>::new();
    let destination = output.join("specializations");
    fs::create_dir_all(destination.join("original"))?;
    let budgets = AnalysisBudgets::standard("deobfuscate-safe-graph-specializations");
    for candidate in candidates {
        let arguments_json = serde_json::to_string(&candidate.constants)?;
        let digest = sha256_hex(arguments_json.as_bytes());
        let filename = format!(
            "function-{}-{}-{}.js",
            candidate.function_span[0],
            candidate.function_span[1],
            &digest[..12],
        );
        let relative = format!("specializations/{filename}");
        let original_relative = format!("specializations/original/{filename}");
        let budget = budgets.operation(
            AnalysisOperation::SafeDeobfuscation,
            format!("lexical callsite {}", candidate.helper),
        );
        let outcome = deobfuscate_source(
            &candidate.specialized,
            relative.clone(),
            SourceMode::Auto,
            max_iterations,
            true,
            &budget,
        );
        let (code, transforms, error) = match outcome {
            Ok(recovered) => (recovered.source, recovered.report.transforms, None),
            Err(error) => (
                candidate.specialized.clone(),
                BTreeMap::new(),
                Some(error.to_string()),
            ),
        };
        fs::write(output.join(&relative), &code)?;
        fs::write(output.join(&original_relative), &candidate.original)?;
        let semantic_rewrites = transforms
            .iter()
            .filter(|(kind, _)| kind.as_str() != "presentation_codegen")
            .map(|(_, count)| count)
            .sum::<usize>();
        let saved_bytes = isize::try_from(candidate.original.len())? - isize::try_from(code.len())?;
        let depth = depths.get(&candidate.function_span).copied().unwrap_or(0);
        let file_link = format!("[{}]({filename})", candidate.helper);
        let summary = format!(
            "{file_link} (original {}..{}) — {constants_hint}; depth {depth}, {semantic_rewrites} rewrites, {saved_bytes:+} bytes, {} callsite{} ([original](original/{filename}))",
            candidate.function_span[0],
            candidate.function_span[1],
            candidate.call_sites.len(),
            if candidate.call_sites.len() == 1 { "" } else { "s" },
            constants_hint = candidate
                .constants
                .iter()
                .map(|(index, literal)| format!("arg{index}={literal}"))
                .collect::<Vec<_>>()
                .join(", "),
        );
        ranked.push((saved_bytes, semantic_rewrites, depth, summary.clone()));
        grouped
            .entry((candidate.helper.clone(), candidate.function_span))
            .or_default()
            .push(summary);
        specialization_rows.push(json!({
            "helper": candidate.helper,
            "function_span": candidate.function_span,
            "arguments": candidate.constants,
            "call_sites": candidate.call_sites,
            "example_call_chain": candidate.example_call_chain,
            "path": relative,
            "original_path": original_relative,
            "specialized_source_changed": candidate.specialized != candidate.original,
            "safe_transforms": transforms,
            "semantic_rewrites": semantic_rewrites,
            "source_depth": depth,
            "original_bytes": candidate.original.len(),
            "readable_bytes": code.len(),
            "saved_bytes": saved_bytes,
            "deobfuscation_error": error,
        }));
    }
    ranked.sort_by(|a, b| {
        b.0.cmp(&a.0)
            .then_with(|| b.1.cmp(&a.1))
            .then_with(|| b.2.cmp(&a.2))
    });
    let mut navigable = String::from("# Readable lexical helpers by impact\n\n");
    navigable.push_str(
        "These are source-reading variants of original functions, not executable replacements. ",
    );
    navigable.push_str(
        "Byte reduction compares the original helper with its formatted recovered code; ",
    );
    navigable.push_str("rewrite counts indicate additional semantic simplifications.\n\n");
    navigable.push_str("## Largest source reductions\n\n");
    for (_, _, _, summary) in ranked.iter().take(20) {
        navigable.push_str(&format!("- {summary}\n"));
    }
    navigable.push_str("\n## All variants grouped by resolved helper\n\n");
    for ((name, span), variants) in grouped {
        navigable.push_str(&format!(
            "### {name} — original bytes {}..{} ({} variants)\n\n",
            span[0],
            span[1],
            variants.len()
        ));
        for variant in variants {
            navigable.push_str(&format!("- {variant}\n"));
        }
        navigable.push('\n');
    }
    fs::write(destination.join("README.md"), navigable)?;
    Ok(specialization_rows)
}

fn run_caller_views(args: CallerViewsArgs) -> Result<()> {
    let original = fs::read_to_string(&args.input)
        .with_context(|| format!("reading caller source {}", args.input.display()))?;
    let views = reconstruct_caller_views(&original, args.entry_member.as_deref())?;
    fs::create_dir_all(&args.output)
        .with_context(|| format!("creating caller output {}", args.output.display()))?;
    let mut index = String::from("# Source-resolved caller paths\n\n");
    index.push_str("Each path traces lexical function targets and argument origins. ");
    index.push_str("Immutable aliases of functions and parameters are followed. ");
    index.push_str("This is a source reading view, not an executable replacement.\n\n");
    let mut manifest = Vec::with_capacity(views.len());
    for (number, view) in views.iter().enumerate() {
        let path = format!("entry-{number}.md");
        fs::write(args.output.join(&path), &view.source)?;
        index.push_str(&format!(
            "- [{}]({path}) — {} resolved paths\n",
            view.entry,
            view.paths.len()
        ));
        manifest.push(json!({
            "entry": view.entry,
            "entry_span": view.entry_span,
            "paths": view.paths,
            "reachable_edges": view.reachable_edges,
            "reachable_functions": view.reachable_functions,
            "markdown_path": path,
        }));
    }
    let specialization_rows = if args.specialize {
        let rows =
            write_callsite_specializations(&original, &views, &args.output, args.max_iterations)?;
        index.push_str(
            "\n[Browse callsite-specialized lexical helper bodies](specializations/README.md).\n",
        );
        rows
    } else {
        Vec::new()
    };
    let mut data = serde_json::to_string_pretty(&json!({
        "schema": "jsvm-caller-views/v2",
        "entries": manifest,
        "specializations": specialization_rows,
        "specialization_count": specialization_rows.len(),
        "source_sha256": sha256_hex(original.as_bytes()),
    }))?;
    data.push('\n');
    fs::write(args.output.join("caller-views.json"), data)?;
    fs::write(args.output.join("README.md"), index)?;
    println!("caller views: {} entries", views.len());
    Ok(())
}

fn main() -> Result<()> {
    match Args::parse().command {
        Command::Source(args) => run_source(args),
        Command::SourceTree(args) => run_source_tree(args),
        Command::CallerViews(args) => run_caller_views(args),
        Command::Project(args) => run_project(args),
        Command::ProjectNames(args) => run_project_names(args),
    }
}

#[cfg(test)]
mod tests {
    use super::{run_caller_views, run_source_tree, sha256_hex, CallerViewsArgs, SourceTreeArgs};
    use anyhow::Result;
    use std::fs;

    #[test]
    fn standalone_caller_views_trace_immutable_aliases_without_source_tree() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("source.js");
        let output = temp.path().join("callers");
        fs::write(
            &input,
            "const deep=(x)=>x;const alias=deep;const middle=(p)=>alias(p);             const api={};api.run=(arg)=>middle(arg);",
        )?;
        run_caller_views(CallerViewsArgs {
            input,
            output: output.clone(),
            entry_member: Some("run".into()),
            specialize: false,
            max_iterations: 12,
        })?;
        let manifest: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join("caller-views.json"))?)?;
        assert_eq!(manifest["schema"], "jsvm-caller-views/v2");
        assert_eq!(manifest["entries"][0]["entry"], ".run");
        assert_eq!(
            manifest["entries"][0]["paths"][0]["functions"],
            serde_json::json!([".run", "middle", "deep"])
        );
        assert_eq!(
            manifest["entries"][0]["paths"][0]["leaf_parameters"][0]["from_entry_index"],
            0
        );
        assert_eq!(
            manifest["entries"][0]["reachable_edges"]
                .as_array()
                .map(Vec::len),
            Some(2)
        );
        let functions = manifest["entries"][0]["reachable_functions"]
            .as_array()
            .ok_or_else(|| anyhow::anyhow!("missing reachable function origins"))?;
        let deep = functions
            .iter()
            .find(|node| node["name"] == "deep")
            .ok_or_else(|| anyhow::anyhow!("missing deep lexical function"))?;
        assert_eq!(deep["shortest_call_depth"], 2);
        assert_eq!(
            deep["parameters"][0]["possible_entry_indices"],
            serde_json::json!([0])
        );
        assert_eq!(deep["parameters"][0]["unknown_or_nonentry_input"], false);
        assert!(fs::read_to_string(output.join("README.md"))?.contains("entry-0.md"));
        Ok(())
    }

    #[test]
    fn standalone_caller_views_materializes_real_specialized_js() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("source.js");
        let output = temp.path().join("callers");
        fs::write(
            &input,
            "const helper=function(selector,x){if(selector===3)return x+1;return x*2;};             const api={};api.run=(x)=>helper(3,x);",
        )?;
        run_caller_views(CallerViewsArgs {
            input,
            output: output.clone(),
            entry_member: Some("run".into()),
            specialize: true,
            max_iterations: 12,
        })?;
        let manifest: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join("caller-views.json"))?)?;
        assert_eq!(manifest["specialization_count"], 1);
        let row = &manifest["specializations"][0];
        assert_eq!(row["helper"], "helper");
        assert_eq!(row["arguments"], serde_json::json!([[0, "3"]]));
        assert!(row["deobfuscation_error"].is_null(), "{row}");
        assert_eq!(row["specialized_source_changed"], true);
        let code = fs::read_to_string(
            output.join(
                row["path"]
                    .as_str()
                    .ok_or_else(|| anyhow::anyhow!("no output path"))?,
            ),
        )?;
        assert!(
            code.contains("return x + 1") || code.contains("return x+1"),
            "{code}"
        );
        assert!(!code.contains("selector === 3"), "{code}");
        let grouped = fs::read_to_string(output.join("specializations/README.md"))?;
        assert!(grouped.contains("Largest source reductions"));
        assert!(grouped.contains("All variants grouped by resolved helper"));
        assert!(grouped.contains("helper — original bytes"));
        assert!(row["semantic_rewrites"].as_u64().is_some());
        assert_eq!(row["source_depth"], 1);
        assert_eq!(
            row["saved_bytes"].as_i64(),
            Some(
                row["original_bytes"].as_i64().unwrap_or_default()
                    - row["readable_bytes"].as_i64().unwrap_or_default()
            )
        );
        Ok(())
    }

    #[test]
    fn standalone_index_keeps_shadowed_same_named_helpers_distinct() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let source = tmp.path().join("source.js");
        let output = tmp.path().join("readable");
        fs::write(&source, "const helper=(x)=>x*3;          const api={};api.run=()=>{let r=helper(4);          {const helper=(x)=>x*4;r+=helper(5);}return r;};")?;
        run_caller_views(CallerViewsArgs {
            input: source,
            output: output.clone(),
            entry_member: Some("run".into()),
            specialize: true,
            max_iterations: 12,
        })?;
        let meta: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join("caller-views.json"))?)?;
        assert_eq!(meta["specialization_count"], 2);
        let index = fs::read_to_string(output.join("specializations/README.md"))?;
        assert_eq!(index.matches("### helper — original bytes").count(), 2);
        assert_ne!(
            meta["specializations"][0]["function_span"],
            meta["specializations"][1]["function_span"]
        );
        Ok(())
    }

    #[test]
    fn source_tree_materializes_nested_js_and_keeps_unknown_source() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("input");
        let nested = input.join("scripts");
        let output = temp.path().join("readable");
        fs::create_dir_all(&nested)?;
        let for_dispatcher =
            "function f(n){var s=4;for(s=4;s!=9;)s==4?s=n?6:9:s==6&&(s=9);return n;}";
        fs::write(nested.join("a.js"), for_dispatcher)?;
        fs::write(input.join("b.mjs"), "export const value = 42;\n")?;
        fs::write(input.join("notes.txt"), "not javascript")?;

        run_source_tree(SourceTreeArgs {
            input: input.clone(),
            output: output.clone(),
            max_iterations: 12,
            format_output: false,
            context_source: None,
            origin_source: None,
            caller_view_entry: None,
        })?;

        let index: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(output.join("reconstruction.json"))?)?;
        assert_eq!(index["source_count"], 2);
        assert_eq!(index["unrecovered_count"], 0);
        assert_eq!(index["semantically_changed_count"], 1);
        assert_eq!(index["presentation_only_count"], 0);
        assert!(index["transforms"]["if_ladder_structured"]
            .as_u64()
            .is_some());
        assert!(output.join("scripts/a.js").exists());
        assert!(output.join("b.mjs").exists());
        assert!(!output.join("notes.txt").exists());
        let transformed = fs::read_to_string(output.join("scripts/a.js"))?;
        assert!(!transformed.contains("s==4"), "{transformed}");
        assert!(fs::read_to_string(output.join("README.md"))?.contains("scripts/a.js"));
        assert_eq!(fs::read_to_string(nested.join("a.js"))?, for_dispatcher);
        Ok(())
    }

    #[test]
    fn source_tree_reflows_and_polishes_original_and_specialized_helpers() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("source");
        let output = temp.path().join("readable");
        let original = temp.path().join("original.js");
        fs::create_dir_all(&input)?;
        fs::write(
            &original,
            "function root(){const modeHandler=function(x, selector, result){for(0;(selector&90)==selector;true){touch(x);break;}result=x;return result;};}",
        )?;
        let handler = "const capturedHandler=function(x){return modeHandler(x,9);};";
        fs::write(input.join("handler.js"), handler)?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 12,
            format_output: true,
            context_source: Some(original),
            origin_source: None,
            caller_view_entry: None,
        })?;
        let context_dir = output.join("lexical-context");
        let context: serde_json::Value =
            serde_json::from_slice(&fs::read(context_dir.join("context.json"))?)?;
        let original_helper = &context["helpers"][0];
        assert_eq!(original_helper["name"], "modeHandler");
        assert_eq!(original_helper["single_trip_loops_reflowed"], 1);
        assert!(original_helper["post_reflow_error"].is_null());
        assert_eq!(original_helper["adjacent_return_values"], 1);
        assert!(original_helper["post_return_error"].is_null());
        let specialization = &context["specializations"][0];
        assert_eq!(specialization["helper"], "modeHandler");
        assert_eq!(specialization["single_trip_loops_reflowed"], 1);
        assert!(specialization["post_reflow_error"].is_null());
        assert_eq!(specialization["adjacent_return_values"], 1);
        assert!(specialization["post_return_error"].is_null());
        let path = specialization["path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("no specialized source path"))?;
        let readable = fs::read_to_string(context_dir.join(path))?;
        assert!(!readable.contains("for ("), "{readable}");
        assert!(!readable.contains("if (false)"), "{readable}");
        assert!(!readable.contains("touch("), "{readable}");
        assert!(readable.contains("return x;"), "{readable}");
        assert_eq!(fs::read_to_string(output.join("lexical-context/original.js"))?,
                   "function root(){const modeHandler=function(x, selector, result){for(0;(selector&90)==selector;true){touch(x);break;}result=x;return result;};}");
        assert!(fs::read_to_string(output.join("handler.js"))?.contains("modeHandler(x, 9)"));
        Ok(())
    }

    #[test]
    fn source_tree_recovers_guarded_return_joins_from_original_helper() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("source");
        let output = temp.path().join("readable");
        let original = temp.path().join("original.js");
        fs::create_dir_all(&input)?;
        let original_source = "function root(){const guarded=function(J,Q,Y,H){H=seed(J);if((Q&3)==1){a:{if(J.Y){H=w8(J,J.D);break a;}H=Y;}}return H;};}";
        fs::write(&original, original_source)?;
        fs::write(
            input.join("handler.js"),
            "const capturedHandler=function(J,Y,H){return guarded(J,1,Y,H);};",
        )?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 12,
            format_output: true,
            context_source: Some(original),
            origin_source: None,
            caller_view_entry: None,
        })?;
        let lexical = output.join("lexical-context");
        let context: serde_json::Value =
            serde_json::from_slice(&fs::read(lexical.join("context.json"))?)?;
        let row = &context["helpers"][0];
        assert_eq!(row["name"], "guarded");
        assert_eq!(row["guarded_return_joins"], 1, "{row}");
        assert!(row["post_return_error"].is_null(), "{row}");
        let path = row["path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("helper view path missing"))?;
        let recovered = fs::read_to_string(lexical.join(path))?;
        assert!(recovered.contains("seed(J)"), "{recovered}");
        assert!(recovered.contains("return w8(J, J.D)"), "{recovered}");
        assert!(recovered.contains("return Y"), "{recovered}");
        assert!(recovered.contains("return H"), "{recovered}");
        assert!(!recovered.contains("break a"), "{recovered}");
        assert_eq!(
            fs::read_to_string(lexical.join("original.js"))?,
            original_source
        );
        assert!(fs::read_to_string(output.join("handler.js"))?.contains("guarded(J, 1, Y, H)"));
        Ok(())
    }

    #[test]
    fn source_tree_links_original_lexical_helper_code() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("source");
        let output = temp.path().join("readable");
        fs::create_dir_all(&input)?;
        let original = temp.path().join("original.js");
        fs::write(
            &original,
            "function original(){const helper=function(x,y){return byte(x)+y;};const byte=function(x){return x[0];};}",
        )?;
        fs::write(
            input.join("handler.js"),
            "const capturedHandler=function(x){return helper(x, 16);};",
        )?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 8,
            format_output: true,
            context_source: Some(original),
            origin_source: None,
            caller_view_entry: None,
        })?;
        let context_dir = output.join("lexical-context");
        let metadata: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(context_dir.join("context.json"))?)?;
        assert_eq!(metadata["helper_count"], 2);
        assert_eq!(metadata["annotated_handler_count"], 1);
        assert_eq!(metadata["expanded_handler_count"], 1);
        let expanded = fs::read_to_string(context_dir.join("expanded-handlers/handler.js"))?;
        assert!(expanded.contains("(byte(x)+(16))"), "{expanded}");
        assert!(!expanded.contains("helper(x, 16)"), "{expanded}");
        assert!(fs::read_to_string(output.join("README.md"))?
            .contains("lexical-context/expanded-handlers/README.md"));
        let inline = fs::read_to_string(context_dir.join("annotated-handlers/handler.js"))?;
        assert!(
            inline.contains("helper /* lexical helper helper: return byte(x)+y; original definition ../helpers/helper-"),
            "{inline}"
        );
        assert!(
            inline.contains("specialized at arg1=16 => ../specializations/helper-arg1-16-"),
            "{inline}"
        );
        assert!(fs::read_to_string(output.join("handler.js"))?.contains("helper(x, 16)"));
        assert!(fs::read_to_string(output.join("README.md"))?
            .contains("lexical-context/annotated-handlers/README.md"));
        assert_eq!(metadata["specialization_count"], 1);
        assert_eq!(metadata["explained_alias_count"], 0);
        assert!(
            fs::read_to_string(context_dir.join("specializations/README.md"))?
                .contains("argument 1 = 16")
        );
        assert!(fs::read_to_string(output.join("README.md"))?.contains("helper-"));
        assert!(fs::read_to_string(context_dir.join("README.md"))?.contains("byte"));
        let mut helpers = fs::read_dir(context_dir.join("helpers"))?
            .map(|entry| entry.map(|entry| entry.path()))
            .collect::<std::io::Result<Vec<_>>>()?;
        helpers.sort();
        assert_eq!(helpers.len(), 2);
        assert!(helpers.iter().any(|path| {
            fs::read_to_string(path)
                .is_ok_and(|source| source.contains("function") && source.contains("return"))
        }));
        Ok(())
    }

    #[test]
    fn source_tree_exposes_actual_conditional_lexical_aliases() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("captured");
        let output = temp.path().join("readable");
        fs::create_dir_all(&input)?;
        let original = temp.path().join("original.js");
        fs::write(
            &original,
            r#"function original(){const helper=function(H,key){
               key='push';H.length<2&&(key=H);
               return function(value){const list=[];list[key](value);return list.length};
            };}"#,
        )?;
        fs::write(
            input.join("handler.js"),
            "const capturedHandler=function(input){return helper(input);};",
        )?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 8,
            format_output: true,
            context_source: Some(original),
            origin_source: None,
            caller_view_entry: None,
        })?;
        let ctx = output.join("lexical-context");
        let meta: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(ctx.join("context.json"))?)?;
        assert_eq!(meta["schema"], "jsvm-readable-lexical-context/v2");
        assert_eq!(meta["explained_alias_count"], 1);
        let alias = &meta["explained_aliases"][0]["aliases"][0];
        assert_eq!(alias["binding"], "key");
        assert_eq!(alias["reads"], 1);
        assert_eq!(alias["writes"][0]["literal"], "push");
        assert!(alias["writes"][1]["when"]
            .as_str()
            .is_some_and(|condition| condition.contains("H.length")));
        // Filename offsets are tied to the real original AST, not hardcoded
        // across formatting. Use the stored manifest relative source paths.
        let original_path = meta["explained_aliases"][0]["source_path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("missing original source path"))?;
        let annotated_path = meta["explained_aliases"][0]["annotated_path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("missing annotated source path"))?;
        let plain = fs::read_to_string(ctx.join(original_path))?;
        let annotated = fs::read_to_string(ctx.join(annotated_path))?;
        assert!(!plain.contains("property alias:"));
        assert!(
            annotated.contains("list[key /* property alias:"),
            "{annotated}"
        );
        assert!(annotated.contains("H.length"));
        assert!(ctx.join("explained/README.md").exists());
        Ok(())
    }

    #[test]
    fn source_tree_links_exact_raw_capture_spans_into_annotated_handlers() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let source_dir = tmp.path().join("captures");
        let output = tmp.path().join("recovered");
        fs::create_dir_all(&source_dir)?;
        let raw = r#"function parent() {
            const helper = function(H, alias) {
                alias = "push";
                H.length < 2 && (alias = H);
                return function(value) { const out = []; out[alias](value); return out; };
            };
        }"#;
        let start = raw
            .find("function(value)")
            .ok_or_else(|| anyhow::anyhow!("capture body missing"))?;
        let end = raw[start..]
            .find("};")
            .map(|size| start + size + 1)
            .ok_or_else(|| anyhow::anyhow!("capture end missing"))?;
        let hash = sha256_hex(raw.as_bytes());
        let captured = format!(
            "// Readable, non-devirtualized provenance view. Original SHA-256: {hash}\n\
             // Handler key: 7. Original bytes: {start}..{end}. Factory call: 0..1.\n\
             const capturedHandler = {};\n",
            &raw[start..end]
        );
        fs::write(source_dir.join("handler.js"), captured)?;
        let original = tmp.path().join("original.js");
        fs::write(&original, raw)?;
        run_source_tree(SourceTreeArgs {
            input: source_dir,
            output: output.clone(),
            max_iterations: 8,
            format_output: true,
            context_source: Some(original.clone()),
            origin_source: Some(original),
            caller_view_entry: None,
        })?;
        let context_dir = output.join("lexical-context");
        let meta: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(context_dir.join("context.json"))?)?;
        assert_eq!(meta["origin_handler_count"], 1);
        assert_eq!(meta["origin_handlers"][0]["annotated_accesses"], 1);
        assert_eq!(meta["origin_handlers"][0]["aliases"][0]["binding"], "alias");
        let plain = fs::read_to_string(output.join("handler.js"))?;
        assert!(!plain.contains("property alias from original"));
        let explained = fs::read_to_string(context_dir.join("handler-origins/handler.js"))?;
        assert!(
            explained.contains("out[alias /* property alias from original"),
            "{explained}"
        );
        assert!(context_dir.join("handler-origins/README.md").exists());
        Ok(())
    }

    #[test]
    fn source_tree_emits_caller_oriented_argument_provenance() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let input = tmp.path().join("captures");
        let output = tmp.path().join("readable");
        fs::create_dir_all(&input)?;
        fs::write(
            input.join("entry.js"),
            "const capturedHandler=function(){return 1;};",
        )?;
        let source = tmp.path().join("original.js");
        fs::write(&source,
            "function outer(){const deep=function(value){return value;};const Wd=function(a,b){return deep(b);};const api={};api.enter=function(J,Q){return new Wd(Q,J);};}")?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 8,
            format_output: true,
            context_source: Some(source),
            origin_source: None,
            caller_view_entry: Some("enter".into()),
        })?;
        let folder = output.join("lexical-context");
        let manifest: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(folder.join("context.json"))?)?;
        assert_eq!(manifest["caller_view_count"], 1);
        assert_eq!(
            manifest["caller_views"][0]["paths"][0]["functions"],
            serde_json::json!([".enter", "Wd", "deep"])
        );
        let text = fs::read_to_string(folder.join("caller-views/entry-0.md"))?;
        assert!(
            text.contains("`value` (parameter 0) ← entry `J` (parameter 0)"),
            "{text}"
        );
        assert!(folder.join("caller-views/README.md").exists());
        Ok(())
    }

    #[test]
    fn source_tree_exposes_shared_deep_specialized_helper_sources() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let input = tmp.path().join("handlers");
        let output = tmp.path().join("readable");
        fs::create_dir_all(&input)?;
        fs::write(input.join("one.js"), "const capturedHandler=()=>0;")?;
        let original = tmp.path().join("original.js");
        fs::write(
            &original,
            "const deep=function(selector, value) {if(selector===7)return value+1;return value-1;};             const mid=(x)=>deep(7,x);const api={};api.enter=(input)=>mid(input);",
        )?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 12,
            format_output: true,
            context_source: Some(original.clone()),
            origin_source: None,
            caller_view_entry: Some("enter".into()),
        })?;
        let dir = output.join("lexical-context");
        let index: serde_json::Value =
            serde_json::from_slice(&fs::read(dir.join("context.json"))?)?;
        assert_eq!(index["caller_view_count"], 1);
        assert_eq!(index["graph_specialization_count"], 1);
        // Older captured-handler specialization metadata is independent:
        // this one is linked by original source-level callsite spans.
        let row = &index["graph_specializations"][0];
        assert_eq!(row["helper"], "deep");
        assert_eq!(row["arguments"], serde_json::json!([[0, "7"]]));
        assert!(row["deobfuscation_error"].is_null());
        let path = row["path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("no source path"))?;
        let original_path = row["original_path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("no original source path"))?;
        let readable = fs::read_to_string(dir.join(path))?;
        let original_body = fs::read_to_string(dir.join(original_path))?;
        assert!(readable.contains("return value + 1") || readable.contains("return value+1"));
        assert!(!readable.contains("selector===7") && !readable.contains("selector === 7"));
        assert!(original_body.contains("selector===7"));
        let index = fs::read_to_string(dir.join("caller-views/specializations/README.md"))?;
        assert!(index.contains("Largest source reductions"));
        assert!(index.contains("deep — original bytes"));
        assert!(index.contains("depth 2"));
        assert_eq!(row["source_depth"], 2);
        assert!(fs::read_to_string(dir.join("caller-views/README.md"))?
            .contains("specializations/README.md"));
        assert!(fs::read_to_string(output.join("README.md"))?
            .contains("callsite-specialized readable helper bodies"));
        assert!(fs::read_to_string(&original)?.contains("selector===7"));
        Ok(())
    }

    #[test]
    fn source_tree_propagates_a_literal_through_a_helper_without_literal_calls() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let input = tmp.path().join("handlers");
        let output = tmp.path().join("tree");
        fs::create_dir_all(&input)?;
        fs::write(input.join("handler.js"), "const capturedHandler = () => 0;")?;
        let original = tmp.path().join("original.js");
        fs::write(
            &original,
            "const last=(selector,value)=>selector===5?value+1:value-1;             const middle=(forwarded,input)=>last(forwarded,input);             const api={};api.enter=(input)=>middle(5,input);",
        )?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 12,
            format_output: true,
            context_source: Some(original),
            origin_source: None,
            caller_view_entry: Some("enter".into()),
        })?;
        let context = output.join("lexical-context");
        let info: serde_json::Value =
            serde_json::from_slice(&fs::read(context.join("context.json"))?)?;
        let Some(rows) = info["graph_specializations"].as_array() else {
            return Err(anyhow::anyhow!("missing graph variants"));
        };
        let leaf = rows
            .iter()
            .find(|row| row["helper"] == "last")
            .ok_or_else(|| anyhow::anyhow!("forwarded literal did not reach leaf"))?;
        assert_eq!(leaf["arguments"], serde_json::json!([[0, "5"]]));
        assert_eq!(leaf["source_depth"], 2);
        assert_eq!(leaf["example_call_chain"].as_array().map(Vec::len), Some(2));
        let path = leaf["path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("leaf file path missing"))?;
        let source = fs::read_to_string(context.join(path))?;
        assert!(
            source.contains("value + 1") || source.contains("value+1"),
            "{source}"
        );
        assert!(!source.contains("selector===5") && !source.contains("selector === 5"));
        Ok(())
    }

    #[test]
    fn source_tree_traces_function_call_wrapper_and_exposes_true_callee() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let input = tmp.path().join("handlers");
        let output = tmp.path().join("tree");
        fs::create_dir_all(&input)?;
        fs::write(input.join("handler.js"), "const capturedHandler=()=>0;")?;
        let original = tmp.path().join("original.js");
        fs::write(
            &original,
            "const hV=(opcode,selector,flag)=>opcode===88&&selector===4&&flag?'YES':'NO';\
             const U6=(selector,flag)=>hV.call(this,88,selector,!!flag);\
             const api={};api.aoF_=()=>U6(4,1);",
        )?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 12,
            format_output: true,
            context_source: Some(original),
            origin_source: None,
            caller_view_entry: Some("aoF_".into()),
        })?;
        let context = output.join("lexical-context");
        let info: serde_json::Value =
            serde_json::from_slice(&fs::read(context.join("context.json"))?)?;
        let edges = info["caller_views"][0]["reachable_edges"]
            .as_array()
            .ok_or_else(|| anyhow::anyhow!("no resolved call graph"))?;
        let edge = edges
            .iter()
            .find(|edge| edge["call"]["callee"] == "hV")
            .ok_or_else(|| anyhow::anyhow!("hV was not linked from U6"))?;
        assert_eq!(edge["call"]["kind"], "function.call");
        assert_eq!(edge["call"]["this_argument"], "this");
        assert_eq!(edge["call"]["arguments"][0]["expression"], "88");
        let leaf = info["graph_specializations"]
            .as_array()
            .and_then(|rows| rows.iter().find(|row| row["helper"] == "hV"))
            .ok_or_else(|| anyhow::anyhow!("missing source-specialized hV"))?;
        assert_eq!(
            leaf["arguments"],
            serde_json::json!([[0, "88"], [1, "4"], [2, "true"]])
        );
        assert_eq!(leaf["example_call_chain"].as_array().map(Vec::len), Some(2));
        let path = leaf["path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("hV source path missing"))?;
        let readable = fs::read_to_string(context.join(path))?;
        assert!(readable.contains("YES"), "{readable}");
        Ok(())
    }

    #[test]
    fn source_tree_computes_original_argument_expression_through_two_callers() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let input = tmp.path().join("handlers");
        let output = tmp.path().join("tree");
        fs::create_dir_all(&input)?;
        fs::write(input.join("handler.js"), "const capturedHandler = () => 0;")?;
        let original = tmp.path().join("original.js");
        fs::write(
            &original,
            "const leaf=(selector,flag)=>selector===11?flag+1:flag-1;             const outer=(a,b)=>leaf((a|0)+(b|0),b>4);             const middle=(x,y)=>outer(x,y);             const api={};api.enter=()=>middle(4,7);",
        )?;
        run_source_tree(SourceTreeArgs {
            input,
            output: output.clone(),
            max_iterations: 12,
            format_output: true,
            context_source: Some(original),
            origin_source: None,
            caller_view_entry: Some("enter".into()),
        })?;
        let context = output.join("lexical-context");
        let info: serde_json::Value =
            serde_json::from_slice(&fs::read(context.join("context.json"))?)?;
        let leaf = info["graph_specializations"]
            .as_array()
            .and_then(|rows| rows.iter().find(|row| row["helper"] == "leaf"))
            .ok_or_else(|| anyhow::anyhow!("computed leaf missing in source tree"))?;
        assert_eq!(
            leaf["arguments"],
            serde_json::json!([[0, "11"], [1, "true"]])
        );
        assert_eq!(leaf["example_call_chain"].as_array().map(Vec::len), Some(3));
        let path = leaf["path"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("missing computed leaf source path"))?;
        let source = fs::read_to_string(context.join(path))?;
        assert!(source.contains("__redox_lexical_helper"), "{source}");
        assert!(
            !source.contains("selector===11") && !source.contains("selector === 11"),
            "{source}"
        );
        assert!(
            leaf["semantic_rewrites"].as_u64().is_some_and(|n| n > 0),
            "{leaf}"
        );
        Ok(())
    }

    #[test]
    fn source_tree_cannot_overwrite_or_contain_original() -> Result<()> {
        let temp = tempfile::tempdir()?;
        let input = temp.path().join("raw");
        fs::create_dir_all(&input)?;
        fs::write(input.join("a.js"), "const a=1;")?;
        let error = run_source_tree(SourceTreeArgs {
            input: input.clone(),
            output: input.join("out"),
            max_iterations: 1,
            format_output: false,
            context_source: None,
            origin_source: None,
            caller_view_entry: None,
        });
        assert!(error.is_err());
        assert_eq!(fs::read_to_string(input.join("a.js"))?, "const a=1;");
        Ok(())
    }
}
