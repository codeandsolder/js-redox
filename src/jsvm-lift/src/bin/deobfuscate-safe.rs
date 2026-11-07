use anyhow::{Context, Result};
use clap::{Args as ClapArgs, Parser, Subcommand, ValueEnum};
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    project_deob::{materialize_project_deobfuscation, ProjectDeobOptions},
    safe_deob::{deobfuscate_source, SourceMode},
    sha256_hex,
    source_tree_aliases::{explain_captured_handler_origins, explain_property_aliases},
    source_tree_context::reconstruct_context,
    source_tree_specialize::specialize_calls,
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
    /// Materialize safe source recovery/deobfuscation for a normalized capture project.
    Project(ProjectArgs),
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
struct ProjectArgs {
    project: PathBuf,
    #[arg(long)]
    jobs: Option<usize>,
    #[arg(long, default_value_t = 16)]
    max_iterations: usize,
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
                label,
                SourceMode::Auto,
                args.max_iterations,
                args.format_output,
                &budget,
            );
            let (code, transforms, error) = match outcome {
                Ok(rewritten) => (rewritten.source, rewritten.report.transforms, None),
                Err(error) => (
                    helper.source.clone(),
                    BTreeMap::new(),
                    Some(error.to_string()),
                ),
            };
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
        fs::write(folder.join("README.md"), &helper_index)?;
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
        fs::create_dir_all(folder.join("specializations"))?;
        let mut specializations_md =
            String::from("# Constant-argument specialized helper code\n\n");
        specializations_md.push_str(
            "Each file substitutes the exact constant arguments of a real handler call              into their original lexical parameter references, then runs static JS              deobfuscation. Original helpers remain available; these files are              callsite-specific analysis views inside the original closure context,              not independent runnable modules.\n\n"
        );
        let mut specialization_rows = Vec::new();
        for specialized in specializations {
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
            let relative = format!(
                "specializations/{}-{}-{suffix}.js",
                specialized.helper, hint
            );
            let budget = budgets.operation(
                AnalysisOperation::SafeDeobfuscation,
                format!("specialized {}", specialized.helper),
            );
            let (code, transforms, error) = match deobfuscate_source(
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
        if let Some(origin_path) = &args.origin_source {
            let raw_origin = fs::read_to_string(origin_path)
                .with_context(|| format!("reading raw capture origin {}", origin_path.display()))?;
            origin_source_sha256 = Some(sha256_hex(raw_origin.as_bytes()));
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
        let mut context_json = serde_json::to_string_pretty(&json!({
            "origin_source_sha256": origin_source_sha256,
            "origin_handler_count": origin_rows.len(),
            "origin_handlers": origin_rows,
            "schema": "jsvm-readable-lexical-context/v2",
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

fn main() -> Result<()> {
    match Args::parse().command {
        Command::Source(args) => run_source(args),
        Command::SourceTree(args) => run_source_tree(args),
        Command::Project(args) => run_project(args),
    }
}

#[cfg(test)]
mod tests {
    use super::{run_source_tree, sha256_hex, SourceTreeArgs};
    use anyhow::Result;
    use std::fs;

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
        })?;
        let context_dir = output.join("lexical-context");
        let metadata: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(context_dir.join("context.json"))?)?;
        assert_eq!(metadata["helper_count"], 2);
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
        });
        assert!(error.is_err());
        assert_eq!(fs::read_to_string(input.join("a.js"))?, "const a=1;");
        Ok(())
    }
}
