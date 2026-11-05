use anyhow::{Context, Result};
use clap::{Args as ClapArgs, Parser, Subcommand, ValueEnum};
use jsvm_lift::{
    analysis_budget::{AnalysisBudgets, AnalysisOperation},
    project_deob::{materialize_project_deobfuscation, ProjectDeobOptions},
    safe_deob::{deobfuscate_source, SourceMode},
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
    let mut changed = 0usize;
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
                if outcome.report.changed {
                    changed += 1;
                }
                let had_semantic_rewrite = outcome
                    .report
                    .transforms
                    .iter()
                    .any(|(kind, count)| kind != "presentation_codegen" && *count > 0);
                let status = if had_semantic_rewrite {
                    "transformed"
                } else if outcome.report.changed {
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
        "changed_count": changed,
        "unrecovered_count": failed,
        "transforms": total_transforms,
        "files": rows,
        "presentation_formatted": args.format_output,
    });
    let mut summary_text = serde_json::to_string_pretty(&summary)?;
    summary_text.push('\n');
    fs::write(out.join("reconstruction.json"), summary_text)?;
    md.push_str("\nMachine-readable summary: [reconstruction.json](reconstruction.json).\n");
    fs::write(out.join("README.md"), md)?;
    println!(
        "{}",
        json!({
            "source_count": summary["source_count"],
            "changed_count": changed,
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
    use super::{run_source_tree, SourceTreeArgs};
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
        })?;

        let index: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(output.join("reconstruction.json"))?)?;
        assert_eq!(index["source_count"], 2);
        assert_eq!(index["unrecovered_count"], 0);
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
        });
        assert!(error.is_err());
        assert_eq!(fs::read_to_string(input.join("a.js"))?, "const a=1;");
        Ok(())
    }
}
