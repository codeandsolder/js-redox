use anyhow::{Context, Result};
use clap::Parser;
use std::{fs, path::PathBuf, time::Duration};
use wasm_redox::wax_view::{write_wax_view, WaxViewOrigin};
use work_budget::{BudgetLimits, WorkBudget};

#[derive(Debug, Parser)]
#[command(about = "Recover readable, provenance-friendly views of WebAssembly modules")]
struct Args {
    input: PathBuf,

    #[arg(long)]
    output_dir: PathBuf,

    #[arg(long, default_value = "wax")]
    wax: PathBuf,

    #[arg(long)]
    skip_wax: bool,

    #[arg(long)]
    skip_deep: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let bytes = fs::read(&args.input).with_context(|| format!("read {}", args.input.display()))?;
    let budget = WorkBudget::new(
        format!("wasm-redox:{}", args.input.display()),
        BudgetLimits::wall_time(Duration::from_secs(180)),
    );
    let report = wasm_redox::analyze(&bytes, &budget)?;
    let wat = wasm_redox::folded_wat(&bytes, &budget)?;

    fs::create_dir_all(&args.output_dir)
        .with_context(|| format!("create {}", args.output_dir.display()))?;
    let report_path = args.output_dir.join("module.report.json");
    let wat_path = args.output_dir.join("module.readable.wat");

    fs::write(&report_path, serde_json::to_vec_pretty(&report)?)
        .with_context(|| format!("write {}", report_path.display()))?;
    fs::write(&wat_path, wat).with_context(|| format!("write {}", wat_path.display()))?;

    if !args.skip_deep {
        let deep = wasm_redox::deep_analyze(&bytes, &report, &budget)?;
        let deep_path = args.output_dir.join("module.deep.json");
        fs::write(&deep_path, serde_json::to_vec_pretty(&deep)?)
            .with_context(|| format!("write {}", deep_path.display()))?;
    }

    if !args.skip_wax {
        let wax_budget = budget.child(
            format!("wax:{}", args.input.display()),
            BudgetLimits::wall_time(Duration::from_secs(180)),
        );
        write_wax_view(
            &args.input,
            &args.output_dir.join("module.readable.wax"),
            &args.wax,
            &wax_budget,
            WaxViewOrigin::Standalone,
        )?;
    }

    println!(
        "{}: {} bytes, {} imports, {} exports, {} defined functions",
        report.sha256,
        report.byte_len,
        report.imports.len(),
        report.exports.len(),
        report.sections.defined_functions
    );
    Ok(())
}
