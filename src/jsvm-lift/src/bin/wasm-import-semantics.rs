use anyhow::{bail, Context, Result};
use clap::Parser;
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(Parser, Debug)]
#[command(
    about = "Prove JavaScript-side WebAssembly import write shapes and import-object instantiation sites"
)]
struct Args {
    input: PathBuf,
    #[arg(long, requires_all = ["import_name", "offset"])]
    import_module: Option<String>,
    #[arg(long, requires_all = ["import_module", "offset"])]
    import_name: Option<String>,
    #[arg(long, requires_all = ["import_module", "import_name"])]
    offset: Option<u32>,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    source: String,
    shapes: Vec<jsvm_lift::wasm_import_semantics::WasmImportDataViewSetU32Shape>,
    import_object_usages: Vec<jsvm_lift::wasm_import_semantics::WasmImportObjectUsage>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let analysis = match (
        args.import_module.as_deref(),
        args.import_name.as_deref(),
        args.offset,
    ) {
        (Some(import_module), Some(import_name), Some(offset)) => {
            jsvm_lift::wasm_import_semantics::proven_wasm_import_semantics_for(
                &source,
                import_module,
                import_name,
                offset,
            )
        }
        (None, None, None) => {
            jsvm_lift::wasm_import_semantics::proven_wasm_import_semantics(&source)
        }
        _ => bail!("--import-module, --import-name and --offset must be supplied together"),
    };
    let report = Report {
        schema: "jsvm-wasm-import-semantics/v2",
        source: args.input.display().to_string(),
        shapes: analysis.shapes,
        import_object_usages: analysis.import_object_usages,
    };
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
