use anyhow::{bail, Context, Result};
use clap::Parser;
use serde::Serialize;
use std::{fs, path::PathBuf};

#[derive(Parser, Debug)]
#[command(about = "Prove JavaScript-side WebAssembly import DataView.setUint32 call shapes")]
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
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let shapes = match (
        args.import_module.as_deref(),
        args.import_name.as_deref(),
        args.offset,
    ) {
        (Some(import_module), Some(import_name), Some(offset)) => {
            jsvm_lift::wasm_import_semantics::proven_wasm_import_data_view_set_u32_shape_at_offset(
                &source,
                import_module,
                import_name,
                offset,
            )
            .into_iter()
            .collect()
        }
        (None, None, None) => {
            jsvm_lift::wasm_import_semantics::proven_wasm_import_data_view_set_u32_shapes(&source)
        }
        _ => bail!("--import-module, --import-name and --offset must be supplied together"),
    };
    let report = Report {
        schema: "jsvm-wasm-import-semantics/v1",
        source: args.input.display().to_string(),
        shapes,
    };
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}
