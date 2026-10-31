use anyhow::Result;
use clap::Parser;
use jsvm_lift::wasm_resource_provenance::correlate_wasm_resource_provenance;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(about = "Correlate exact captured WASM responses with observed CDP script initiators")]
struct Args {
    project: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let summary = correlate_wasm_resource_provenance(&args.project)?;
    if summary.applicable {
        println!(
            "WASM runtime provenance: {} exact response observation(s), {} exact runtime initiator(s), {} unmatched, {} non-body observation(s)",
            summary.observations,
            summary.runtime_script_identities,
            summary.unmatched_wasm_events,
            summary.ignored_non_body_wasm_events,
        );
    } else {
        println!("WASM runtime provenance: unavailable for this capture");
    }
    Ok(())
}
