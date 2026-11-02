use anyhow::{Context, Result};
use std::{env, fs, time::Duration};
use wasm_redox::state_machine::analyze_export_semantics;
use work_budget::{BudgetLimits, WorkBudget};

fn main() -> Result<()> {
    let path = env::args().nth(1).context("wasm")?;
    let export_name = env::args().nth(2).context("export")?;
    let bytes = fs::read(&path)?;
    let budget = WorkBudget::new(
        format!("state-machine:{path}:{export_name}"),
        BudgetLimits::wall_time(Duration::from_secs(180)),
    );
    let analysis = analyze_export_semantics(&bytes, &export_name, &budget)?;
    for machine in analysis.state_machines {
        println!(
            "MACHINE state=v{} dispatcher=block{} comparisons={} initial={:?}",
            machine.state_value, machine.dispatcher_block, machine.comparisons, machine.initial
        );
        println!(
            "  recovered_states={} unresolved_backedges={} data_forks={}",
            machine.graph.len(),
            machine.unresolved_backedges,
            machine.data_forks
        );
        for (from, to) in machine.graph.iter().take(64) {
            println!("  {from:10} -> {:?}", to);
        }
    }
    Ok(())
}
