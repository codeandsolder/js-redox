use std::{collections::{BTreeMap, BTreeSet}, env, fs, process, time::Instant};
use zipp_vm::embed::compile_script;

fn main() {
    let path = env::args().nth(1).expect("usage: zipp-knitsail-probe <file.js>");
    let source = fs::read_to_string(&path).expect("read JS");
    let start = Instant::now();
    let mut state = match compile_script(&source) {
        Ok(state) => state,
        Err(err) => { eprintln!("COMPILE_ERROR:{err}"); process::exit(2); }
    };
    let compiled_ms = start.elapsed().as_millis();
    state.set_limits(2_000_000, None);
    state.set_dynamic_code_limits(1 << 20, 1 << 22, 1000, 500, 500);
    state.start_trace(400_000);
    let execution = state.run_init();
    let executed_ms = start.elapsed().as_millis().saturating_sub(compiled_ms);
    let steps = state.steps_used();
    let truncated = state.trace_truncated();
    let rows = state.finish_trace(0);
    let output = state.take_output();
    match &execution {
        Ok(result) => eprintln!("EXECUTION:ok:{result:?}"),
        Err(err) => eprintln!("EXECUTION:error:{err}"),
    }
    for line in output { println!("{line}"); }
    match rows {
        None => eprintln!("TRACE:none; steps={steps}; truncated={truncated}; compile_ms={compiled_ms}; execute_ms={executed_ms}"),
        Some(rows) => {
            let mut pcs = BTreeSet::new();
            let mut opcodes = BTreeMap::<u8, usize>::new();
            let mut edges = BTreeSet::<(u64, u64)>::new();
            for (idx, row) in rows.iter().enumerate() {
                pcs.insert(row.pc);
                *opcodes.entry(row.opcode).or_default() += 1;
                if let Some(next) = rows.get(idx + 1) { edges.insert((row.pc, next.pc)); }
            }
            eprintln!("TRACE:rows={};unique_pcs={};unique_pc_edges={};steps={steps};truncated={truncated};compile_ms={compiled_ms};execute_ms={executed_ms};opcodes={opcodes:?}", rows.len(), pcs.len(), edges.len());
        }
    }
    if execution.is_err() { process::exit(3); }
}
