use std::{env, fs, process};
use zipp_vm::embed::compile_script;

fn main() {
    let filename = env::args().nth(1).expect("usage: witness <file.js>");
    let source = fs::read_to_string(filename).expect("read JS");
    let mut state = compile_script(&source).expect("compile JS");
    state.set_limits(2_000_000, None);
    state.start_property_witnesses(2000);
    let execution = state.run_init();
    for line in state.take_output() {
        println!("{line}");
    }
    let report = state.take_property_witnesses().expect("observer enabled");
    eprintln!(
        "WITNESSES count={} truncated={}",
        report.events.len(),
        report.truncated
    );
    for evt in report.events {
        eprintln!(
            "WITNESS fid={} name={:?} span={}..{} ip={} op={} bits={:#x} key={:?} object={}",
            evt.function_id,
            evt.function_name,
            evt.source_start,
            evt.source_end,
            evt.bytecode_ip,
            evt.operation,
            evt.key_bits,
            evt.key_text,
            evt.object_key
        );
    }
    if let Err(error) = execution {
        eprintln!("EXECUTION_ERROR: {error}");
        process::exit(2);
    }
    if report.truncated {
        process::exit(3);
    }
}
