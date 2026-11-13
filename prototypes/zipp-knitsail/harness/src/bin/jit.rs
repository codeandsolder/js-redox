use std::{env, fs, process, time::Instant};
use zipp_vm::embed::compile_script;

fn main() {
    let path = env::args().nth(1).expect("usage: jit <file.js>");
    let src = fs::read_to_string(&path).expect("read JS");
    let t = Instant::now();
    let mut vm = compile_script(&src).unwrap_or_else(|err| {
        eprintln!("COMPILE_ERROR:{err}");
        process::exit(2);
    });
    let compile_ms = t.elapsed().as_millis();
    let t = Instant::now();
    let run = vm.run_init();
    let elapsed_ms = t.elapsed().as_millis();
    eprintln!("RUN:compile_ms={compile_ms};execute_ms={elapsed_ms};result={run:?}");
    for l in vm.take_output() {
        println!("{l}");
    }
    if run.is_err() {
        process::exit(3);
    }
}
