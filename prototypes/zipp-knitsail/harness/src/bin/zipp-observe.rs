//! Observes native ZIPP dynamic-code input without rewriting JavaScript.
//! The source digest identifies the exact host-supplied initial script, not
//! necessarily the origin of every function subsequently installed at runtime.
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{env, fs, io, path::PathBuf};
use zipp_vm::embed::{
    compile_script, DynamicCallerOrigin, DynamicSourceKind, DynamicSourceOutcome,
};

fn hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        output.push(HEX[(byte >> 4) as usize] as char);
        output.push(HEX[(byte & 0x0f) as usize] as char);
    }
    output
}

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn outcome(result: &Result<(), String>) -> Value {
    match result {
        Ok(()) => json!({"ok": true}),
        Err(message) => json!({"ok": false, "error": message}),
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = env::args_os().skip(1);
    let original = args
        .next()
        .ok_or("Usage: zipp-observe ORIGINAL.js [ENTRY.js]")?;
    let entry = args.next().map(PathBuf::from);
    if args.next().is_some() {
        return Err("Usage: zipp-observe ORIGINAL.js [ENTRY.js]".into());
    }
    let bytes = fs::read(&original)?;
    let source = std::str::from_utf8(&bytes)?;
    let entry_source = entry.as_ref().map(fs::read_to_string).transpose()?;
    let mut state = compile_script(source).map_err(io::Error::other)?;
    state.set_limits(10_000_000, None);
    state.set_dynamic_code_limits(1 << 20, 1 << 25, 10_000, 5_000, 5_000);
    state.start_dynamic_source_capture(10_000, 32 << 20);
    let initial = state.run_init().map(|_| ());
    let entry_result = if initial.is_ok() {
        entry_source
            .as_deref()
            .map(|text| state.eval_in_context(text).map(|_| ()))
    } else {
        None
    };
    let capture = state
        .take_dynamic_source_capture()
        .ok_or("ZIPP source observer was not enabled")?;
    let events: Vec<_> = capture
        .events
        .iter()
        .enumerate()
        .map(|(index, event)| {
            let kind = match event.kind {
                DynamicSourceKind::DirectEval => "direct-eval",
                DynamicSourceKind::IndirectEvalOrHost => "indirect-or-host",
                DynamicSourceKind::FunctionConstructor => "function-constructor",
            };
            let caller = event.caller.map(|caller| {
                json!({
                    "functionId": caller.function_id,
                    "origin": match caller.origin {
                        DynamicCallerOrigin::InitialProgram => "initial-program",
                        DynamicCallerOrigin::RuntimeInstalled => "runtime-installed",
                    },
                    "instructionIp": caller.instruction_ip,
                    "line": caller.line,
                    "column": caller.column,
                })
            });
            let event_outcome = event.outcome.as_ref().map(|outcome| match outcome {
                DynamicSourceOutcome::Returned { type_name } => {
                    json!({"status": "returned", "type": type_name})
                }
                DynamicSourceOutcome::Threw => json!({"status": "threw"}),
            });
            json!({
                "index": index,
                "kind": kind,
                "sourceHex": hex(&event.source_bytes),
                "caller": caller,
                "outcome": event_outcome,
            })
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schemaVersion": 2,
            "engine": "zipp",
            "sourceSha256": digest(&bytes),
            "truncated": capture.truncated,
            "execution": {
                "initial": outcome(&initial),
                "entry": entry_result.as_ref().map(outcome),
            },
            "events": events,
        }))?
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("zipp-observe: {error}");
        std::process::exit(1);
    }
}
