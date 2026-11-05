use anyhow::{ensure, Context, Result};
use clap::Parser;
use jsvm_lift::{
    forwarding_semantics::structurally_proven_lazy_registry_read_calls,
    lazy_cell::{
        proven_slow_lazy_cell_captured_handler_install,
        proven_slow_lazy_cell_exact_registry_assignments, proven_slow_lazy_cell_factory_call,
        proven_slow_lazy_cell_registry_assignment, proven_slow_lazy_cell_update_state,
        structurally_proven_slow_lazy_cell_factory_shapes,
    },
    lexical_mutation::audit_lexical_binding_mutation,
    receiver_identity::{
        structurally_proven_prototype_method_phase_closures,
        structurally_proven_runtime_origin_flow,
    },
    registry_identity::proven_origin_registry_handler_installs,
};
use jsvm_lift::{js_format::format_source, safe_deob::SourceMode, sha256_hex};
use oxc_allocator::Allocator;
use oxc_semantic::SemanticBuilder;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use serde_json::json;
use std::{fs, path::PathBuf, time::Duration};
use work_budget::{BudgetLimits, WorkBudget};

/// Deliberately separate from the cheap browser-project scan: proving
/// constructor-origin and wrapper-capture provenance can be expensive.
#[derive(Parser, Debug)]
#[command(
    version,
    about = "Explain exact-key lazy-cell handler captures without claiming executed dispatch"
)]
struct Args {
    /// Original or recovered JavaScript child (byte offsets refer to these exact bytes).
    input: PathBuf,
    /// New/empty directory containing JSON proofs and readable captured handlers.
    #[arg(long)]
    output: PathBuf,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize)]
struct HandlerCapture {
    exact_key: i64,
    factory_call: [u32; 2],
    handler: [u32; 2],
    install_call: [u32; 2],
    caller_handler_parameter_index: usize,
    allocation: [u32; 2],
    constructor: [u32; 2],
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let allocator = Allocator::default();
    let parsed = parse_program(
        &allocator,
        &source,
        SourceMode::for_path(&args.input).source_type(),
    );
    anyhow::ensure!(parsed.is_clean(), "unparseable input");
    let result = SemanticBuilder::new()
        .with_build_nodes(true)
        .with_cfg(true)
        .with_check_syntax_error(true)
        .build(&parsed.program);
    anyhow::ensure!(result.diagnostics.is_empty(), "semantic diagnostics");
    let semantic = &result.semantic;
    let scoping = semantic.scoping();
    let budget = WorkBudget::new(
        "lazy-cell-proof-inventory",
        BudgetLimits::wall_time(Duration::from_secs(180)),
    );
    let flow = structurally_proven_runtime_origin_flow(&parsed.program, semantic, &budget)?;
    let shapes = structurally_proven_slow_lazy_cell_factory_shapes(&parsed.program, scoping);
    // Report unresolved mutation hazards on the captured phase closure.
    // A syntactically unique assignment is not an immutable-value theorem.
    let phase_closures =
        structurally_proven_prototype_method_phase_closures(&parsed.program, scoping, &budget)?;
    let mut phase_mutation_audits = Vec::new();
    for closure in phase_closures.iter().filter(|closure| {
        shapes
            .iter()
            .any(|shape| shape.phase_binding_symbol == closure.phase_binding_symbol)
    }) {
        let audit = audit_lexical_binding_mutation(
            semantic,
            closure.phase_binding_symbol,
            oxc_span::Span::new(closure.phase_assignment_start, closure.phase_assignment_end),
            &budget,
        )?;
        phase_mutation_audits.push(json!({
            "phase_assignment": [closure.phase_assignment_start, closure.phase_assignment_end],
            "phase_function": [closure.phase_function_start, closure.phase_function_end],
            "equal_value": closure.equal_value,
            "unequal_value": closure.unequal_value,
            "explicit_writes": audit.explicit_writes.iter().map(|span| [span.start,span.end]).collect::<Vec<_>>(),
            "unique_expected_write": audit.unique_expected_write,
            "lexical_direct_eval_calls": audit.lexical_direct_eval_calls.iter().map(|site| json!({
                "span":[site.span.start,site.span.end],
                "enclosing_function":site.enclosing_function.map(|s|[s.start,s.end]),
            })).collect::<Vec<_>>(),
            "lexical_with_statements": audit.lexical_with_statements.iter().map(|site| json!({
                "span":[site.span.start,site.span.end],
                "enclosing_function":site.enclosing_function.map(|s|[s.start,s.end]),
            })).collect::<Vec<_>>(),
            "root_scope_binding": audit.root_scope_binding,
            "source_mutation_isolated": audit.source_mutation_isolated,
            "initialization_before_later_capture_proven": false,
        }));
    }
    let reads = structurally_proven_lazy_registry_read_calls(&parsed.program, scoping, &budget)?;
    let installs =
        proven_origin_registry_handler_installs(&parsed.program, scoping, &flow, &budget)?;
    eprintln!(
        "shapes={} direct_calls={} lazy_reads={} installs={}",
        shapes.len(),
        flow.direct_calls.len(),
        reads.len(),
        installs.len()
    );
    let mut proven_calls = Vec::new();
    let mut with_registry = Vec::new();
    let mut with_update = Vec::new();
    let mut exact = Vec::new();
    let mut captured_handlers = Vec::new();
    for call in &flow.direct_calls {
        budget.consume(1)?;
        if !shapes.iter().any(|shape| {
            shape.function_start == call.callee.function_start
                && shape.function_end == call.callee.function_end
        }) {
            continue;
        }
        let Some(factory) =
            proven_slow_lazy_cell_factory_call(&source, &parsed.program, semantic, call)
        else {
            continue;
        };
        proven_calls.push(json!({"call":[call.call_start,call.call_end], "factory":[call.callee.function_start,call.callee.function_end],"arg_int":call.exact_integer_arguments}));
        if let Some(update) =
            proven_slow_lazy_cell_update_state(&parsed.program, semantic, &factory)
        {
            with_update.push(json!({"call":[call.call_start,call.call_end],"initial":update.initial_state_value,"updated":update.post_update_state_value}));
        }
        if let Some(registry) =
            proven_slow_lazy_cell_registry_assignment(&parsed.program, semantic, &factory)
        {
            with_registry.push(json!({"call":[call.call_start,call.call_end],"path":registry.registry_path,"key_span":[registry.key_start,registry.key_end]}));
            for item in proven_slow_lazy_cell_exact_registry_assignments(
                &source,
                &parsed.program,
                semantic,
                &flow,
                &registry,
            ) {
                budget.consume(1)?;
                for install in installs.iter().filter(|install| {
                    install.exact_key == item.exact_key_value
                        && install.origin.allocation_start == factory.call.callee.allocation_start
                        && install.origin.allocation_end == factory.call.callee.allocation_end
                        && install.origin.constructor_start == factory.call.callee.constructor_start
                        && install.origin.constructor_end == factory.call.callee.constructor_end
                        && install.install.registry_path == registry.registry_path
                }) {
                    budget.consume(1)?;
                    if let Some(proven) = proven_slow_lazy_cell_captured_handler_install(
                        &source,
                        &parsed.program,
                        semantic,
                        &item,
                        install,
                    ) {
                        captured_handlers.push(HandlerCapture {
                            exact_key: proven.install.exact_key,
                            factory_call: [factory.call.call_start, factory.call.call_end],
                            handler: [
                                proven.install.install.handler_start,
                                proven.install.install.handler_end,
                            ],
                            install_call: [
                                proven.install.install.call_start,
                                proven.install.install.call_end,
                            ],
                            caller_handler_parameter_index: proven.caller_handler_parameter_index,
                            allocation: [
                                proven.install.origin.allocation_start,
                                proven.install.origin.allocation_end,
                            ],
                            constructor: [
                                proven.install.origin.constructor_start,
                                proven.install.origin.constructor_end,
                            ],
                        });
                    }
                }
                exact.push(json!({"call":[call.call_start,call.call_end],"key":item.exact_key_value,
                  "origin":[item.caller.callee.allocation_start,item.caller.callee.allocation_end],
                  "chain":item.provenance_calls.iter().map(|v| [v.call_start,v.call_end]).collect::<Vec<_>>()}));
            }
        }
    }
    captured_handlers.sort();
    captured_handlers.dedup();

    // Associate dynamic-source sites with captured functions only when the
    // exact source interval contains the entire hazard. This is provenance,
    // not an assertion that the handler was invoked or the site was reached.
    for audit in &mut phase_mutation_audits {
        for kind in ["lexical_direct_eval_calls", "lexical_with_statements"] {
            if let Some(sites) = audit
                .get_mut(kind)
                .and_then(serde_json::Value::as_array_mut)
            {
                for site in sites {
                    budget.consume(1)?;
                    let (Some(start), Some(end)) =
                        (site["span"][0].as_u64(), site["span"][1].as_u64())
                    else {
                        continue;
                    };
                    let containing_keys = captured_handlers
                        .iter()
                        .filter(|capture| {
                            u64::from(capture.handler[0]) <= start
                                && end <= u64::from(capture.handler[1])
                        })
                        .map(|capture| capture.exact_key)
                        .collect::<Vec<_>>();
                    site["containing_captured_handler_keys"] = json!(containing_keys);
                    site["invocation_witnessed"] = json!(false);
                }
            }
        }
    }

    let source_sha256 = sha256_hex(source.as_bytes());
    let report = json!({
        "schema": "jsvm-lazy-cell-proof/v2",
        "input": args.input,
        "source_sha256": source_sha256,
        "source_bytes": source.len(),
        "shape_count": shapes.len(),
        "shapes": shapes.iter().map(|s|json!({
            "span":[s.function_start,s.function_end],
            "slot":s.handler_slot,
            "state_param":s.state_parameter_index,
            "handler_param":s.handler_parameter_index,
            "resolver":s.resolver_property
        })).collect::<Vec<_>>(),
        "proven_calls_count":proven_calls.len(),"proven_calls":proven_calls,
        "registry_bindings_count":with_registry.len(),"registry_bindings":with_registry,
        "update_state_count":with_update.len(),"update_state":with_update,
        "captured_handler_count":captured_handlers.len(), "captured_handlers":captured_handlers,
        "exact_assignment_count":exact.len(),"exact_assignments":exact,
        "lazy_read_count":reads.len(),"origin_handler_installs_count":installs.len(),
        "phase_binding_mutation_audits": phase_mutation_audits,
        "limitations": [
            "Binding mutation hazards include scope-visible eval and with even when no second explicit assignment is found.",
            "No assertion that an indirect call executed or a selected branch was taken.",
            "No proof of registry-slot persistence from installation to read.",
            "No proof that a lazy-cell returned the captured original handler at a particular runtime phase.",
            "Source spans refer to the exact SHA-256 input, not the formatted view."
        ]
    });

    if args.output.exists() {
        ensure!(
            fs::read_dir(&args.output)
                .with_context(|| format!("reading output directory {}", args.output.display()))?
                .next()
                .is_none(),
            "output directory is not empty: {}",
            args.output.display()
        );
    }
    let handlers_dir = args.output.join("handlers");
    fs::create_dir_all(&handlers_dir)?;
    fs::write(
        args.output.join("analysis.json"),
        serde_json::to_vec_pretty(&report)?,
    )?;

    let mut index = String::from(
        r#"# Proven lazy-cell handler captures

These are the original functions proven to flow into lazy-cell wrappers.
They are **not** necessarily the functions executed by a specific browser invocation.

Source identity and exact byte spans are in [analysis.json](analysis.json).
Readable files are views, not executable devirtualizations.
See the phase binding mutation audits in analysis.json: each dynamic-code site
includes its exact containing captured handler keys when structural provenance exists.
This is containment only, not evidence that a handler or the dynamic-code site executed.
A syntactically unique assignment is not sufficient when direct eval can reach the binding.

| Exact key | Handler function | Original source bytes | Factory call bytes |
|---:|---|---|---|
"#,
    );
    let mut written = std::collections::BTreeSet::new();
    for capture in &captured_handlers {
        budget.consume(1)?;
        let [start, end] = capture.handler;
        let name = format!("key-{}-source-{}-{}.js", capture.exact_key, start, end);
        if written.insert(name.clone()) {
            let source_code = source
                .get(start as usize..end as usize)
                .with_context(|| format!("invalid handler source span {start}..{end}"))?;
            let wrapped = format!("const capturedHandler = {source_code};\n");
            let readable = format_source(&wrapped, &budget)
                .with_context(|| format!("formatting handler key {}", capture.exact_key))?;
            let header = format!(
                "// Readable, non-devirtualized provenance view. Original SHA-256: {source_sha256}\n                 // Handler key: {}. Original bytes: {start}..{end}. Factory call: {}..{}.\n                 // This proves capture into a wrapper, not which handler ran.\n",
                capture.exact_key, capture.factory_call[0], capture.factory_call[1]
            );
            fs::write(handlers_dir.join(&name), format!("{header}{readable}"))?;
        }
        index.push_str(&format!(
            "| {} | [view](handlers/{}) | {}..{} | {}..{} |\n",
            capture.exact_key, name, start, end, capture.factory_call[0], capture.factory_call[1]
        ));
    }
    index.push_str(
        "\n## Dynamic-source lexical mutation hazards\n\n\
         The following sites are syntactically capable of affecting captured bindings.\n\
         Captured-handler links prove only exact source-span containment,\n\
         **not handler execution, temporal reachability or mutation**.\n\n\
         | Phase function bytes | Site kind | Site bytes | Enclosing function bytes | Containing captured functions |\n\
         |---|---|---|---|---|\n",
    );
    let mut hazard_count = 0_usize;
    for audit in &phase_mutation_audits {
        let phase_start = audit["phase_function"][0].as_u64();
        let phase_end = audit["phase_function"][1].as_u64();
        let phase_label = match (phase_start, phase_end) {
            (Some(start), Some(end)) => format!("{start}..{end}"),
            _ => String::from("unknown"),
        };
        for (kind, label) in [
            ("lexical_direct_eval_calls", "direct eval"),
            ("lexical_with_statements", "with"),
        ] {
            let Some(sites) = audit.get(kind).and_then(serde_json::Value::as_array) else {
                continue;
            };
            for site in sites {
                budget.consume(1)?;
                let (Some(start), Some(end)) = (site["span"][0].as_u64(), site["span"][1].as_u64())
                else {
                    continue;
                };
                hazard_count += 1;
                let enclosing = match (
                    site["enclosing_function"][0].as_u64(),
                    site["enclosing_function"][1].as_u64(),
                ) {
                    (Some(start), Some(end)) => format!("{start}..{end}"),
                    _ => String::from("top-level / unknown"),
                };
                let matching_handlers = captured_handlers
                    .iter()
                    .filter(|capture| {
                        u64::from(capture.handler[0]) <= start
                            && end <= u64::from(capture.handler[1])
                    })
                    .map(|capture| {
                        format!(
                            "[key {}](handlers/key-{}-source-{}-{}.js)",
                            capture.exact_key,
                            capture.exact_key,
                            capture.handler[0],
                            capture.handler[1],
                        )
                    })
                    .collect::<Vec<_>>();
                let related = if matching_handlers.is_empty() {
                    String::from("none proven")
                } else {
                    matching_handlers.join(", ")
                };
                index.push_str(&format!(
                    "| {phase_label} | {label} | {start}..{end} | {enclosing} | {related} |\n"
                ));
            }
        }
    }
    if hazard_count == 0 {
        index.push_str("| — | No syntactic hazard found | — | — | — |\n");
    }
    fs::write(args.output.join("README.md"), index)?;
    println!(
        "Proved {} captured handlers across {} exact-key assignment paths; report: {}",
        captured_handlers.len(),
        exact.len(),
        args.output.display()
    );
    Ok(())
}
