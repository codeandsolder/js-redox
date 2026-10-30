use serde::Serialize;
use std::panic::{catch_unwind, AssertUnwindSafe};
use waffle::{
    entity::EntityRef, ConstVal, FrontendOptions, Func, ImportKind, InterpContext,
    InterpMemoryAccessKind, InterpResult, Module, Operator, Table, ValueDef,
};

const DEFAULT_FUEL: u64 = 1_000_000;
const MAX_MEMORY_PAGES: usize = 2048;
const MAX_TABLE_ELEMENTS: usize = 100_000;

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum FreshEvalOutcome {
    Returned,
    Trap,
    OutOfFuel,
    UnsupportedOrPanicked,
    InvalidRequest,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FreshI32CallReport {
    pub schema: &'static str,
    pub function_index: usize,
    pub i32_args: Vec<u32>,
    pub fuel_limit: u64,
    pub fuel_consumed: Option<u64>,
    pub initial_memory_pages: Vec<usize>,
    pub final_memory_pages: Vec<usize>,
    pub outcome: FreshEvalOutcome,
    pub i32_result: Option<u32>,
}

impl FreshI32CallReport {
    pub fn proven_result(&self) -> Option<u32> {
        (self.outcome == FreshEvalOutcome::Returned)
            .then_some(self.i32_result)
            .flatten()
    }
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FreshI32Arg {
    Literal { value: u32 },
    StepResult { step: usize },
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FreshI32CallRequest {
    pub function_index: usize,
    pub i32_args: Vec<FreshI32Arg>,
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
pub struct FreshTableGrowRequest {
    pub table_index: usize,
    pub delta: u32,
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum FreshMemoryAccessKind {
    Read,
    Write,
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
pub struct FreshMemoryAccessReport {
    pub kind: FreshMemoryAccessKind,
    pub memory: usize,
    pub addr: u32,
    pub len: u32,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FreshI32SequenceStepReport {
    pub function_index: usize,
    pub resolved_i32_args: Vec<u32>,
    pub fuel_consumed: Option<u64>,
    pub initial_memory_pages: Vec<usize>,
    pub final_memory_pages: Vec<usize>,
    pub outcome: FreshEvalOutcome,
    pub i32_result: Option<u32>,
    pub memory_accesses: Vec<FreshMemoryAccessReport>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FreshI32SequenceReport {
    pub schema: &'static str,
    pub initial_table_grows: Vec<FreshTableGrowRequest>,
    pub calls: Vec<FreshI32CallRequest>,
    pub fuel_limit_per_call: u64,
    pub outcome: FreshEvalOutcome,
    pub steps: Vec<FreshI32SequenceStepReport>,
}

impl FreshI32SequenceReport {
    pub fn proven_result(&self, step: usize) -> Option<u32> {
        (self.outcome == FreshEvalOutcome::Returned)
            .then(|| self.steps.get(step)?.i32_result)
            .flatten()
    }
}

fn memory_pages(module: &Module<'_>, context: &InterpContext) -> Vec<usize> {
    module
        .memories
        .entries()
        .map(|(memory, _)| context.memories[memory].data.len() / waffle::WASM_PAGE)
        .collect()
}

fn failed_report(
    function_index: usize,
    i32_args: &[u32],
    fuel_limit: u64,
    outcome: FreshEvalOutcome,
) -> FreshI32CallReport {
    FreshI32CallReport {
        schema: "wasm-redox/fresh-i32-call-v1",
        function_index,
        i32_args: i32_args.to_vec(),
        fuel_limit,
        fuel_consumed: None,
        initial_memory_pages: Vec::new(),
        final_memory_pages: Vec::new(),
        outcome,
        i32_result: None,
    }
}

pub fn evaluate_fresh_i32_call(
    bytes: &[u8],
    function_index: usize,
    i32_args: &[u32],
    fuel_limit: Option<u64>,
) -> FreshI32CallReport {
    let fuel_limit = fuel_limit.unwrap_or(DEFAULT_FUEL);
    if fuel_limit == 0 {
        return failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::InvalidRequest,
        );
    }

    match catch_unwind(AssertUnwindSafe(|| {
        evaluate_inner(bytes, function_index, i32_args, fuel_limit)
    })) {
        Ok(report) => report,
        Err(_) => failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::UnsupportedOrPanicked,
        ),
    }
}

fn closed_direct_call_graph(
    module: &Module<'_>,
    function: Func,
    visiting: &mut std::collections::BTreeSet<Func>,
    proven: &mut std::collections::BTreeSet<Func>,
) -> bool {
    if proven.contains(&function) {
        return true;
    }
    if !visiting.insert(function) {
        return false;
    }
    let Some(body) = module.funcs[function].body() else {
        visiting.remove(&function);
        return false;
    };
    for (_, value) in body.values.entries() {
        let ValueDef::Operator(operator, _, _) = value else {
            continue;
        };
        match operator {
            Operator::Call { function_index } => {
                if !closed_direct_call_graph(module, *function_index, visiting, proven) {
                    visiting.remove(&function);
                    return false;
                }
            }
            Operator::CallIndirect { .. }
            | Operator::TableGet { .. }
            | Operator::TableSet { .. }
            | Operator::TableGrow { .. }
            | Operator::TableSize { .. }
            | Operator::TableFill { .. } => {
                visiting.remove(&function);
                return false;
            }
            _ => {}
        }
    }
    visiting.remove(&function);
    proven.insert(function);
    true
}

fn closed_sequence_call_graph(
    module: &Module<'_>,
    function: Func,
    visiting: &mut std::collections::BTreeSet<Func>,
    proven: &mut std::collections::BTreeSet<Func>,
) -> bool {
    if proven.contains(&function) {
        return true;
    }
    if !visiting.insert(function) {
        // Recursive interpreter calls consume the Rust stack before the fuel
        // budget becomes a useful bound. Keep the proof deliberately acyclic.
        return false;
    }
    let Some(body) = module.funcs[function].body() else {
        // Imported functions have no body. Waffle currently panics if the
        // interpreter reaches one; reject them before interpretation instead.
        visiting.remove(&function);
        return false;
    };
    for (_, value) in body.values.entries() {
        let ValueDef::Operator(operator, _, _) = value else {
            continue;
        };
        match operator {
            Operator::Call { function_index } => {
                if !closed_sequence_call_graph(module, *function_index, visiting, proven) {
                    visiting.remove(&function);
                    return false;
                }
            }
            Operator::CallIndirect { .. } => {
                // We do not prove the complete contents of funcref tables here.
                visiting.remove(&function);
                return false;
            }
            _ => {}
        }
    }
    visiting.remove(&function);
    proven.insert(function);
    true
}

pub fn evaluate_fresh_i32_sequence(
    bytes: &[u8],
    initial_table_grows: &[FreshTableGrowRequest],
    calls: &[FreshI32CallRequest],
    fuel_limit_per_call: Option<u64>,
) -> FreshI32SequenceReport {
    let fuel_limit_per_call = fuel_limit_per_call.unwrap_or(DEFAULT_FUEL);
    let failed = |outcome| FreshI32SequenceReport {
        schema: "wasm-redox/fresh-i32-sequence-v2",
        initial_table_grows: initial_table_grows.to_vec(),
        calls: calls.to_vec(),
        fuel_limit_per_call,
        outcome,
        steps: Vec::new(),
    };
    if calls.is_empty() || fuel_limit_per_call == 0 {
        return failed(FreshEvalOutcome::InvalidRequest);
    }
    match catch_unwind(AssertUnwindSafe(|| {
        evaluate_sequence_inner(bytes, initial_table_grows, calls, fuel_limit_per_call)
    })) {
        Ok(report) => report,
        Err(_) => failed(FreshEvalOutcome::UnsupportedOrPanicked),
    }
}

fn sequence_report(
    initial_table_grows: &[FreshTableGrowRequest],
    calls: &[FreshI32CallRequest],
    fuel_limit_per_call: u64,
    outcome: FreshEvalOutcome,
    steps: Vec<FreshI32SequenceStepReport>,
) -> FreshI32SequenceReport {
    FreshI32SequenceReport {
        schema: "wasm-redox/fresh-i32-sequence-v2",
        initial_table_grows: initial_table_grows.to_vec(),
        calls: calls.to_vec(),
        fuel_limit_per_call,
        outcome,
        steps,
    }
}

fn apply_initial_table_grows(
    module: &Module<'_>,
    context: &mut InterpContext,
    grows: &[FreshTableGrowRequest],
) -> bool {
    for grow in grows {
        if grow.table_index >= module.tables.len() {
            return false;
        }
        let table = Table::new(grow.table_index);
        let state = &mut context.tables[table];
        // We intentionally support only opaque-reference tables here. Growing
        // a funcref table would require concrete new function entries.
        if state.stores_functions {
            return false;
        }
        let Ok(delta) = usize::try_from(grow.delta) else {
            return false;
        };
        let Some(new_size) = state.size.checked_add(delta) else {
            return false;
        };
        if new_size > MAX_TABLE_ELEMENTS || state.max.is_some_and(|max| new_size > max) {
            return false;
        }
        state.size = new_size;
    }
    true
}

fn resolve_sequence_args(
    args: &[FreshI32Arg],
    steps: &[FreshI32SequenceStepReport],
) -> Option<Vec<u32>> {
    args.iter()
        .map(|arg| match arg {
            FreshI32Arg::Literal { value } => Some(*value),
            FreshI32Arg::StepResult { step } => steps.get(*step)?.i32_result,
        })
        .collect()
}

fn evaluate_sequence_inner(
    bytes: &[u8],
    initial_table_grows: &[FreshTableGrowRequest],
    calls: &[FreshI32CallRequest],
    fuel_limit_per_call: u64,
) -> FreshI32SequenceReport {
    let failed = |outcome, steps| {
        sequence_report(
            initial_table_grows,
            calls,
            fuel_limit_per_call,
            outcome,
            steps,
        )
    };
    let Ok(mut module) = Module::from_wasm_bytes(bytes, &FrontendOptions::default()) else {
        return failed(FreshEvalOutcome::InvalidRequest, Vec::new());
    };
    if module.expand_all_funcs().is_err()
        || module.start_func.is_some()
        || module.memories.len() > 1
        || module.memories.values().any(|memory| {
            memory.initial_pages > MAX_MEMORY_PAGES
                || memory
                    .maximum_pages
                    .is_some_and(|maximum| maximum > MAX_MEMORY_PAGES)
        })
        || module.imports.iter().any(|import| {
            matches!(
                import.kind,
                ImportKind::Memory(_) | ImportKind::Global(_) | ImportKind::Table(_)
            )
        })
    {
        return failed(FreshEvalOutcome::UnsupportedOrPanicked, Vec::new());
    }

    let Ok(mut context) = InterpContext::new(&module) else {
        return failed(FreshEvalOutcome::InvalidRequest, Vec::new());
    };
    if !apply_initial_table_grows(&module, &mut context, initial_table_grows) {
        return failed(FreshEvalOutcome::InvalidRequest, Vec::new());
    }

    let mut steps = Vec::with_capacity(calls.len());
    for call in calls {
        if call.function_index >= module.funcs.len() {
            return failed(FreshEvalOutcome::InvalidRequest, steps);
        }
        let Some(resolved_i32_args) = resolve_sequence_args(&call.i32_args, &steps) else {
            return failed(FreshEvalOutcome::InvalidRequest, steps);
        };
        let function = Func::new(call.function_index);
        if module.funcs[function].body().is_none() {
            return failed(FreshEvalOutcome::InvalidRequest, steps);
        }
        if !closed_sequence_call_graph(
            &module,
            function,
            &mut std::collections::BTreeSet::new(),
            &mut std::collections::BTreeSet::new(),
        ) {
            return failed(FreshEvalOutcome::UnsupportedOrPanicked, steps);
        }
        let signature = &module.signatures[module.funcs[function].sig()];
        let returns_i32 = signature.returns.as_slice() == [waffle::Type::I32];
        let returns_void = signature.returns.is_empty();
        if signature.params.len() != resolved_i32_args.len()
            || !signature.params.iter().all(|ty| *ty == waffle::Type::I32)
            || (!returns_i32 && !returns_void)
        {
            return failed(FreshEvalOutcome::InvalidRequest, steps);
        }

        // Each step gets its own access trace. That makes a caller-selected
        // semantic boundary (for example, immediately after a proven JS copy)
        // explicit without mutating or snapshotting linear memory.
        context.take_memory_accesses();
        let initial_memory_pages = memory_pages(&module, &context);
        context.fuel = fuel_limit_per_call;
        let arguments = resolved_i32_args
            .iter()
            .copied()
            .map(ConstVal::I32)
            .collect::<Vec<_>>();
        let result = context.call(&module, function, &arguments);
        let final_memory_pages = memory_pages(&module, &context);
        let fuel_consumed = Some(fuel_limit_per_call.saturating_sub(context.fuel));
        let memory_accesses = context
            .take_memory_accesses()
            .into_iter()
            .map(|access| FreshMemoryAccessReport {
                kind: match access.kind {
                    InterpMemoryAccessKind::Read => FreshMemoryAccessKind::Read,
                    InterpMemoryAccessKind::Write => FreshMemoryAccessKind::Write,
                },
                memory: access.memory.index(),
                addr: access.addr,
                len: access.len,
            })
            .collect::<Vec<_>>();

        let (outcome, i32_result) = match result {
            InterpResult::Ok(values) if returns_i32 => match values.as_slice() {
                [ConstVal::I32(value)] => (FreshEvalOutcome::Returned, Some(*value)),
                _ => (FreshEvalOutcome::InvalidRequest, None),
            },
            InterpResult::Ok(values) if returns_void => {
                if values.is_empty() {
                    (FreshEvalOutcome::Returned, None)
                } else {
                    (FreshEvalOutcome::InvalidRequest, None)
                }
            }
            InterpResult::Ok(_) => (FreshEvalOutcome::InvalidRequest, None),
            InterpResult::Trap(..) => (FreshEvalOutcome::Trap, None),
            InterpResult::OutOfFuel => (FreshEvalOutcome::OutOfFuel, None),
        };
        steps.push(FreshI32SequenceStepReport {
            function_index: call.function_index,
            resolved_i32_args,
            fuel_consumed,
            initial_memory_pages,
            final_memory_pages,
            outcome,
            i32_result,
            memory_accesses,
        });
        if outcome != FreshEvalOutcome::Returned {
            return failed(outcome, steps);
        }
    }

    failed(FreshEvalOutcome::Returned, steps)
}

fn evaluate_inner(
    bytes: &[u8],
    function_index: usize,
    i32_args: &[u32],
    fuel_limit: u64,
) -> FreshI32CallReport {
    let Ok(mut module) = Module::from_wasm_bytes(bytes, &FrontendOptions::default()) else {
        return failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::InvalidRequest,
        );
    };
    if function_index >= module.funcs.len() || module.expand_all_funcs().is_err() {
        return failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::InvalidRequest,
        );
    }
    if module.start_func.is_some()
        || module.memories.len() > 1
        || module.memories.values().any(|memory| {
            memory.initial_pages > MAX_MEMORY_PAGES
                || memory
                    .maximum_pages
                    .is_some_and(|maximum| maximum > MAX_MEMORY_PAGES)
        })
        || module.imports.iter().any(|import| {
            matches!(
                import.kind,
                ImportKind::Memory(_) | ImportKind::Global(_) | ImportKind::Table(_)
            )
        })
    {
        return failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::UnsupportedOrPanicked,
        );
    }

    let function = Func::new(function_index);
    if !closed_direct_call_graph(
        &module,
        function,
        &mut std::collections::BTreeSet::new(),
        &mut std::collections::BTreeSet::new(),
    ) {
        return failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::UnsupportedOrPanicked,
        );
    }
    let signature = module.funcs[function].sig();
    let signature = &module.signatures[signature];
    if signature.params.len() != i32_args.len()
        || !signature.params.iter().all(|ty| *ty == waffle::Type::I32)
        || signature.returns.as_slice() != [waffle::Type::I32]
        || module.funcs[function].body().is_none()
    {
        return failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::InvalidRequest,
        );
    }

    let Ok(mut context) = InterpContext::new(&module) else {
        return failed_report(
            function_index,
            i32_args,
            fuel_limit,
            FreshEvalOutcome::InvalidRequest,
        );
    };
    let initial_memory_pages = memory_pages(&module, &context);
    context.fuel = fuel_limit;
    let arguments = i32_args
        .iter()
        .copied()
        .map(ConstVal::I32)
        .collect::<Vec<_>>();
    let result = context.call(&module, function, &arguments);
    let final_memory_pages = memory_pages(&module, &context);
    let fuel_consumed = Some(fuel_limit.saturating_sub(context.fuel));

    let (outcome, i32_result) = match result {
        InterpResult::Ok(values) => match values.as_slice() {
            [ConstVal::I32(value)] => (FreshEvalOutcome::Returned, Some(*value)),
            _ => (FreshEvalOutcome::InvalidRequest, None),
        },
        InterpResult::Trap(..) => (FreshEvalOutcome::Trap, None),
        InterpResult::OutOfFuel => (FreshEvalOutcome::OutOfFuel, None),
    };

    FreshI32CallReport {
        schema: "wasm-redox/fresh-i32-call-v1",
        function_index,
        i32_args: i32_args.to_vec(),
        fuel_limit,
        fuel_consumed,
        initial_memory_pages,
        final_memory_pages,
        outcome,
        i32_result,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_fresh_i32_call_returns_concrete_value() -> anyhow::Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (memory 1)
                (func (param i32) (result i32)
                    local.get 0
                    i32.const 3
                    i32.add))"#,
        )?;
        let report = evaluate_fresh_i32_call(&bytes, 0, &[39], Some(100));
        assert_eq!(report.outcome, FreshEvalOutcome::Returned);
        assert_eq!(report.proven_result(), Some(42));
        assert!(report.fuel_consumed.is_some_and(|fuel| fuel > 0));
        assert_eq!(report.initial_memory_pages, vec![1]);
        assert_eq!(report.final_memory_pages, vec![1]);
        Ok(())
    }

    #[test]
    fn exact_fresh_i32_sequence_preserves_state() -> anyhow::Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (memory 1)
                (global $next (mut i32) (i32.const 64))
                (func (param i32) (result i32)
                    (local $old i32)
                    global.get $next
                    local.tee $old
                    local.get 0
                    i32.add
                    global.set $next
                    local.get $old))"#,
        )?;
        let report = evaluate_fresh_i32_sequence(
            &bytes,
            &[],
            &[
                FreshI32CallRequest {
                    function_index: 0,
                    i32_args: vec![FreshI32Arg::Literal { value: 16 }],
                },
                FreshI32CallRequest {
                    function_index: 0,
                    i32_args: vec![FreshI32Arg::Literal { value: 512 }],
                },
            ],
            Some(100),
        );
        assert_eq!(report.outcome, FreshEvalOutcome::Returned);
        assert_eq!(report.proven_result(0), Some(64));
        assert_eq!(report.proven_result(1), Some(80));
        assert_eq!(report.steps.len(), 2);
        Ok(())
    }

    #[test]
    fn exact_sequence_resolves_prior_results_and_reports_accesses() -> anyhow::Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (table 2 externref)
                (memory 1)
                (func $slot (result i32)
                    ref.null extern
                    i32.const 1
                    table.grow)
                (func $free (param i32)
                    local.get 0
                    ref.null extern
                    table.set)
                (func $write (param i32)
                    local.get 0
                    i32.const 99
                    i32.store))"#,
        )?;
        let report = evaluate_fresh_i32_sequence(
            &bytes,
            &[FreshTableGrowRequest {
                table_index: 0,
                delta: 2,
            }],
            &[
                FreshI32CallRequest {
                    function_index: 0,
                    i32_args: vec![],
                },
                FreshI32CallRequest {
                    function_index: 1,
                    i32_args: vec![FreshI32Arg::StepResult { step: 0 }],
                },
                FreshI32CallRequest {
                    function_index: 2,
                    i32_args: vec![FreshI32Arg::Literal { value: 32 }],
                },
            ],
            Some(100),
        );
        assert_eq!(report.outcome, FreshEvalOutcome::Returned);
        assert_eq!(report.proven_result(0), Some(4));
        assert_eq!(report.steps[1].resolved_i32_args, vec![4]);
        assert!(report.steps[1].memory_accesses.is_empty());
        assert_eq!(
            report.steps[2].memory_accesses,
            vec![FreshMemoryAccessReport {
                kind: FreshMemoryAccessKind::Write,
                memory: 0,
                addr: 32,
                len: 4,
            }]
        );
        Ok(())
    }

    #[test]
    fn imported_call_fails_closed() -> anyhow::Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "x" "f" (func $f (param i32) (result i32)))
                (func (param i32) (result i32)
                    local.get 0
                    call $f))"#,
        )?;
        let report = evaluate_fresh_i32_call(&bytes, 1, &[1], Some(100));
        assert_eq!(report.outcome, FreshEvalOutcome::UnsupportedOrPanicked);
        assert_eq!(report.proven_result(), None);

        let sequence = evaluate_fresh_i32_sequence(
            &bytes,
            &[],
            &[FreshI32CallRequest {
                function_index: 1,
                i32_args: vec![FreshI32Arg::Literal { value: 1 }],
            }],
            Some(100),
        );
        assert_eq!(sequence.outcome, FreshEvalOutcome::UnsupportedOrPanicked);
        assert!(sequence.steps.is_empty());
        Ok(())
    }

    #[test]
    fn start_section_and_table_state_fail_closed() -> anyhow::Result<()> {
        let with_start = wat::parse_str(
            r#"(module
                (func $start)
                (start $start)
                (func (param i32) (result i32)
                    local.get 0))"#,
        )?;
        let report = evaluate_fresh_i32_call(&with_start, 1, &[7], Some(100));
        assert_eq!(report.outcome, FreshEvalOutcome::UnsupportedOrPanicked);
        assert_eq!(report.proven_result(), None);

        let table_dependent = wat::parse_str(
            r#"(module
                (table 1 funcref)
                (func (param i32) (result i32)
                    i32.const 0
                    table.get
                    drop
                    local.get 0))"#,
        )?;
        let report = evaluate_fresh_i32_call(&table_dependent, 0, &[7], Some(100));
        assert_eq!(report.outcome, FreshEvalOutcome::UnsupportedOrPanicked);
        assert_eq!(report.proven_result(), None);

        let imported_memory = wat::parse_str(
            r#"(module
                (import "host" "memory" (memory 1))
                (func (param i32) (result i32)
                    local.get 0))"#,
        )?;
        let report = evaluate_fresh_i32_call(&imported_memory, 0, &[7], Some(100));
        assert_eq!(report.outcome, FreshEvalOutcome::UnsupportedOrPanicked);
        assert_eq!(report.proven_result(), None);

        let oversized_memory = wat::parse_str(
            r#"(module
                (memory 1 4096)
                (func (param i32) (result i32)
                    local.get 0))"#,
        )?;
        let report = evaluate_fresh_i32_call(&oversized_memory, 0, &[7], Some(100));
        assert_eq!(report.outcome, FreshEvalOutcome::UnsupportedOrPanicked);
        assert_eq!(report.proven_result(), None);

        let recursive = wat::parse_str(
            r#"(module
                (func $recur (param i32) (result i32)
                    local.get 0
                    call $recur))"#,
        )?;
        let report = evaluate_fresh_i32_call(&recursive, 0, &[7], Some(100));
        assert_eq!(report.outcome, FreshEvalOutcome::UnsupportedOrPanicked);
        assert_eq!(report.proven_result(), None);
        Ok(())
    }

    #[test]
    fn fuel_exhaustion_fails_closed() -> anyhow::Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (param i32) (result i32)
                    (loop $again
                        br $again)
                    local.get 0))"#,
        )?;
        let report = evaluate_fresh_i32_call(&bytes, 0, &[1], Some(8));
        assert_eq!(report.outcome, FreshEvalOutcome::OutOfFuel);
        assert_eq!(report.proven_result(), None);
        Ok(())
    }
}
