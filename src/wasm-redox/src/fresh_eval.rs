use serde::Serialize;
use std::panic::{catch_unwind, AssertUnwindSafe};
use waffle::{
    entity::EntityRef, ConstVal, FrontendOptions, Func, ImportKind, InterpContext, InterpResult,
    Module, Operator, ValueDef,
};

const DEFAULT_FUEL: u64 = 1_000_000;
const MAX_MEMORY_PAGES: usize = 2048;

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
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
