#[cfg(test)]
use anyhow::{Context, Result};
#[cfg(test)]
use std::collections::BTreeSet;

mod analysis;
mod copied_input;
mod helper_recognition;
mod host_effect;
mod ir;
mod nesting;
mod reporting;
mod scalar;
mod semantic_render;
mod transition;
mod value_flow;

pub use analysis::{analyze_export_semantics, ExportSemanticAnalysis};
pub use copied_input::{ExternrefBulkCopyCandidateReport, StructuralInputCopyLoadReport};
#[cfg(test)]
use helper_recognition::normalize_import_name;
pub use host_effect::OpaqueHostEffectMemoryReadReport;
pub use reporting::{
    compose_machine_pipelines, root_machine_indices, NestedMachineEntryReport,
    SemanticBindingReport, StateCaseReport, StateMachinePipelineReport,
    StateMachinePipelineStageReport, StateMachineReport, StateTransitionReport,
};
#[cfg(test)]
use scalar::{fold_closed_i32_expression, render_scalar_family, try_eval_i32_expression};
pub use semantic_render::{SemanticReturnReport, SemanticRuntimeBindingReport};

#[cfg(test)]
mod tests {
    use super::copied_input::FreshCleanupSlotRole;
    use super::*;

    fn return_expressions(analysis: &ExportSemanticAnalysis) -> Vec<&str> {
        analysis
            .returns
            .iter()
            .map(|report| report.expression.as_str())
            .collect()
    }

    #[test]
    fn reports_structural_externref_bulk_copy_candidate() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory 1)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    i32.const 0
                    local.get $source
                    table.set

                    i32.const 1
                    i32.const 0
                    table.get
                    call $ctor
                    table.set

                    i32.const 1
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set

                    local.get $base
                    i32.load
                    local.get $base
                    i32.load offset=4
                    i32.add))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        assert_eq!(analysis.externref_bulk_copy_candidates.len(), 1);
        let candidate = &analysis.externref_bulk_copy_candidates[0];
        assert_eq!(candidate.set_import_function, 1);
        assert_eq!(candidate.constructor_import_function, 0);
        assert_eq!(candidate.source_entry_parameter, 0);
        assert_eq!(candidate.destination_element_index_shift, 2);
        assert_eq!(candidate.destination_base_guaranteed_trailing_zero_bits, 0);
        assert_eq!(
            candidate
                .destination_loads
                .iter()
                .map(|load| load.byte_offset)
                .collect::<Vec<_>>(),
            vec![0, 4]
        );
        assert!(candidate
            .destination_loads
            .iter()
            .all(|load| load.copied_bytes_unmodified_since_set));
        Ok(())
    }

    #[test]
    fn copied_input_destination_alignment_proves_masked_base() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory 1)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    (local $aligned i32)
                    local.get $base i32.const -4 i32.and local.set $aligned
                    i32.const 0 local.get $source table.set
                    i32.const 1 i32.const 0 table.get call $ctor table.set
                    i32.const 1 table.get
                    i32.const 0 table.get
                    local.get $aligned i32.const 2 i32.shr_u
                    call $set
                    local.get $aligned i32.load))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        assert!(candidate.destination_base_guaranteed_trailing_zero_bits >= 2);
        Ok(())
    }

    #[test]
    fn copied_input_destination_alignment_fails_closed_on_degrading_loop() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory 1)
                (func (export "copy")
                    (param $source externref) (param $base i32) (param $count i32) (result i32)
                    (local $aligned i32)
                    local.get $base i32.const -4 i32.and local.set $aligned
                    block $exit
                        loop $again
                            local.get $count i32.eqz br_if $exit
                            local.get $aligned i32.const 1 i32.shr_u local.set $aligned
                            local.get $count i32.const 1 i32.sub local.set $count
                            br $again
                        end
                    end
                    i32.const 0 local.get $source table.set
                    i32.const 1 i32.const 0 table.get call $ctor table.set
                    i32.const 1 table.get
                    i32.const 0 table.get
                    local.get $aligned i32.const 2 i32.shr_u
                    call $set
                    local.get $aligned i32.load))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        assert_eq!(candidate.destination_base_guaranteed_trailing_zero_bits, 0);
        Ok(())
    }

    fn copied_input_recipe_fixture(alternate: u32, length_slot: u32) -> Result<Vec<u8>> {
        wat::parse_str(format!(
            r#"(module
                (import "wbg" "__wbg_length_0123456789abcdef"
                    (func $length (param externref) (result i32)))
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 8 externref)
                (memory 1)
                (func $length_helper (param $slot i32) (result i32)
                    local.get $slot
                    table.get
                    call $length)
                (func $alloc (param $bytes i32) (result i32)
                    local.get $bytes
                    i32.const 1024
                    i32.add)
                (func (export "copy") (param $source externref) (param $use_alt i32) (result i32)
                    (local $base i32)
                    i32.const 0
                    local.get $source
                    table.set
                    i32.const 1
                    i32.const 2
                    table.get
                    call $ctor
                    table.set
                    local.get $use_alt
                    if (result i32)
                        i32.const {alternate}
                    else
                        i32.const {length_slot}
                        call $length_helper
                        i32.const 2
                        i32.shl
                        call $alloc
                    end
                    local.set $base
                    i32.const 1
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set
                    local.get $base
                    i32.load))"#,
        ))
        .context("parse copied-input recipe fixture")
    }

    fn copied_input_fresh_alignment_boundary_fixture() -> Result<Vec<u8>> {
        wat::parse_str(
            r#"(module
                (import "wbg" "length" (func $length (param externref) (result i32)))
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (import "wbg" "__wbindgen_init_externref_table" (func $start))
                (table (export "__wbindgen_export_0") 8 externref)
                (memory (export "memory") 1)
                (data (i32.const 0) "\08\00\00\00")

                (func $memory_slot (result i32)
                    (local $slot i32)
                    i32.const 2
                    local.tee $slot
                    call $memory
                    table.set
                    local.get $slot)
                (func $buffer_slot (param $slot i32) (result i32)
                    local.get $slot)
                (func $length_helper (param $slot i32) (result i32)
                    local.get $slot
                    table.get
                    call $length)
                (func $alloc (param $bytes i32) (result i32)
                    i32.const 0
                    i32.load
                    local.get $bytes
                    i32.add)
                (export "__wbindgen_start" (func $start))
                (func (export "copy") (param $source externref) (param $use_alt i32) (result i32)
                    (local $base i32)
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    i32.const 0
                    local.get $source
                    table.set
                    i32.const 1
                    call $memory_slot
                    call $buffer_slot
                    table.get
                    call $ctor
                    table.set
                    local.get $use_alt
                    if (result i32)
                        i32.const 4
                    else
                        i32.const 0
                        call $length_helper
                        i32.const 2
                        i32.shl
                        call $alloc
                    end
                    local.set $base
                    i32.const 1
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set
                    local.get $base
                    i32.load
                    local.get $base
                    i32.load offset=4
                    i32.add))"#,
        )
        .context("parse copied-input fresh-alignment boundary fixture")
    }

    #[test]
    fn copied_input_fresh_alignment_boundary_requires_exact_evaluation() -> Result<()> {
        let bytes = copied_input_fresh_alignment_boundary_fixture()?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        assert_eq!(candidate.destination_base_guaranteed_trailing_zero_bits, 0);
        let Some(recipe) = &candidate.fresh_destination_base_recipe else {
            return Err(anyhow::anyhow!("expected fresh destination-base recipe"));
        };
        assert_eq!(recipe.source_length_byte_shift, 2);
        assert_eq!(recipe.alternate_constant_bases, vec![4]);
        assert_eq!(recipe.source_length_import_function, 0);
        assert_eq!(recipe.function, 8);
        Ok(())
    }

    #[test]
    fn copied_input_reports_fresh_destination_recipe() -> Result<()> {
        let bytes = copied_input_recipe_fixture(4, 0)?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        let Some(recipe) = &candidate.fresh_destination_base_recipe else {
            return Err(anyhow::anyhow!("expected fresh destination-base recipe"));
        };
        assert_eq!(recipe.source_length_byte_shift, 2);
        assert_eq!(recipe.alternate_constant_bases, vec![4]);
        assert_eq!(recipe.source_length_import_function, 0);
        Ok(())
    }

    #[test]
    fn copied_input_recipe_rejects_unaligned_alternate_or_wrong_source_slot() -> Result<()> {
        for bytes in [
            copied_input_recipe_fixture(2, 0)?,
            copied_input_recipe_fixture(4, 3)?,
        ] {
            let analysis = analyze_export_semantics(&bytes, "copy")?;
            let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
                return Err(anyhow::anyhow!("expected one copied-input candidate"));
            };
            assert!(candidate.fresh_destination_base_recipe.is_none());
        }
        Ok(())
    }

    #[test]
    fn copied_input_load_integrity_rejects_intervening_same_memory_write() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory 1)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    i32.const 0 local.get $source table.set
                    i32.const 1 i32.const 0 table.get call $ctor table.set
                    i32.const 1 table.get
                    i32.const 0 table.get
                    local.get $base i32.const 2 i32.shr_u
                    call $set
                    local.get $base i32.const 99 i32.store
                    local.get $base i32.load))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        let [load] = candidate.destination_loads.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input load"));
        };
        assert!(!load.copied_bytes_unmodified_since_set);
        Ok(())
    }

    #[test]
    fn copied_input_load_integrity_resets_at_repeated_copy_site() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory 1)
                (func (export "copy")
                    (param $source externref) (param $base i32) (param $repeat i32) (result i32)
                    (local $result i32)
                    (loop $again
                        i32.const 0 local.get $source table.set
                        i32.const 1 i32.const 0 table.get call $ctor table.set
                        i32.const 1 table.get
                        i32.const 0 table.get
                        local.get $base i32.const 2 i32.shr_u
                        call $set
                        local.get $repeat
                        if
                            local.get $base i32.const 99 i32.store
                            i32.const 0 local.set $repeat
                            br $again
                        end
                        local.get $base i32.load
                        local.set $result)
                    local.get $result))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        let [load] = candidate.destination_loads.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input load"));
        };
        assert!(!load.unresolved_intervening_memory_mutation);
        assert!(load.copied_bytes_unmodified_since_set);
        Ok(())
    }

    #[test]
    fn copied_input_load_integrity_rejects_path_dependent_memory_write() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory 1)
                (func (export "copy")
                    (param $source externref) (param $base i32) (param $condition i32) (result i32)
                    i32.const 0 local.get $source table.set
                    i32.const 1 i32.const 0 table.get call $ctor table.set
                    i32.const 1 table.get
                    i32.const 0 table.get
                    local.get $base i32.const 2 i32.shr_u
                    call $set
                    local.get $condition
                    if
                        local.get $base i32.const 99 i32.store
                    end
                    local.get $base i32.load))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        let [load] = candidate.destination_loads.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input load"));
        };
        assert!(!load.copied_bytes_unmodified_since_set);
        Ok(())
    }

    #[test]
    fn copied_input_load_integrity_ignores_alternate_memory_writes() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory $copied 1)
                (memory $other 1)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    i32.const 0 local.get $source table.set
                    i32.const 1 i32.const 0 table.get call $ctor table.set
                    i32.const 1 table.get
                    i32.const 0 table.get
                    local.get $base i32.const 2 i32.shr_u
                    call $set
                    local.get $base i32.const 99 i32.store $other
                    local.get $base i32.load $copied))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        let [load] = candidate.destination_loads.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input load"));
        };
        assert!(load.copied_bytes_unmodified_since_set);
        Ok(())
    }

    #[test]
    fn copied_input_load_integrity_treats_calls_as_memory_barriers() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (import "wbg" "opaque" (func $opaque))
                (table 4 externref)
                (memory 1)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    i32.const 0 local.get $source table.set
                    i32.const 1 i32.const 0 table.get call $ctor table.set
                    i32.const 1 table.get
                    i32.const 0 table.get
                    local.get $base i32.const 2 i32.shr_u
                    call $set
                    call $opaque
                    local.get $base i32.load))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        let [load] = candidate.destination_loads.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input load"));
        };
        assert!(!load.copied_bytes_unmodified_since_set);
        Ok(())
    }

    #[test]
    fn reports_memory_import_for_structural_bulk_copy_candidate() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory (export "memory") 1)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    i32.const 2
                    local.tee $slot
                    call $memory
                    table.set
                    local.get $slot)
                (func $buffer_slot (param $slot i32) (result i32)
                    local.get $slot)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    i32.const 0
                    local.get $source
                    table.set

                    i32.const 1
                    call $memory_slot
                    call $buffer_slot
                    table.get
                    call $ctor
                    table.set

                    i32.const 1
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set

                    local.get $base
                    i32.load
                    local.get $base
                    i32.load offset=4
                    i32.add))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        assert_eq!(analysis.externref_bulk_copy_candidates.len(), 1);
        let candidate = &analysis.externref_bulk_copy_candidates[0];
        assert_eq!(candidate.constructor_import_function, 1);
        assert_eq!(candidate.set_import_function, 2);
        assert_eq!(candidate.constructor_input_memory_import_function, Some(0));
        assert_eq!(candidate.constructor_input_slot_provider_function, Some(4));
        assert_eq!(
            candidate.constructor_input_provider_argument_function,
            Some(3)
        );
        assert_eq!(
            candidate
                .destination_loads
                .iter()
                .map(|load| load.memory)
                .collect::<Vec<_>>(),
            vec![0, 0]
        );
        Ok(())
    }

    #[test]
    fn reports_fresh_cleanup_disjointness_recipe() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_buffer_fixture" (func $buffer (param externref) (result externref)))
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 16 externref)
                (memory 1)
                (global $next_slot (mut i32) (i32.const 4))
                (func $slot_alloc (result i32)
                    (local $slot i32)
                    global.get $next_slot
                    local.tee $slot
                    i32.const 1
                    i32.add
                    global.set $next_slot
                    local.get $slot)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $slot_alloc
                    local.tee $slot
                    call $memory
                    table.set
                    local.get $slot)
                (func $buffer_slot (param $memory_slot i32) (result i32)
                    (local $value externref)
                    (local $slot i32)
                    local.get $memory_slot
                    table.get
                    call $buffer
                    local.set $value
                    call $slot_alloc
                    local.tee $slot
                    local.get $value
                    table.set
                    local.get $slot)
                (func $cleanup (param $slot i32)
                    local.get $slot
                    i32.const 2
                    i32.shl
                    i32.const 4096
                    i32.add
                    i32.const 0
                    i32.store)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    (local $memory_slot i32)
                    (local $buffer_slot i32)
                    (local $receiver_slot i32)
                    (local $receiver externref)
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    i32.const 0
                    local.get $source
                    table.set
                    call $memory_slot
                    local.tee $memory_slot
                    call $buffer_slot
                    local.tee $buffer_slot
                    table.get
                    call $ctor
                    local.set $receiver
                    call $slot_alloc
                    local.tee $receiver_slot
                    local.get $receiver
                    table.set
                    local.get $buffer_slot
                    call $cleanup
                    local.get $receiver_slot
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set
                    local.get $receiver_slot
                    call $cleanup
                    local.get $memory_slot
                    call $cleanup
                    local.get $base
                    i32.load))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        let [candidate] = analysis.externref_bulk_copy_candidates.as_slice() else {
            return Err(anyhow::anyhow!("expected one copied-input candidate"));
        };
        let Some(recipe) = &candidate.fresh_cleanup_disjointness_recipe else {
            return Err(anyhow::anyhow!(
                "expected fresh cleanup disjointness recipe"
            ));
        };
        assert_eq!(recipe.slot_allocator_function, 4);
        assert_eq!(recipe.cleanup_function, 7);
        assert_eq!(recipe.bypassed_setup_import_functions, vec![0, 1]);
        assert_eq!(recipe.pre_copy_cleanup, FreshCleanupSlotRole::Buffer);
        assert_eq!(
            recipe.post_copy_cleanups,
            vec![FreshCleanupSlotRole::Receiver, FreshCleanupSlotRole::Memory]
        );
        assert_eq!(
            candidate.destination_loads[0].internal_memory_mutation_call_barriers,
            vec![7]
        );
        Ok(())
    }

    #[test]
    fn rejects_bulk_copy_candidate_with_path_dependent_source_overwrite() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (func (export "copy")
                    (param $source externref)
                    (param $other externref)
                    (param $condition i32)
                    (param $base i32)
                    i32.const 0
                    local.get $source
                    table.set

                    local.get $condition
                    if
                        i32.const 0
                        local.get $other
                        table.set
                    end

                    i32.const 1
                    i32.const 0
                    table.get
                    call $ctor
                    table.set

                    i32.const 1
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "copy")?;
        assert!(analysis.externref_bulk_copy_candidates.is_empty());
        Ok(())
    }

    #[test]
    fn recovers_xor_encoded_state_chain() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (result i32)
                    (local $state i32)
                    i32.const 10
                    local.set $state
                    loop $dispatch
                        local.get $state i32.const 10 i32.eq
                        if
                            local.get $state i32.const 30 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 20 i32.eq
                        if
                            local.get $state i32.const 10 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 30 i32.eq
                        if
                            local.get $state i32.const 54 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 40 i32.eq
                        if
                            local.get $state i32.const 26 i32.xor local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 50 i32.eq
                        if i32.const 7 return end
                        unreachable
                    end
                    unreachable))"#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        let machines = &analysis.state_machines;
        assert_eq!(machines.len(), 1);
        let machine = &machines[0];
        assert_eq!(machine.initial, BTreeSet::from([10]));
        assert_eq!(machine.graph.len(), 5);
        assert_eq!(machine.unresolved_backedges, 0);
        assert_eq!(machine.graph[&10], BTreeSet::from([20]));
        assert_eq!(machine.graph[&20], BTreeSet::from([30]));
        assert_eq!(machine.graph[&30], BTreeSet::from([40]));
        assert_eq!(machine.graph[&40], BTreeSet::from([50]));
        assert!(machine.graph[&50].is_empty());
        assert_eq!(machine.linearized, Some(vec![10, 20, 30, 40, 50]));
        assert_eq!(machine.cases.len(), 5);
        assert_eq!(machine.cases[0].state, 10);
        assert_eq!(machine.cases[0].successors, BTreeSet::from([20]));
        assert_eq!(machine.cases[0].transitions.len(), 1);
        assert_eq!(machine.cases[0].transitions[0].successor, 20);
        assert!(!machine.cases[0].transitions[0]
            .composed_arguments
            .is_empty());
        assert!(machine.cases[0].nested_machines.is_empty());
        assert!(machine.cases[0].direct_nested_machines.is_empty());
        assert_eq!(root_machine_indices(machines), vec![0]);
        Ok(())
    }

    #[test]
    fn folds_closed_i32_expression_language() {
        assert_eq!(
            try_eval_i32_expression(
                "wrapping_add(reverse_bits32(0x00000001), rotl(0x00000001, 0x00000008))"
            ),
            Some(0x8000_0100)
        );
        assert_eq!(
            fold_closed_i32_expression("((0x000000f0 >> 0x00000004) | 0x00000010)".to_owned()),
            "0x0000001f"
        );
        assert_eq!(try_eval_i32_expression("$p1"), None);
        assert_eq!(
            render_scalar_family("i32mul", &["$x".into(), "0x00000000".into()]),
            Some("0x00000000".into())
        );
        assert_eq!(
            render_scalar_family("i32or", &["$x".into(), "0x00000000".into()]),
            Some("$x".into())
        );
        assert_eq!(
            render_scalar_family("i32add", &["0x00000002".into(), "0x00000003".into()]),
            Some("0x00000005".into())
        );
    }

    #[test]
    fn folds_carried_value_across_linear_state_chain() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (result i32)
                    (local $state i32)
                    (local $value i32)
                    i32.const 10
                    local.set $state
                    i32.const 1
                    local.set $value
                    loop $dispatch
                        local.get $state i32.const 10 i32.eq
                        if
                            local.get $value i32.const 3 i32.add local.set $value
                            i32.const 20 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 20 i32.eq
                        if
                            local.get $value i32.const 1 i32.rotl local.set $value
                            i32.const 30 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 30 i32.eq
                        if
                            local.get $value i32.const 5 i32.xor local.set $value
                            i32.const 40 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 40 i32.eq
                        if
                            local.get $value i32.const 7 i32.mul local.set $value
                            i32.const 50 local.set $state
                            br $dispatch
                        end
                        local.get $state i32.const 50 i32.eq
                        if local.get $value return end
                        unreachable
                    end
                    unreachable))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.state_machines.len(), 1);
        assert_eq!(analysis.state_machine_pipelines.len(), 1);
        assert!(analysis
            .terminal_bindings
            .iter()
            .filter(|binding| !binding.state_parameter)
            .any(|binding| binding.expression == "0x0000005b"));
        Ok(())
    }

    #[test]
    fn renders_canonical_i32_bit_reverse() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "reverse") (param $input i32) (result i32)
                    (local $value i32)
                    local.get $input
                    i32.const 1
                    i32.shr_u
                    i32.const 0x55555555
                    i32.and
                    local.get $input
                    i32.const 0x55555555
                    i32.and
                    i32.const 1
                    i32.shl
                    i32.or
                    local.set $value

                    local.get $value
                    i32.const 2
                    i32.shr_u
                    i32.const 0x33333333
                    i32.and
                    local.get $value
                    i32.const 0x33333333
                    i32.and
                    i32.const 2
                    i32.shl
                    i32.or
                    local.set $value

                    local.get $value
                    i32.const 4
                    i32.shr_u
                    i32.const 0x0f0f0f0f
                    i32.and
                    local.get $value
                    i32.const 0x0f0f0f0f
                    i32.and
                    i32.const 4
                    i32.shl
                    i32.or
                    local.set $value

                    local.get $value
                    i32.const 24
                    i32.shr_u
                    local.get $value
                    i32.const 8
                    i32.shr_u
                    i32.const 0x0000ff00
                    i32.and
                    i32.or
                    local.get $value
                    i32.const 8
                    i32.shl
                    i32.const 0x00ff0000
                    i32.and
                    i32.or
                    local.get $value
                    i32.const 24
                    i32.shl
                    i32.or))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "reverse")?;
        assert_eq!(return_expressions(&analysis), ["reverse_bits32($arg0)"]);
        assert!(analysis.state_machines.is_empty());
        Ok(())
    }

    #[test]
    fn recovers_nested_linear_state_machines() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (result i32)
                    (local $outer i32)
                    (local $inner i32)
                    i32.const 10
                    local.set $outer
                    block $after_outer
                        loop $outer_dispatch
                            local.get $outer i32.const 10 i32.eq
                            if i32.const 20 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 20 i32.eq
                            if i32.const 30 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 30 i32.eq
                            if i32.const 40 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 40 i32.eq
                            if i32.const 50 local.set $outer br $outer_dispatch end
                            local.get $outer i32.const 50 i32.eq
                            if br $after_outer end
                            unreachable
                        end
                    end
                    i32.const 100
                    local.set $inner
                    loop $inner_dispatch
                        local.get $inner i32.const 100 i32.eq
                        if i32.const 110 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 110 i32.eq
                        if i32.const 120 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 120 i32.eq
                        if i32.const 130 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 130 i32.eq
                        if i32.const 140 local.set $inner br $inner_dispatch end
                        local.get $inner i32.const 140 i32.eq
                        if i32.const 7 return end
                        unreachable
                    end
                    unreachable))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        let machines = &analysis.state_machines;
        assert_eq!(machines.len(), 2);
        let roots = &analysis.state_machine_roots;
        assert_eq!(roots.len(), 1);
        let root = roots[0];
        let children = machines[root]
            .cases
            .iter()
            .flat_map(|case| case.direct_nested_machines.iter().copied())
            .collect::<BTreeSet<_>>();
        assert_eq!(children.len(), 1);
        let child = *children.iter().next().context("nested child")?;
        assert!(machines[child]
            .cases
            .iter()
            .all(|case| case.direct_nested_machines.is_empty()));
        assert!(machines[root].graph.len() >= 5);
        assert!(machines[child].graph.len() >= 5);
        let pipelines = compose_machine_pipelines(machines);
        assert_eq!(pipelines.len(), 1);
        assert_eq!(pipelines[0].stages.len(), 2);
        assert_eq!(pipelines[0].stages[0].next_machine, Some(child));
        Ok(())
    }

    #[test]
    fn names_proven_wasm_bindgen_length_wrapper() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbg_length_6ca527665d89694d"
                    (func $length (param externref) (result i32)))
                (table 1 externref)
                (func $length_slot (param $slot i32) (result i32)
                    local.get $slot
                    table.get 0
                    call $length)
                (func (export "run") (result i32)
                    i32.const 0
                    call $length_slot))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(return_expressions(&analysis), ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(analysis.runtime_bindings[0].name, "$runtime0");
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.externref_length(0x00000000)"
        );
        assert_eq!(
            normalize_import_name("wbg", "__wbg_length_6ca527665d89694d"),
            "wbg.length"
        );
        Ok(())
    }

    #[test]
    fn does_not_name_transformed_length_helper_as_plain_length() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbg_length_6ca527665d89694d"
                    (func $length (param externref) (result i32)))
                (table 1 externref)
                (func $length_plus_one (param $slot i32) (result i32)
                    local.get $slot
                    table.get 0
                    call $length
                    i32.const 1
                    i32.add)
                (func (export "run") (result i32)
                    i32.const 0
                    call $length_plus_one))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(return_expressions(&analysis).len(), 1);
        assert!(analysis
            .runtime_bindings
            .iter()
            .all(|binding| !binding.expression.contains("wbindgen.externref_length")));
        Ok(())
    }

    #[test]
    fn names_proven_wasm_bindgen_memory_slot_wrapper() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 2 externref)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)
                (func (export "run") (result externref)
                    call $memory_slot
                    table.get 0))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(
            return_expressions(&analysis),
            ["table_get<table0>($runtime0)"]
        );
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.memory_slot()"
        );
        Ok(())
    }

    #[test]
    fn names_proven_wasm_bindgen_get_u32_bridge() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbg_getUint32_9c3cc8fde7919ed4"
                    (func $get (param externref i32) (result i32)))
                (func $bridge (param $offset i32) (result i32)
                    ref.null extern
                    local.get $offset
                    call $get)
                (func (export "run") (result i32)
                    i32.const 7
                    call $bridge))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(return_expressions(&analysis), ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.getUint32_bridge(0x00000007)"
        );
        Ok(())
    }

    #[test]
    fn runtime_dag_reuses_one_ssa_call_value() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "host" "read" (func $read (param i32) (result i32)))
                (func (export "run") (result i32)
                    (local $value i32)
                    i32.const 3
                    call $read
                    local.set $value
                    local.get $value
                    local.get $value
                    i32.add))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "host.read(0x00000003)"
        );
        assert_eq!(
            return_expressions(&analysis),
            ["wrapping_add($runtime0, $runtime0)"]
        );
        assert!(analysis.runtime_bindings[0].runtime_dependencies.is_empty());
        assert_eq!(
            analysis.returns[0].runtime_dependencies,
            [analysis.runtime_bindings[0].value]
        );
        Ok(())
    }

    #[test]
    fn runtime_dag_records_direct_nested_runtime_dependencies() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "host" "read" (func $read (param i32) (result i32)))
                (import "host" "transform" (func $transform (param i32) (result i32)))
                (func (export "run") (result i32)
                    i32.const 3
                    call $read
                    call $transform))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.runtime_bindings.len(), 2);
        let inner = &analysis.runtime_bindings[0];
        let outer = &analysis.runtime_bindings[1];
        assert_eq!(inner.expression, "host.read(0x00000003)");
        assert!(inner.runtime_dependencies.is_empty());
        assert_eq!(outer.expression, "host.transform($runtime0)");
        assert_eq!(outer.runtime_dependencies, [inner.value]);
        assert_eq!(return_expressions(&analysis), ["$runtime1"]);
        assert_eq!(analysis.returns[0].runtime_dependencies, [outer.value]);
        Ok(())
    }

    #[test]
    fn follows_surviving_block_params_after_redundant_param_removal() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (param $cond i32) (result i32)
                    (local $a i32)
                    (local $b i32)
                    (local $c i32)
                    (local $d i32)
                    i32.const 10
                    local.set $a
                    i32.const 20
                    local.set $b
                    i32.const 30
                    local.set $c
                    i32.const 40
                    local.set $d

                    local.get $cond
                    if
                        i32.const 21
                        local.set $b
                        i32.const 41
                        local.set $d
                    end

                    local.get $a
                    local.get $b
                    i32.add
                    local.get $c
                    i32.add
                    local.get $d
                    i32.add))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        let expression = analysis
            .returns
            .first()
            .map(|report| report.expression.as_str())
            .context("return expression")?;
        assert!(expression.contains("phi(0x00000014, 0x00000015)"));
        assert!(expression.contains("phi(0x00000028, 0x00000029)"));
        Ok(())
    }

    #[test]
    fn names_structurally_proven_heap_allocator() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (memory 1)
                (func $alloc (param $bytes i32) (result i32)
                    (local $ptr i32)
                    local.get $bytes
                    i32.const 65535
                    i32.add
                    i32.const 16
                    i32.shr_u
                    memory.grow
                    local.tee $ptr
                    i32.const -1
                    i32.eq
                    if
                        i32.const 0
                        return
                    end
                    local.get $ptr
                    i32.const 16
                    i32.shl
                    local.set $ptr

                    local.get $ptr
                    i32.load
                    drop
                    local.get $ptr
                    i32.load offset=4
                    drop
                    local.get $ptr
                    i32.load offset=8
                    drop
                    local.get $ptr
                    i32.load offset=12
                    drop

                    local.get $ptr
                    i32.const 1
                    i32.store
                    local.get $ptr
                    i32.const 2
                    i32.store offset=4
                    local.get $ptr
                    i32.const 3
                    i32.store offset=8
                    local.get $ptr
                    i32.const 4
                    i32.store offset=12
                    local.get $ptr
                    i32.const 5
                    i32.store offset=16
                    local.get $ptr
                    i32.const 6
                    i32.store offset=20
                    local.get $ptr
                    i32.const 7
                    i32.store offset=24
                    local.get $ptr
                    i32.const 8
                    i32.store offset=28

                    local.get $ptr
                    i32.const 8
                    i32.add)
                (func (export "run") (param $bytes i32) (result i32)
                    local.get $bytes
                    call $alloc))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(return_expressions(&analysis), ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wasm.heap_alloc($arg0)"
        );
        Ok(())
    }

    #[test]
    fn does_not_name_plain_memory_grow_as_heap_allocator() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (memory 1)
                (func $grow (param $pages i32) (result i32)
                    local.get $pages
                    memory.grow)
                (func (export "run") (param $pages i32) (result i32)
                    local.get $pages
                    call $grow))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(return_expressions(&analysis), ["$runtime0"]);
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert!(!analysis.runtime_bindings[0]
            .expression
            .contains("wasm.heap_alloc"));
        Ok(())
    }

    #[test]
    fn renders_direct_conditional_phi_with_its_guard() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (func (export "run") (param $cond i32) (result i32)
                    (local $value i32)
                    i32.const 10
                    local.set $value
                    local.get $cond
                    if
                        i32.const 20
                        local.set $value
                    else
                        i32.const 30
                        local.set $value
                    end
                    local.get $value))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        let expression = analysis
            .returns
            .first()
            .map(|report| report.expression.as_str())
            .context("return expression")?;
        assert_eq!(expression, "phi_if($arg0, 0x00000014, 0x0000001e)");
        Ok(())
    }
    #[test]
    fn names_captured_memory_grow_only_with_proven_memory_receiver() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_grow_43d369088a370694"
                    (func $grow (param externref i32) (result i32)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 2 externref)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)
                (func (export "run") (result i32)
                    call $memory_slot
                    table.get 0
                    i32.const 1
                    call $grow))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.runtime_bindings.len(), 2);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.memory_slot()"
        );
        assert_eq!(
            analysis.runtime_bindings[1].expression,
            "wasm.memory_grow(0x00000001, externref_slot=$runtime0)"
        );
        Ok(())
    }
    fn host_effect_memory_fixture(host_effect_body: &str, run_body: &str) -> Result<Vec<u8>> {
        wat::parse_str(format!(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_grow_43d369088a370694"
                    (func $grow (param externref i32) (result i32)))
                (import "wbg" "__wbg_buffer_609cc3eee51ed158"
                    (func $buffer (param externref) (result externref)))
                (import "wbg" "__wbg_byteLength_ea52ac3de882b483"
                    (func $byte_length (param externref) (result i32)))
                (import "wbg" "__wbg_new_7e079fa25e135eb1"
                    (func $view_new (param externref i32 i32) (result externref)))
                (import "wbg" "__wbg_getUint32_9c3cc8fde7919ed4"
                    (func $get_u32 (param externref i32) (result i32)))
                (import "host" "opaque_signal"
                    (func $opaque_signal (param externref i32 i32)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 16 externref)

                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)

                (func $buffer_slot (param $memory_slot i32) (result i32)
                    (local $buffer externref)
                    (local $slot i32)
                    local.get $memory_slot
                    table.get 0
                    call $buffer
                    local.set $buffer
                    call $alloc
                    local.tee $slot
                    local.get $buffer
                    table.set 0
                    local.get $slot)

                (func $memory_get (param $offset i32) (result i32)
                    (local $buffer_slot i32)
                    (local $length i32)
                    (local $view externref)
                    (local $view_slot i32)
                    call $memory_slot
                    call $buffer_slot
                    local.tee $buffer_slot
                    table.get 0
                    call $byte_length
                    local.set $length
                    local.get $buffer_slot
                    table.get 0
                    i32.const 0
                    local.get $length
                    call $view_new
                    local.set $view
                    call $alloc
                    local.tee $view_slot
                    local.get $view
                    table.set 0
                    local.get $view_slot
                    table.get 0
                    local.get $offset
                    call $get_u32)

                (func $host_effect (param $slot i32) (param $base i32) (param $offset i32)
                    {host_effect_body})

                (func (export "run") (result i32)
                    (local $slot i32)
                    (local $base i32)
                    call $memory_slot
                    local.tee $slot
                    table.get 0
                    i32.const 1
                    call $grow
                    i32.const 16
                    i32.shl
                    local.set $base
                    {run_body}))"#
        ))
        .map_err(Into::into)
    }

    const STRAIGHT_HOST_EFFECT: &str = r#"
        local.get $slot
        table.get 0
        local.get $base
        local.get $offset
        call $opaque_signal
    "#;

    #[test]
    fn reports_same_block_opaque_host_effect_before_memory_read() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.opaque_host_effect_memory_reads.len(), 1);
        let relation = &analysis.opaque_host_effect_memory_reads[0];
        assert_eq!(relation.offset, 3536);
        assert_eq!(relation.host_import, "host.opaque_signal");
        assert!(relation
            .runtime_binding
            .as_deref()
            .is_some_and(|name| name.starts_with("$runtime")));
        Ok(())
    }

    #[test]
    fn rejects_host_effect_memory_read_with_different_offset() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3540
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn rejects_host_effect_with_different_memory_slot() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                i32.const 3
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn rejects_memory_read_before_host_effect() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            STRAIGHT_HOST_EFFECT,
            r#"
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
                drop
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                i32.const 0
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn rejects_conditional_opaque_host_effect_wrapper() -> Result<()> {
        let bytes = host_effect_memory_fixture(
            r#"
                local.get $offset
                if
                    local.get $slot
                    table.get 0
                    local.get $base
                    local.get $offset
                    call $opaque_signal
                end
            "#,
            r#"
                local.get $slot
                local.get $base
                i32.const 3536
                call $host_effect
                local.get $base
                i32.const 3536
                i32.or
                call $memory_get
            "#,
        )?;
        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert!(analysis.opaque_host_effect_memory_reads.is_empty());
        Ok(())
    }

    #[test]
    fn names_only_proven_module_memory_get_u32_bridge_strongly() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_buffer_609cc3eee51ed158"
                    (func $buffer (param externref) (result externref)))
                (import "wbg" "__wbg_byteLength_ea52ac3de882b483"
                    (func $byte_length (param externref) (result i32)))
                (import "wbg" "__wbg_new_7e079fa25e135eb1"
                    (func $view_new (param externref i32 i32) (result externref)))
                (import "wbg" "__wbg_getUint32_9c3cc8fde7919ed4"
                    (func $get_u32 (param externref i32) (result i32)))
                (import "host" "alloc" (func $alloc (result i32)))
                (table 16 externref)

                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $alloc
                    local.tee $slot
                    call $memory
                    table.set 0
                    local.get $slot)

                (func $buffer_slot (param $memory_slot i32) (result i32)
                    (local $buffer externref)
                    (local $slot i32)
                    local.get $memory_slot
                    table.get 0
                    call $buffer
                    local.set $buffer
                    call $alloc
                    local.tee $slot
                    local.get $buffer
                    table.set 0
                    local.get $slot)

                (func $memory_get (param $offset i32) (result i32)
                    (local $memory_slot i32)
                    (local $buffer_slot i32)
                    (local $length i32)
                    (local $view externref)
                    (local $view_slot i32)
                    call $memory_slot
                    local.tee $memory_slot
                    call $buffer_slot
                    local.tee $buffer_slot
                    table.get 0
                    call $byte_length
                    local.set $length
                    local.get $buffer_slot
                    table.get 0
                    i32.const 0
                    local.get $length
                    call $view_new
                    local.set $view
                    call $alloc
                    local.tee $view_slot
                    local.get $view
                    table.set 0
                    local.get $view_slot
                    table.get 0
                    local.get $offset
                    call $get_u32)

                (func (export "run") (result i32)
                    i32.const 7
                    call $memory_get))"#,
        )?;

        let analysis = analyze_export_semantics(&bytes, "run")?;
        assert_eq!(analysis.runtime_bindings.len(), 1);
        assert_eq!(
            analysis.runtime_bindings[0].expression,
            "wbindgen.memory_get_u32(0x00000007)"
        );
        Ok(())
    }
}
