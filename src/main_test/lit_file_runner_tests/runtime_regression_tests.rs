use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use crate::pipeline::{render_run_source_code_output, run_source_code};
use crate::prelude::*;
use crate::to_latex::to_latex_from_source;
use crate::to_python::to_python_from_source;

use super::helper::run_with_large_stack;

fn legacy_acceptance_field_name() -> String {
    ["accepted", "by"].join("_")
}

fn assert_no_legacy_acceptance_field(run_output: &str, context: &str) {
    let field_name = legacy_acceptance_field_name();
    assert!(
        !run_output.contains(&format!("\"{}\"", field_name)),
        "{} output should not expose legacy acceptance field:\n{}",
        context,
        run_output
    );
}

pub(super) fn run_runtime_contract_suite_impl() {
    println!("--- runtime contracts: running selected runtime/output smoke tests ---");
    runtime_contract_builtin_and_clear();
    output_contracts::unknown_fact_failure_has_structured_output_fields();
    core_definitions_and_syntax::latex_output_is_fragment_without_default_packages();
    core_definitions_and_syntax::python_extractor_outputs_supported_have_subset();
    output_contracts::detail_output_keeps_composite_fact_step_metadata();
    println!("--- runtime contracts: all selected smoke tests OK ---");
}

fn runtime_contract_builtin_and_clear() {
    let source_code = "1 = 1";

    let mut import_runtime = Runtime::new();
    import_runtime.new_file_path_new_env_new_name_scope("runtime_contract_import");
    import_runtime.strict_mode = true;
    let (import_stmt_results, import_runtime_error) =
        run_source_code(source_code, &mut import_runtime);
    let (import_run_succeeded, import_run_output) = render_run_source_code_output(
        &import_runtime,
        &import_stmt_results,
        &import_runtime_error,
        false,
    );
    assert!(
        import_run_succeeded,
        "runtime contract builtin fixture failed:\n{}",
        import_run_output
    );

    let clear_source_code =
        "abstract_prop local_prop(x)\ntrust $local_prop(2)\nclear\n$local_prop(2)";
    let mut clear_runtime = Runtime::new();
    clear_runtime.new_file_path_new_env_new_name_scope("runtime_contract_clear");
    let (clear_stmt_results, clear_runtime_error) =
        run_source_code(clear_source_code, &mut clear_runtime);
    let (clear_succeeded, clear_output) = render_run_source_code_output(
        &clear_runtime,
        &clear_stmt_results,
        &clear_runtime_error,
        false,
    );
    assert!(
        !clear_succeeded,
        "runtime contract clear fixture should drop local facts:\n{}",
        clear_output
    );
}

mod core_definitions_and_syntax;
mod definitions_and_runtime;
mod finite_set_induction;
mod functions_sets_and_iterated;
mod kernel_soundness;
mod missing_numeric_builtins;
mod numeric_and_set_rules;
mod output_contracts;
mod proof_control_and_choice;
mod structural_definitions;
