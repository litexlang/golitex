use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use crate::pipeline::render_run_output;
use crate::prelude::*;
use crate::test_support::execute_source;
use crate::to_latex::to_latex_from_source;
use crate::to_python::to_python_from_source;

use super::helper::run_with_large_stack;

fn run_repository_for_test(
    repository_path: &str,
    detailed_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    let outcome = run(RunRequest::new(
        RunTarget::repository(repository_path),
        RunOptions {
            output_style: if detailed_output {
                OutputStyle::Detailed
            } else {
                OutputStyle::Normal
            },
            strict_mode,
            output_language,
            summarize,
            ..RunOptions::default()
        },
    ));
    (outcome.ok, outcome.output)
}

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
    runtime_contract_builtin();
    output_contracts::unknown_fact_failure_has_structured_output_fields();
    core_definitions_and_syntax::latex_output_is_fragment_without_default_packages();
    core_definitions_and_syntax::python_extractor_outputs_supported_have_subset();
    output_contracts::detail_output_keeps_composite_fact_step_metadata();
    println!("--- runtime contracts: all selected smoke tests OK ---");
}

#[test]
fn runtime_contract_builtin() {
    let source_code = "1 = 1";

    let mut import_runtime = Runtime::default();
    import_runtime.start_isolated_source("runtime_contract_import");
    import_runtime.strict_mode = true;
    let (import_stmt_results, import_runtime_error) =
        execute_source(source_code, &mut import_runtime);
    let (import_run_succeeded, import_run_output) =
        render_run_output(&import_runtime, &import_stmt_results, &import_runtime_error);
    assert!(
        import_run_succeeded,
        "runtime contract builtin fixture failed:\n{}",
        import_run_output
    );
}

mod builtin_interfaces;
mod callable_aliases;
mod complex_scalars;
mod core_definitions_and_syntax;
mod definitions_and_runtime;
mod finite_set_induction;
mod functions_sets_and_iterated;
mod indexed_set_family;
mod kernel_soundness;
mod matrix_semantics;
mod missing_numeric_builtins;
mod native_exp_sign_factorial;
mod native_number_theory;
mod native_real_constants;
mod native_rounding_extrema;
mod native_trigonometry;
mod numeric_and_set_rules;
mod output_contracts;
mod proof_control_and_choice;
mod proper_set_relations;
mod quantifier_free_builtin_premises;
mod sequence_semantics;
mod setting_syntax;
mod structural_definitions;
