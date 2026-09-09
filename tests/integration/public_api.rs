use litex::api::{
    compile_litex_source_to_lean_compilation_report, compile_litex_source_to_lean_source,
    run_eval_command, run_file_command, run_isolated_file_command, run_repository_command,
    RuntimeOptions, OutputDetail, OutputLanguage, RunOutcome, RunTarget, RunTargetKind,
    Runtime, SourceRunOutcome, StmtResult, StmtResultToLeanCompilationReport, SummaryOption,
    VerifyStrictnessPolicy,
};

#[test]
fn curated_api_executes_litex_inside_an_existing_runtime() {
    let mut runtime = Runtime::new(RuntimeOptions::new(
        VerifyStrictnessPolicy::Ordinary,
        OutputDetail::Compact,
        OutputLanguage::English,
        SummaryOption::None,
    ));
    runtime.start_virtual_source(litex::api::VirtualSource::Named(
        "public-api.lit".to_string(),
    ));

    let SourceRunOutcome {
        stmt_results: results,
        runtime_error: error,
    } = runtime.execute_source("1 = 1");

    assert!(error.is_none(), "{error:?}");
    assert_eq!(results.len(), 1);
    let _: &StmtResult = &results[0];
}

#[test]
fn curated_api_exposes_one_owned_entry_for_every_batch_input() {
    let options = RuntimeOptions::new(
        VerifyStrictnessPolicy::Strict,
        OutputDetail::Compact,
        OutputLanguage::SimplifiedChinese,
        SummaryOption::Summarize,
    );
    let code = run_eval_command("1 = 1", options);
    assert!(code.ok, "{}", code.output);
    assert_eq!(code.target, RunTarget::Eval);
    assert_eq!(code.target.kind(), RunTargetKind::Code);
    assert!(code.target.path().is_none());
    assert_eq!(code.runtime.execution_options, options);

    let automatic_file = run_file_command(
        "missing-project-file.lit",
        RuntimeOptions::ordinary(
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        ),
    );
    assert!(matches!(
        automatic_file.target,
        RunTarget::IsolatedFile { .. }
    ));
    assert_eq!(
        automatic_file.runtime.execution_options.verify_strictness(),
        VerifyStrictnessPolicy::Ordinary
    );
    let isolated_file = run_isolated_file_command(
        "missing-isolated-file.lit",
        RuntimeOptions::ordinary(
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        ),
    );
    assert!(matches!(
        isolated_file.target,
        RunTarget::IsolatedFile { .. }
    ));
    assert_eq!(
        isolated_file.runtime.execution_options.verify_strictness(),
        VerifyStrictnessPolicy::Ordinary
    );
    let repository = run_repository_command("missing-project", RuntimeOptions::default());
    assert!(matches!(repository.target, RunTarget::Repository { .. }));
    assert_eq!(
        repository.runtime.execution_options.verify_strictness(),
        VerifyStrictnessPolicy::Ordinary
    );

    let _: fn(&str, RuntimeOptions) -> RunOutcome = run_eval_command;
    let _: fn(&str, RuntimeOptions) -> RunOutcome = run_file_command;
    let _: fn(&str, RuntimeOptions) -> RunOutcome = run_isolated_file_command;
    let _: fn(&str, RuntimeOptions) -> RunOutcome = run_repository_command;
}

#[test]
fn curated_api_keeps_only_canonical_execution_paths_public() {
    let _: fn(&mut Runtime, litex::api::VirtualSource) = Runtime::start_virtual_source;
    let _: fn(&mut Runtime, &str) -> SourceRunOutcome = Runtime::execute_source;
    let _: fn(&str, RuntimeOptions) -> RunOutcome = litex::pipeline::run_eval_command;
    let _: fn(&str, RuntimeOptions) -> RunOutcome = litex::pipeline::run_file_command;
    let _: fn(&str, RuntimeOptions) -> RunOutcome =
        litex::pipeline::run_isolated_file_command;
    let _: fn(&str, RuntimeOptions) -> RunOutcome = litex::pipeline::run_repository_command;
    let _: fn(&str) -> Result<String, String> = litex::pipeline::resolve_source_file_path;
    let _: fn(&str, &str) -> Result<String, String> = compile_litex_source_to_lean_source;
    let _: fn(&str, &str) -> Result<StmtResultToLeanCompilationReport, String> =
        compile_litex_source_to_lean_compilation_report;

    let _: fn(&litex::object::FnSet) -> litex::statement::definition_stmt::FnSetClause =
        litex::execution::function_equality_support::fn_set_to_fn_set_clause;
    let _: Option<litex::statement::proof_directives::ByThmStmt> = None;
    let _: Option<litex::parsing::Tokenizer> = None;
    let _: Option<litex::inference::InferRule> = None;
    let _: Option<litex::verification::VerifyState> = None;
    let _: Option<litex::module_system::ModuleManager> = None;
    let _: fn(&str, &str) -> Result<String, litex::error::RuntimeError> =
        litex::latex_renderer::to_latex_from_source;
    let _: fn(&str, &str) -> Result<String, litex::error::RuntimeError> =
        litex::extract_code_of_other_languages_from_litex::python::to_python_from_source;
    let _: fn(&str, &str) -> Result<String, litex::error::RuntimeError> =
        litex::extract_code_of_other_languages_from_litex::c::to_c_from_source;
    let _: fn(&str, &str) -> Result<String, String> =
        litex::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source;

    // Compatibility aliases remain available for one version.
    let _: fn(&litex::object::FnSet) -> litex::statement::definition_stmt::FnSetClause =
        litex::execute::function_equality_support::fn_set_to_fn_set_clause;
    let _: fn(&litex::obj::FnSet) -> litex::stmt::definition_stmt::FnSetClause =
        litex::execute::function_equality_support::fn_set_to_fn_set_clause;
    let _: Option<litex::stmt::explicit_verify::ByThmStmt> = None;
    let _: Option<litex::parse::Tokenizer> = None;
    let _: Option<litex::infer::InferRule> = None;
    let _: Option<litex::verify::VerifyState> = None;
    let _: Option<litex::module_manager::ModuleManager> = None;
    let _: fn(&str, &str) -> Result<String, litex::error::RuntimeError> =
        litex::to_latex::to_latex_from_source;
    let _: fn(&str, &str) -> Result<String, litex::error::RuntimeError> =
        litex::to_python::to_python_from_source;
    let _: fn(&str, &str) -> Result<String, litex::error::RuntimeError> =
        litex::to_c::to_c_from_source;
}

#[test]
#[allow(deprecated)]
fn output_api_exposes_canonical_names_and_legacy_shims() {
    let _: fn(&StmtResult) -> String = litex::api::render_statement_result_json;
    let _: fn(&Runtime, &litex::error::RuntimeError, bool) -> String =
        litex::api::render_runtime_error_json;
    let _: Option<OutputDetail> = None;

    let _: fn(&StmtResult) -> String = litex::api::display_stmt_result_json_v2;
    let _: fn(&Runtime, &StmtResult, bool) -> String = litex::api::display_stmt_exec_result_json;
    let _: Option<litex::api::OutputStyle> = None;
    let _: fn(
        &Runtime,
        &litex::error::RuntimeErrorUnknownResult,
        OutputDetail,
    ) -> litex::output::json_value::JsonValue = litex::output::unknown_result_json_value;
}
