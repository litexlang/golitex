use litex::api::{
    compile_litex_source_to_lean_compilation_report, compile_litex_source_to_lean_source, run_code,
    run_file, run_isolated_file, run_repository, ExecutionOption, OutputDetail, OutputLanguage,
    RunOption, RunOptions, RunOutcome, RunTarget, RunTargetKind, Runtime, SourceRunOutcome,
    StmtResult, StmtResultToLeanCompilationReport, SummaryOption,
};

#[test]
fn curated_api_executes_litex_inside_an_existing_runtime() {
    let mut runtime = Runtime::new(
        RunOptions::execute(ExecutionOption::Eval).with_output_detail(OutputDetail::Compact),
    );
    runtime.start_isolated_source("public-api.lit");

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
    let options = RunOptions::strict_execute(ExecutionOption::Eval)
        .with_output_detail(OutputDetail::Compact)
        .with_output_language(OutputLanguage::SimplifiedChinese)
        .with_summary(SummaryOption::Summarize);
    let code = run_code("1 = 1", options);
    assert!(code.ok, "{}", code.output);
    assert_eq!(code.target, RunTarget::Eval);
    assert_eq!(code.target.kind(), RunTargetKind::Code);
    assert!(code.target.path().is_none());
    assert_eq!(code.runtime.run_options, options);

    let project_file = run_file(
        "missing-project-file.lit",
        RunOptions::execute(ExecutionOption::IsolatedFile),
    );
    assert!(matches!(project_file.target, RunTarget::File { .. }));
    assert_eq!(
        project_file.runtime.run_options.run(),
        RunOption::Execute(ExecutionOption::File)
    );
    let isolated_file = run_isolated_file(
        "missing-isolated-file.lit",
        RunOptions::execute(ExecutionOption::File),
    );
    assert!(matches!(
        isolated_file.target,
        RunTarget::IsolatedFile { .. }
    ));
    assert!(isolated_file.runtime.run_options.is_isolated());
    assert_eq!(
        isolated_file.runtime.run_options.run(),
        RunOption::Execute(ExecutionOption::IsolatedFile)
    );
    let repository = run_repository("missing-project", RunOptions::default());
    assert!(matches!(repository.target, RunTarget::Repository { .. }));
    assert_eq!(
        repository.runtime.run_options.run(),
        RunOption::Execute(ExecutionOption::Repo)
    );

    let _: fn(&str, RunOptions) -> RunOutcome = run_code;
    let _: fn(&str, RunOptions) -> RunOutcome = run_file;
    let _: fn(&str, RunOptions) -> RunOutcome = run_isolated_file;
    let _: fn(&str, RunOptions) -> RunOutcome = run_repository;
}

#[test]
fn curated_api_keeps_only_canonical_execution_paths_public() {
    let _: fn(&mut Runtime, &str) = Runtime::start_isolated_source;
    let _: fn(&mut Runtime, &str) -> SourceRunOutcome = Runtime::execute_source;
    let _: fn(&str, RunOptions) -> RunOutcome = litex::pipeline::run_code;
    let _: fn(&str, RunOptions) -> RunOutcome = litex::pipeline::run_file;
    let _: fn(&str, RunOptions) -> RunOutcome = litex::pipeline::run_isolated_file;
    let _: fn(&str, RunOptions) -> RunOutcome = litex::pipeline::run_repository;
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
