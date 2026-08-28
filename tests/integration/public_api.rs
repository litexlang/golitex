use litex::api::{
    compile_litex_source_to_lean_compilation_report, compile_litex_source_to_lean_source, run,
    OutputLanguage, OutputStyle, RunOptions, RunOutcome, RunRequest, RunTarget, RunTargetKind,
    Runtime, SourceRunOutcome, StmtResult, StmtResultToLeanCompilationReport,
};

#[test]
fn curated_api_executes_litex_inside_an_existing_runtime() {
    let mut runtime = Runtime::new(RunOptions {
        output_style: OutputStyle::Compact,
        ..RunOptions::default()
    });
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
fn curated_api_exposes_one_owned_run_entry_for_every_target_kind() {
    let options = RunOptions {
        output_style: OutputStyle::Compact,
        strict_mode: true,
        output_language: OutputLanguage::SimplifiedChinese,
        summarize: true,
        force_isolated: true,
    };
    let code = run(RunRequest::new(RunTarget::code("1 = 1"), options));
    assert!(code.ok, "{}", code.output);
    assert_eq!(code.target_kind, RunTargetKind::Code);
    assert!(code.target_path.is_none());
    assert_eq!(code.runtime.run_options, options);

    let _: fn(RunRequest) -> RunOutcome = run;
    let _: fn(&str) -> RunTarget = RunTarget::code;
    let _: fn(&str) -> RunTarget = RunTarget::file;
    let _: fn(&str) -> RunTarget = RunTarget::repository;
}

#[test]
fn curated_api_keeps_only_canonical_execution_paths_public() {
    let _: fn(&mut Runtime, &str) = Runtime::start_isolated_source;
    let _: fn(&mut Runtime, &str) -> SourceRunOutcome = Runtime::execute_source;
    let _: fn(RunRequest) -> RunOutcome = litex::pipeline::run;
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
        litex::python_extractor::to_python_from_source;
    let _: fn(&str, &str) -> Result<String, String> =
        litex::lean_compiler::compile_litex_source_to_lean_source;

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
    let _: fn(&str, &str) -> Result<String, String> =
        litex::stmt_result_to_lean_compiler::compile_litex_source_to_lean_source;
}
