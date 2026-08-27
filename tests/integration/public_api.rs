use litex::api::{
    compile_litex_source_to_lean_compilation_report, compile_litex_source_to_lean_source, run,
    OutputLanguage, OutputStyle, RunOptions, RunOutcome, RunRequest, RunTarget, RunTargetKind,
    Runtime, SourceRunOutcome, StmtResult, StmtResultToLeanCompilationReport,
};

#[test]
fn curated_api_executes_litex_inside_an_existing_runtime() {
    let mut runtime = Runtime::new(OutputStyle::Compact, false, OutputLanguage::English);
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
    let code = run(RunRequest::new(
        RunTarget::code("1 = 1"),
        RunOptions::default(),
    ));
    assert!(code.ok, "{}", code.output);
    assert_eq!(code.target_kind, RunTargetKind::Code);
    assert!(code.target_path.is_none());

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

    let _: fn(&litex::obj::FnSet) -> litex::stmt::definition_stmt::FnSetClause =
        litex::execute::function_equality_support::fn_set_to_fn_set_clause;
}
