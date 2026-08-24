use litex::api::{
    compile_litex_source_to_lean_source, run_file, run_repository, run_source_code,
    run_source_code_in_file_with_ok, run_source_code_with_options, FileRunOptions, OutputLanguage,
    OutputStyle, RunOutputOptions, Runtime, SourceRunOptions, StmtResult,
};

#[test]
fn curated_api_executes_litex_without_the_internal_prelude() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("public-api.lit");
    runtime.set_output_style(OutputStyle::Compact);
    runtime.output_language = OutputLanguage::English;

    let (results, error) = run_source_code("1 = 1", &mut runtime);

    assert!(error.is_none(), "{error:?}");
    assert_eq!(results.len(), 1);
    let _: &StmtResult = &results[0];
}

#[test]
fn curated_api_exposes_a_structured_source_run() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("structured-source-run.lit");

    let outcome = run_source_code_with_options("1 = 1", &mut runtime, SourceRunOptions::default());

    assert!(
        outcome.runtime_error.is_none(),
        "{:?}",
        outcome.runtime_error
    );
    assert!(outcome.failure_kind.is_none());
    assert_eq!(outcome.stmt_results.len(), 1);
}

#[test]
fn curated_api_keeps_existing_module_paths_compatible() {
    let _: fn(&mut Runtime, &str) = Runtime::start_isolated_source;
    let _: fn(&mut Runtime, &str) = Runtime::new_file_path_new_env_new_name_scope;

    let _: fn(
        &str,
        &mut litex::runtime::Runtime,
    ) -> (
        Vec<litex::result::StmtResult>,
        Option<litex::error::RuntimeError>,
    ) = litex::pipeline::run_source_code;
    let _: fn(
        &str,
        &mut litex::runtime::Runtime,
    ) -> (
        Vec<litex::result::StmtResult>,
        Option<litex::error::RuntimeError>,
    ) = litex::pipeline::source_execution::run_source_code;
    let _: fn(
        &str,
        &mut litex::runtime::Runtime,
    ) -> (
        Vec<litex::result::StmtResult>,
        Option<litex::error::RuntimeError>,
    ) = litex::pipeline::pipeline::run_source_code;

    let _: fn(&str) -> (bool, String) = run_source_code_in_file_with_ok;
    let _: fn(&str, FileRunOptions) -> (bool, String) = run_file;
    let _: fn(&str, RunOutputOptions) -> (bool, String) = run_repository;
    let _: fn(&str) -> Result<String, String> = litex::pipeline::resolve_source_file_path;
    let _: fn(&str) -> Result<String, String> = litex::runner::resolve_litex_file_path;
    let _: fn(&str, &str) -> Result<String, String> = compile_litex_source_to_lean_source;
}
