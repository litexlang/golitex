use litex::api::{
    compile_litex_source_to_lean_compilation_report, compile_litex_source_to_lean_source, run_code,
    run_file, run_isolated_file, run_repository, FileRunMode, OutputLanguage, OutputStyle,
    RunOptions, RunOutcome, RunTarget, RunTargetKind, Runtime, SourceRunOutcome, StmtResult,
    StmtResultToLeanCompilationReport,
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
fn curated_api_exposes_one_owned_entry_for_every_batch_input() {
    let options = RunOptions {
        output_style: OutputStyle::Compact,
        strict_mode: true,
        output_language: OutputLanguage::SimplifiedChinese,
        summarize: true,
        is_isolated: false,
    };
    let code = run_code("1 = 1", options);
    assert!(code.ok, "{}", code.output);
    assert_eq!(code.target, RunTarget::Eval);
    assert_eq!(code.target.kind(), RunTargetKind::Code);
    assert!(code.target.path().is_none());
    assert_eq!(code.runtime.run_options, options);

    let project_file = run_file("missing-project-file.lit", RunOptions::default());
    assert!(matches!(
        project_file.target,
        RunTarget::File {
            mode: FileRunMode::Project,
            ..
        }
    ));
    let isolated_file = run_file(
        "missing-isolated-file.lit",
        RunOptions {
            is_isolated: true,
            ..RunOptions::default()
        },
    );
    assert!(matches!(
        isolated_file.target,
        RunTarget::File {
            mode: FileRunMode::Isolated,
            ..
        }
    ));
    assert!(isolated_file.runtime.run_options.is_isolated);
    let compatibility_isolated_file =
        run_isolated_file("missing-compatibility-file.lit", RunOptions::default());
    assert!(matches!(
        compatibility_isolated_file.target,
        RunTarget::File {
            mode: FileRunMode::Isolated,
            ..
        }
    ));
    assert!(compatibility_isolated_file.runtime.run_options.is_isolated);
    let repository = run_repository("missing-project", RunOptions::default());
    assert!(matches!(repository.target, RunTarget::Repository { .. }));

    let _: fn(&str, RunOptions) -> RunOutcome = run_code;
    let _: fn(&str, RunOptions) -> RunOutcome = run_file;
    let _: fn(&str, RunOptions) -> RunOutcome = run_isolated_file;
    let _: fn(&str, RunOptions) -> RunOutcome = run_repository;
    let _: FileRunMode = FileRunMode::Isolated;
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
