use litex::api::{
    compile_litex_source_to_lean_source, run_source_code, run_source_code_in_file_with_ok,
    OutputLanguage, OutputStyle, Runtime, StmtResult,
};

#[test]
fn curated_api_executes_litex_without_the_internal_prelude() {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope("public-api.lit");
    runtime.set_output_style(OutputStyle::Compact);
    runtime.output_language = OutputLanguage::English;

    let (results, error) = run_source_code("1 = 1", &mut runtime);

    assert!(error.is_none(), "{error:?}");
    assert_eq!(results.len(), 1);
    let _: &StmtResult = &results[0];
}

#[test]
fn curated_api_keeps_existing_module_paths_compatible() {
    let _: fn(
        &str,
        &mut litex::runtime::Runtime,
    ) -> (
        Vec<litex::result::StmtResult>,
        Option<litex::error::RuntimeError>,
    ) = litex::pipeline::run_source_code;

    let _: fn(&str) -> (bool, String) = run_source_code_in_file_with_ok;
    let _: fn(&str, &str) -> Result<String, String> = compile_litex_source_to_lean_source;
}
