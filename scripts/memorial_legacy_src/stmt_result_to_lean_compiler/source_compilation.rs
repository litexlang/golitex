use super::{StmtResultToLeanCompilationReport, StmtResultToLeanCompiler};
use crate::prelude::*;

pub fn compile_litex_source_to_lean_source(
    source: &str,
    source_label: &str,
) -> Result<String, String> {
    let results = execute_litex_source_for_lean_compilation(source, source_label)
        .map_err(|error| format!("Litex execution failed before Lean compilation: {error:?}"))?;
    StmtResultToLeanCompiler::new(source_label).compile_stmt_results_to_lean_source(&results)
}

pub fn compile_litex_source_to_lean_compilation_report(
    source: &str,
    source_label: &str,
) -> Result<StmtResultToLeanCompilationReport, String> {
    let results = execute_litex_source_for_lean_compilation(source, source_label)
        .map_err(|error| format!("Litex execution failed before Lean compilation: {error:?}"))?;
    Ok(
        match StmtResultToLeanCompiler::new(source_label)
            .compile_stmt_results_to_lean_source(&results)
        {
            Ok(lean_code) => StmtResultToLeanCompilationReport::complete(lean_code),
            Err(reason) => StmtResultToLeanCompilationReport::incomplete_lean_source_construction(
                source_label,
                reason,
            ),
        },
    )
}

pub fn execute_litex_source_for_lean_compilation(
    source: &str,
    _source_label: &str,
) -> Result<Vec<StmtResult>, RuntimeError> {
    let normalized = source.replace('\r', "");
    let mut runtime = Runtime::with_virtual_source(VirtualSource::ToLean);
    let outcome = runtime.execute_source(&normalized);
    if let Some(error) = outcome.runtime_error {
        return Err(error);
    }
    let results = outcome.stmt_results;
    if let Some(result) = results.iter().find(|result| result.is_unknown()) {
        return Err(stmt_result_to_lean_compilation_error(
            &result.line_file(),
            "StmtResult-to-Lean compilation received an unknown statement result",
        ));
    }
    if results.is_empty() {
        return Err(stmt_result_to_lean_compilation_error(
            &default_line_file(),
            "StmtResult-to-Lean compilation requires at least one successful statement result",
        ));
    }
    drop(runtime);
    Ok(results)
}

fn stmt_result_to_lean_compilation_error(line_file: &LineFile, message: &str) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.to_string(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}
