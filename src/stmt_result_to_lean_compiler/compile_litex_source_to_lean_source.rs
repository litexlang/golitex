use super::{StmtResultToLeanCompilationReport, StmtResultToLeanCompiler};
use crate::prelude::*;

pub fn compile_litex_source_to_lean_source(
    source: &str,
    source_label: &str,
) -> Result<String, String> {
    let results = execute_litex_source_to_stmt_results(source, source_label)
        .map_err(|error| format!("Litex execution failed before Lean compilation: {error:?}"))?;
    StmtResultToLeanCompiler::new(source_label).compile_stmt_results_to_lean_source(&results)
}

pub fn compile_litex_source_to_stmt_result_to_lean_compilation_report(
    source: &str,
    source_label: &str,
) -> Result<StmtResultToLeanCompilationReport, String> {
    let results = execute_litex_source_to_stmt_results(source, source_label)
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

pub(crate) fn execute_litex_source_to_stmt_results(
    source: &str,
    source_label: &str,
) -> Result<Vec<StmtResult>, RuntimeError> {
    let normalized = source.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.isolated = true;
    runtime.new_file_path_new_env_new_name_scope(source_label);
    let tokenizer = Tokenizer::new();
    let blocks = tokenizer.parse_blocks(&normalized, runtime.current_file_path_rc())?;
    let mut results = Vec::new();
    for mut block in blocks {
        let statement = runtime.parse_stmt(&mut block)?;
        if matches!(statement, Stmt::Command(CommandStmt::ImportStmt(_))) {
            return Err(stmt_result_to_lean_compilation_error(
                &statement.line_file(),
                "single-file StmtResult-to-Lean compilation does not support `import`",
            ));
        }
        let result = run_stmt_at_global_env(&statement, &mut runtime)?;
        if result.is_unknown() {
            return Err(stmt_result_to_lean_compilation_error(
                &statement.line_file(),
                "StmtResult-to-Lean compilation received an unknown statement result",
            ));
        }
        results.push(result);
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
