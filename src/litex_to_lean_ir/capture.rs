use crate::prelude::*;

/// Verify one standalone Litex source and return the exact backend-facing IR
/// captured from that successful verifier run.
pub fn capture_litex_to_lean_ir_from_source(
    source_code: &str,
    entry_label: &str,
) -> Result<Vec<LitexToLeanStatementIr>, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    let started_capture = runtime.start_well_defined_capture();
    let result = capture_litex_to_lean_ir(&normalized, &mut runtime);
    if started_capture {
        runtime.stop_well_defined_capture();
    }
    result
}

fn capture_litex_to_lean_ir(
    source_code: &str,
    runtime: &mut Runtime,
) -> Result<Vec<LitexToLeanStatementIr>, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let blocks = tokenizer.parse_blocks(source_code, runtime.current_file_path_rc())?;
    let mut ir = Vec::new();
    for mut block in blocks {
        let statement = runtime.parse_stmt(&mut block)?;
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(litex_to_lean_ir_error(
                &statement.line_file(),
                "Litex-to-Lean received an unverified Litex statement",
            ));
        }
        let Some(statement_ir) = result.litex_to_lean_ir() else {
            return Err(litex_to_lean_ir_error(
                &statement.line_file(),
                "Litex-to-Lean capture completed a statement without producing IR",
            ));
        };
        ir.push(statement_ir.clone());
    }
    if ir.is_empty() {
        return Err(litex_to_lean_ir_error(
            &default_line_file(),
            "Litex-to-Lean requires at least one supported statement",
        ));
    }
    Ok(ir)
}

fn litex_to_lean_ir_error(line_file: &LineFile, message: &str) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.to_string(),
        line_file.clone(),
        None,
        vec![],
    ))
    .into()
}
