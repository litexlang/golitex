use super::LitexToLeanIrBuilder;
use crate::prelude::*;

/// Verify every statement in one standalone Litex source, retain the complete
/// ordered `StmtResult` sequence, and only then lower that completed sequence
/// to the Lean backend IR.
pub fn capture_litex_to_lean_ir_from_source(
    source_code: &str,
    entry_label: &str,
) -> Result<Vec<LitexToLeanStatementIr>, RuntimeError> {
    let normalized = source_code.replace('\r', "");
    let mut runtime = Runtime::new();
    runtime.isolated = true;
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
    let results = execute_single_file_source(source_code, runtime)?;
    let builder = LitexToLeanIrBuilder::new(runtime);
    results
        .iter()
        .map(|result| builder.compile_statement(result))
        .collect()
}

fn execute_single_file_source(
    source_code: &str,
    runtime: &mut Runtime,
) -> Result<Vec<StmtResult>, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let blocks = tokenizer.parse_blocks(source_code, runtime.current_file_path_rc())?;
    let mut results = Vec::new();
    for mut block in blocks {
        let statement = runtime.parse_stmt(&mut block)?;
        if matches!(statement, Stmt::Command(CommandStmt::ImportStmt(_))) {
            return Err(litex_to_lean_ir_error(
                &statement.line_file(),
                "single-file Litex-to-Lean does not support `import`; compile a standalone file",
            ));
        }
        let result = run_stmt_at_global_env(&statement, runtime)?;
        if result.is_unknown() {
            return Err(litex_to_lean_ir_error(
                &statement.line_file(),
                "Litex-to-Lean received an unverified Litex statement",
            ));
        }
        results.push(result);
    }
    if results.is_empty() {
        return Err(litex_to_lean_ir_error(
            &default_line_file(),
            "Litex-to-Lean requires at least one supported statement",
        ));
    }
    Ok(results)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_file_execution_finishes_verified_stmt_ir_before_lowering() {
        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("known_equality_result.lit");
        runtime.start_well_defined_capture();

        let results = execute_single_file_source(
            "forall a, b set:\n    a = b\n    =>:\n        b = a\n",
            &mut runtime,
        )
        .expect("verify the whole single-file source");

        assert_eq!(results.len(), 1);
        let StmtResult::Success(VerifiedStmtIr {
            statement,
            verification,
            ..
        }) = &results[0]
        else {
            panic!("expected one completed VerifiedStmtIr");
        };
        assert!(matches!(statement, Stmt::Fact(Fact::ForallFact(_))));
        assert!(matches!(
            verification,
            VerifiedStmtVerificationIr::Fact(FactualStmtSuccess {
                verified_by: VerifiedByResult::ForallProof(_),
                ..
            })
        ));
    }
}
