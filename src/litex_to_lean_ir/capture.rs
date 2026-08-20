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
    let results = execute_single_file_source(&normalized, &mut runtime)?;
    drop(runtime);
    lower_completed_stmt_results(&results)
}

fn lower_completed_stmt_results(
    results: &[StmtResult],
) -> Result<Vec<LitexToLeanStatementIr>, RuntimeError> {
    let builder = LitexToLeanIrBuilder::new();
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
    fn compositional_fact_result_retains_wd_evaluation_store_and_infer() {
        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("compositional_stmt_result.lit");
        let mut results = execute_single_file_source("2 + 3 $in N\n", &mut runtime)
            .expect("execute the compositional fact tracer");
        assert_eq!(results.len(), 1);
        let StmtResult::Success(SuccessStmtResult::Fact(success)) = results.remove(0) else {
            panic!("expected one successful fact statement");
        };

        assert!(success.well_definedness.recursive.is_some());
        let SuccessFactProofResult::BuiltinRule(builtin) = success.underlying_verified_by() else {
            panic!("expected a direct builtin proof");
        };
        let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = &builtin.evidence else {
            panic!("expected retained numeric membership evidence");
        };
        assert_eq!(evidence.evaluation.value.normalized_value, "5");
        let SuccessEvaluateObjStepResult::Binary(addition) = &evidence.evaluation.step else {
            panic!("expected the retained addition node");
        };
        assert_eq!(addition.operator, EvaluateBinaryObjOperator::Add);

        let source_fact_id = success.fact_id.expect("source fact should be stored");
        let source_store = success
            .infers
            .store_fact_outputs
            .iter()
            .find(|output| output.fact_id == Some(source_fact_id))
            .expect("store output should cite the source FactId");
        assert_eq!(
            source_store.itself_and_why_itself_is_stored.0.to_string(),
            "2 + 3 $in N"
        );
        assert_eq!(source_store.inferred_facts.len(), 1);
        assert_eq!(source_store.inferred_facts[0].to_string(), "2 + 3 >= 0");
        let inferred_fact_id = source_store.inferred_fact_ids[0]
            .expect("inferred nonnegativity should retain its FactId");
        assert_ne!(source_fact_id, inferred_fact_id);
    }

    #[test]
    fn completed_result_lowers_after_execution_runtime_is_dropped() {
        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("runtime_free_lowering.lit");
        let results = execute_single_file_source("2 + 3 $in N\n", &mut runtime)
            .expect("execute before dropping the runtime");
        drop(runtime);

        let lowered = lower_completed_stmt_results(&results)
            .expect("lowering must consume only the completed recursive Result");
        let [LitexToLeanStatementIr::Fact(statement)] = lowered.as_slice() else {
            panic!("expected one lowered fact statement");
        };
        let LitexToLeanFactProofIr::RuleApplication { rule, premises, .. } =
            &statement.source.proof
        else {
            panic!("expected a rule application");
        };
        let LitexToLeanProofRuleIr::ClosedNumericMembership(evidence) = rule else {
            panic!("expected retained closed numeric membership evidence");
        };
        assert!(premises.is_empty());
        assert_eq!(evidence.target_set, StandardSet::N);
        assert_eq!(evidence.evaluation.value.normalized_value, "5");
    }

    #[test]
    fn single_file_execution_finishes_success_stmt_result_before_lowering() {
        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("known_equality_result.lit");
        let results = execute_single_file_source(
            "forall a, b set:\n    a = b\n    =>:\n        b = a\n",
            &mut runtime,
        )
        .expect("verify the whole single-file source");

        assert_eq!(results.len(), 1);
        let StmtResult::Success(SuccessStmtResult::Fact(success)) = &results[0] else {
            panic!("expected one completed forall-fact IR");
        };
        assert!(matches!(
            success.verification.as_ref(),
            SuccessVerifyFactResult::ForallFact(_)
        ));
        assert!(matches!(
            success.proof(),
            SuccessFactProofResult::ForallProof(_)
        ));
    }

    #[test]
    fn explicit_trust_and_checked_fact_have_distinct_ir_variants() {
        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("trust_shape.lit");

        let results = execute_single_file_source("trust:\n    1 = 1\n\n1 = 1\n", &mut runtime)
            .expect("execute explicit trust followed by an ordinary checked fact");

        assert!(matches!(
            &results[0],
            StmtResult::Success(SuccessStmtResult::UnsafeStmt(
                SuccessUnsafeStmtResult::TrustStmt(_)
            ))
        ));
        assert!(matches!(
            &results[1],
            StmtResult::Success(SuccessStmtResult::Fact(success))
                if matches!(
                    success.verification.as_ref(),
                    SuccessVerifyFactResult::AtomicFact(_)
                )
        ));
    }

    #[test]
    fn axiom_and_theorem_have_distinct_top_level_ir_variants() {
        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("axiom_theorem_shape.lit");

        let results = execute_single_file_source(
            "axiom assumed_reflexive:\n    ? forall a R:\n        a = a\n\nthm checked_reflexive:\n    ? forall a R:\n        a = a\n",
            &mut runtime,
        )
        .expect("execute one axiom and one checked theorem");

        assert!(matches!(
            &results[0],
            StmtResult::Success(SuccessStmtResult::AxiomStmt(_))
        ));
        assert!(matches!(
            &results[1],
            StmtResult::Success(SuccessStmtResult::DefThmStmt(result))
                if result.verification.is_some()
        ));
    }
}
