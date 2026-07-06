use super::helpers_by_stmt::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_contra_stmt(&mut self, stmt: &ByContraStmt) -> Result<StmtResult, RuntimeError> {
        let to_prove_fact = stmt.to_prove.clone();
        self.verify_fact_well_defined(&to_prove_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by contra: failed to prove `{}`", to_prove_fact),
                    Some(verify_error),
                    vec![],
                )
            })?;

        let (exec_proof_inside_results, last_error) = self.run_in_local_env(|rt| {
            let mut inside_results: Vec<StmtResult> = Vec::new();

            let reverse_to_prove_fact = reverse_fact_for_by_contra(&to_prove_fact)?;
            rt.verify_well_defined_and_store_and_infer_with_default_verify_state(
                reverse_to_prove_fact,
            )
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by contra: failed to store reverse of `{}`", to_prove_fact),
                    Some(store_fact_error),
                    vec![],
                )
            })?;

            let mut last_error: Option<RuntimeError> = None;
            for proof_stmt in stmt.proof.iter() {
                let exec_stmt_result = rt.exec_stmt(proof_stmt);
                match exec_stmt_result {
                    Ok(result) => inside_results.push(result),
                    Err(statement_error) => {
                        last_error = Some(statement_error);
                        break;
                    }
                }
            }

            if last_error.is_some() {
                return Ok((inside_results, last_error));
            }

            let verify_impossible_fact_result =
                rt.verify_atomic_fact(&stmt.impossible_fact, &VerifyState::new(0, false))?;
            if verify_impossible_fact_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    impossible_proof_error_message(&stmt.impossible_fact, None),
                    None,
                    inside_results,
                ));
            }

            let verify_reversed_impossible_fact_result = rt.verify_atomic_fact(
                &stmt.impossible_fact.make_reversed(),
                &VerifyState::new(0, false),
            )?;
            if verify_reversed_impossible_fact_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    impossible_proof_error_message(&stmt.impossible_fact, None),
                    None,
                    vec![],
                ));
            }
            inside_results.push(verify_impossible_fact_result);
            inside_results.push(verify_reversed_impossible_fact_result);

            Ok((inside_results, last_error))
        })?;

        if let Some(last_error) = last_error {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by contra: failed to execute proof".to_string(),
                Some(last_error),
                exec_proof_inside_results,
            ));
        }

        let to_prove_fact_display_string = to_prove_fact.to_string();
        let infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(to_prove_fact)
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by contra: failed to release `{}`",
                        to_prove_fact_display_string
                    ),
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        let reverse_assumption = reverse_fact_for_by_contra(&stmt.to_prove)?;
        let by_verification = ByContraVerificationResult::new(
            stmt.to_prove.clone(),
            reverse_assumption,
            stmt.proof.len(),
            stmt.impossible_fact.clone(),
        )
        .into();

        Ok((NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            exec_proof_inside_results,
            by_verification,
        ))
        .into())
    }
}

fn reverse_fact_for_by_contra(fact: &Fact) -> Result<Fact, RuntimeError> {
    match fact {
        Fact::AtomicFact(atomic_fact) => Ok(atomic_fact.make_reversed().into()),
        Fact::ForallFact(forall_fact) => Ok(NotForallFact::new(forall_fact.clone()).into()),
        Fact::NotForall(not_forall) => Ok(not_forall.forall_fact.clone().into()),
        Fact::ExistFact(exist_fact) => match exist_fact {
            ExistFactEnum::ExistFact(body) => Ok(ExistFactEnum::NotExistFact(body.clone()).into()),
            ExistFactEnum::NotExistFact(body) => Ok(ExistFactEnum::ExistFact(body.clone()).into()),
            ExistFactEnum::ExistUniqueFact(_) => Err(RuntimeError::ExecStmtError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "by contra: cannot build reverse assumption for `{}` yet",
                        fact
                    ),
                    fact.line_file(),
                ),
            )),
        },
        Fact::OrFact(_) | Fact::AndFact(_) | Fact::ChainFact(_) | Fact::ForallFactWithIff(_) => {
            Err(RuntimeError::ExecStmtError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "by contra: cannot build reverse assumption for `{}` yet",
                        fact
                    ),
                    fact.line_file(),
                ),
            ))
        }
    }
}
