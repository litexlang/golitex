use crate::prelude::*;

impl Runtime {
    pub fn exec_by_def_stmt(&mut self, stmt: &ByDefStmt) -> Result<StmtResult, RuntimeError> {
        let predicate_name = stmt.fact.predicate.to_string();
        if matches!(predicate_name.as_str(), INJECTIVE | SURJECTIVE | BIJECTIVE) {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by def: `{}` is a builtin predicate; write the fact directly to verify its builtin definition",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        if self
            .get_abstract_prop_definition_by_name(&predicate_name)
            .is_some()
        {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by def: `{}` is an abstract_prop and has no concrete definition body",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        let definition = self
            .get_active_prop_definition_by_name(&predicate_name)
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by def: concrete prop definition `{}` was not found",
                        predicate_name
                    ),
                    None,
                    vec![],
                )
            })?;
        if definition.iff_facts.is_empty() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by def: concrete prop `{}` has no definition clauses",
                    predicate_name
                ),
                None,
                vec![],
            ));
        }
        let expected_argument_count = definition.params_def_with_type.number_of_params();
        if stmt.fact.body.len() != expected_argument_count {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by def `{}`: expected {} argument(s), got {}",
                    predicate_name,
                    expected_argument_count,
                    stmt.fact.body.len()
                ),
                None,
                vec![],
            ));
        }

        let verify_state = VerifyState::new(0, false);
        let (parameter_type_check, clause_checks) = self
            .run_in_local_env(|rt| {
                rt.verify_normal_atomic_fact_definition_clauses(
                    &stmt.fact,
                    &definition,
                    &verify_state,
                )
            })
            .map_err(|error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by def `{}`: failed while checking the concrete definition",
                        predicate_name
                    ),
                    Some(error),
                    vec![],
                )
            })?;

        if parameter_type_check.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by def `{}`: could not verify argument parameter types",
                    predicate_name
                ),
                None,
                vec![parameter_type_check],
            ));
        }

        let mut instantiated_clauses = Vec::with_capacity(clause_checks.len());
        let mut inside_results = Vec::with_capacity(clause_checks.len() + 1);
        inside_results.push(parameter_type_check);
        for (clause_index, (instantiated_clause, clause_result)) in
            clause_checks.into_iter().enumerate()
        {
            if clause_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by def `{}`: definition clause {} is not verified: `{}`",
                        predicate_name,
                        clause_index + 1,
                        instantiated_clause
                    ),
                    None,
                    vec![clause_result],
                ));
            }
            instantiated_clauses.push(instantiated_clause.to_string());
            inside_results.push(clause_result);
        }

        let target_fact: Fact = stmt.fact.clone().into();
        let trust_summary = self.proof_trust_summary_from_stmt_results(&inside_results);
        let infer_result = self.run_in_local_env_and_commit(|rt| {
            rt.store_trusted_fact_and_infer_with_reason_and_trust(
                target_fact.clone(),
                InferReason::Other(ByDefStmt::store_reason().to_string()),
                trust_summary,
            )
        })?;

        let by_verification = ByDefinitionVerificationResult::new(
            predicate_name,
            stmt.fact.body.iter().map(|arg| arg.to_string()).collect(),
            instantiated_clauses,
            target_fact.to_string(),
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            by_verification.into(),
        )
        .into())
    }

    pub(crate) fn exec_by_def_stmt_affect_environment_only(
        &mut self,
        stmt: &ByDefStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let target_fact: Fact = stmt.fact.clone().into();
        let infer_result = self.run_in_local_env_and_commit(|rt| {
            rt.store_trusted_fact_and_infer_with_reason(
                target_fact.clone(),
                InferReason::Other(ByDefStmt::store_reason().to_string()),
            )
        })?;
        let by_verification = ByDefinitionVerificationResult::new(
            stmt.fact.predicate.to_string(),
            stmt.fact.body.iter().map(|arg| arg.to_string()).collect(),
            vec![],
            target_fact.to_string(),
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            vec![],
            by_verification.into(),
        )
        .into())
    }
}
