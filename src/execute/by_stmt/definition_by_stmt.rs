use crate::prelude::*;

impl Runtime {
    pub fn exec_by_def_stmt(&mut self, stmt: &ByDefStmt) -> Result<StmtResult, RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        if explicit_builtin_definition_supported(&stmt.fact) {
            self.verify_atomic_fact_well_defined(&stmt.fact, &verify_state)?;
            let result = self
                .verify_explicit_builtin_definition(&stmt.fact, &verify_state)?
                .unwrap_or_else(|| StmtUnknown::new().into());
            if result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by def `{}`: builtin definition requirements are not verified",
                        stmt.fact.key()
                    ),
                    None,
                    vec![result],
                ));
            }
            return self.finish_by_def_stmt(
                stmt,
                stmt.fact.key(),
                vec![format!("builtin definition of `{}`", stmt.fact)],
                vec![result],
            );
        }

        let AtomicFact::NormalAtomicFact(normal_fact) = &stmt.fact else {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by def: `{}` has no supported builtin definition",
                    stmt.fact
                ),
                None,
                vec![],
            ));
        };
        let predicate_name = normal_fact.predicate.to_string();
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
        if normal_fact.body.len() != expected_argument_count {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by def `{}`: expected {} argument(s), got {}",
                    predicate_name,
                    expected_argument_count,
                    normal_fact.body.len()
                ),
                None,
                vec![],
            ));
        }
        self.verify_atomic_fact_well_defined(&stmt.fact, &verify_state)?;

        let (parameter_type_check, clause_checks) = self
            .run_in_local_env(|rt| {
                rt.verify_normal_atomic_fact_definition_clauses(
                    normal_fact,
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

        self.finish_by_def_stmt(stmt, predicate_name, instantiated_clauses, inside_results)
    }

    pub(crate) fn exec_by_def_stmt_affect_environment_only(
        &mut self,
        stmt: &ByDefStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.finish_by_def_stmt(stmt, stmt.fact.key(), vec![], vec![])
    }

    fn verify_explicit_builtin_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        match fact {
            AtomicFact::SubsetFact(_) | AtomicFact::SupersetFact(_) => {
                self.verify_atomic_fact_using_builtin_or_prop_definition(fact, verify_state)
            }
            AtomicFact::FnEqualInFact(fact) => Ok(Some(
                self.verify_fn_equal_in_fact_with_builtin_rules(fact, verify_state)?,
            )),
            AtomicFact::FnEqualFact(fact) => Ok(Some(
                self.verify_fn_equal_fact_with_builtin_rules(fact, verify_state)?,
            )),
            AtomicFact::NormalAtomicFact(fact) => match fact.predicate.to_string().as_str() {
                PRIME => self.verify_prime_fact_by_definition(&fact.clone().into(), verify_state),
                INJECTIVE | SURJECTIVE | BIJECTIVE => {
                    self.verify_builtin_function_property_by_definition(fact, verify_state)
                }
                PROPER_SUBSET | PROPER_SUPERSET => self
                    .verify_builtin_proper_set_relation_by_definition(
                        &fact.clone().into(),
                        verify_state,
                    ),
                _ => Ok(None),
            },
            _ => Ok(None),
        }
    }

    fn finish_by_def_stmt(
        &mut self,
        stmt: &ByDefStmt,
        definition_name: String,
        definition_clauses: Vec<String>,
        inside_results: Vec<StmtResult>,
    ) -> Result<StmtResult, RuntimeError> {
        let target_fact: Fact = stmt.fact.clone().into();
        let infer_result = self.run_in_local_env_and_commit(|rt| {
            rt.store_trusted_fact_and_infer_with_reason(
                target_fact.clone(),
                InferReason::Other(ByDefStmt::store_reason().to_string()),
            )
        })?;
        let by_verification = ByDefinitionVerificationResult::new(
            definition_name,
            stmt.fact.args().iter().map(|arg| arg.to_string()).collect(),
            definition_clauses,
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
}

fn explicit_builtin_definition_supported(fact: &AtomicFact) -> bool {
    match fact {
        AtomicFact::SubsetFact(_)
        | AtomicFact::SupersetFact(_)
        | AtomicFact::FnEqualInFact(_)
        | AtomicFact::FnEqualFact(_) => true,
        AtomicFact::NormalAtomicFact(fact) => matches!(
            fact.predicate.to_string().as_str(),
            PRIME | INJECTIVE | SURJECTIVE | BIJECTIVE | PROPER_SUBSET | PROPER_SUPERSET
        ),
        _ => false,
    }
}
