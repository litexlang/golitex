use crate::prelude::*;

impl Runtime {
    pub fn exec_def_strategy_stmt(
        &mut self,
        stmt: &DefStrategyStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let strategy_names = stmt.names.join(", ");
        self.verify_fact_well_defined(
            &Fact::ForallFact(stmt.forall_fact.clone()),
            &VerifyState::new(0, false),
        )
        .map_err(|e| {
            short_exec_error(
                stmt.clone().into(),
                "strategy: forall fact is not well defined".to_string(),
                Some(e),
                vec![],
            )
        })?;

        let body_exec_result: StmtResult = self.run_in_local_env(|rt| {
            rt.define_params_with_type(
                &stmt.forall_fact.params_def_with_type,
                false,
                ParamObjType::Forall,
            )
            .map_err(|define_params_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
            })?;

            for dom_fact in stmt.forall_fact.dom_facts.iter() {
                rt.verify_well_defined_and_store_and_infer_with_default_verify_state(
                    dom_fact.clone(),
                )?;
            }

            let mut inside_results = vec![];
            let proof_len = stmt.prove_process.len();
            for (proof_index, proof_stmt) in stmt.prove_process.iter().enumerate() {
                let result = rt.exec_stmt(proof_stmt)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(proof_stmt.clone()),
                            format!(
                                "strategy `{}` failed: proof step is unknown",
                                strategy_names
                            ),
                            proof_stmt.line_file(),
                            None,
                            vec![],
                            RuntimeErrorOutput::proof_step_unknown(
                                proof_stmt.clone(),
                                proof_index + 1,
                                proof_len,
                                &result,
                            ),
                        ),
                    )));
                }
                inside_results.push(result);
            }

            let then_count = stmt.forall_fact.then_facts.len();
            for (then_index, then_fact) in stmt.forall_fact.then_facts.iter().enumerate() {
                let mut result = rt.verify_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &VerifyState::new(0, false),
                )?;
                if result.is_unknown() {
                    let then_goal = then_fact.clone().to_fact();
                    result = result.wrap_unknown_for_fact(then_goal.clone());
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(then_goal.clone().into()),
                            format!(
                                "strategy `{}` failed: cannot prove then-clause",
                                strategy_names
                            ),
                            then_fact.line_file(),
                            None,
                            vec![],
                            RuntimeErrorOutput::then_clause_unknown(
                                then_goal,
                                then_index + 1,
                                then_count,
                                &result,
                            ),
                        ),
                    )));
                }
                inside_results.push(result);
            }

            Ok(
                NonFactualStmtSuccess::new(stmt.clone().into(), InferResult::new(), inside_results)
                    .into(),
            )
        })?;

        self.store_def_strategy(stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        let infer_result_after_store = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(Fact::ForallFact(
                stmt.forall_fact.clone(),
            ))?;

        for name in stmt.names.iter() {
            self.activate_strategy(stmt, name, stmt.clone().into())?;
        }

        Ok(body_exec_result.with_infers(infer_result_after_store))
    }

    pub fn exec_use_strategy_stmt(
        &mut self,
        stmt: &UseStrategyStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let strategy_name = stmt.name.to_string();
        let strategy = self
            .get_strategy_definition_by_name(&strategy_name)
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("use strategy: strategy `{}` is not defined", stmt.name),
                    None,
                    vec![],
                )
            })?;
        self.activate_strategy(&strategy, &strategy_name, stmt.clone().into())?;
        Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone().into()).into())
    }

    pub fn exec_stop_strategy_stmt(
        &mut self,
        stmt: &StopStrategyStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let strategy_name = stmt.name.to_string();
        let strategy = self
            .get_strategy_definition_by_name(&strategy_name)
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("stop strategy: strategy `{}` is not defined", stmt.name),
                    None,
                    vec![],
                )
            })?;
        let atomic_fact_key = strategy_then_atomic_fact_key(&strategy, stmt.clone().into())?;
        self.top_level_env()
            .stopped_strategy_stmts
            .insert(atomic_fact_key, strategy_name);
        Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone().into()).into())
    }

    fn activate_strategy(
        &mut self,
        strategy: &DefStrategyStmt,
        strategy_name: &str,
        caller_stmt: Stmt,
    ) -> Result<(), RuntimeError> {
        let atomic_fact_key = strategy_then_atomic_fact_key(strategy, caller_stmt)?;
        let env = self.top_level_env();
        env.used_strategy_stmts
            .insert(atomic_fact_key.clone(), strategy_name.to_string());
        env.stopped_strategy_stmts.remove(&atomic_fact_key);
        Ok(())
    }
}

fn strategy_then_atomic_fact_key(
    strategy: &DefStrategyStmt,
    caller_stmt: Stmt,
) -> Result<(PropName, bool), RuntimeError> {
    let then_fact = strategy.forall_fact.then_facts.first().ok_or_else(|| {
        short_exec_error(
            caller_stmt.clone(),
            "strategy: missing then-clause fact".to_string(),
            None,
            vec![],
        )
    })?;

    match then_fact {
        ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
            Ok((atomic_fact.key(), atomic_fact.is_true()))
        }
        _ => Err(short_exec_error(
            caller_stmt,
            "strategy: then-clause fact must be atomic".to_string(),
            None,
            vec![],
        )),
    }
}
