use crate::prelude::*;

use super::exec_have_fn_equal_shared::case_conditions_are_disjoint;

impl Runtime {
    pub fn exec_have_fn_by_induc(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_fn_by_induc_verify_well_definedness(stmt)?;
        let inside_results = self.exec_have_fn_by_induc_verify_process(stmt)?;
        let infer_result = self.exec_have_fn_by_induc_affect_environment(stmt)?;

        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results)).into())
    }

    pub(crate) fn exec_have_fn_by_induc_affect_environment(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<InferResult, RuntimeError> {
        let flat = stmt.to_have_fn_equal_case_by_case_stmt();
        let fn_set_stored = self
            .fn_set_from_fn_set_clause(&flat.fn_set_clause)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        self.store_have_fn_equal_case_by_case_stmt_facts(&flat, &fn_set_stored)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))
    }

    pub(crate) fn exec_have_fn_by_induc_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_have_fn_by_induc_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn have_fn_by_induc_err(stmt: &HaveFnByInducStmt, cause: RuntimeError) -> RuntimeError {
        exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), cause)
    }

    fn exec_have_fn_by_induc_verify_process(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.run_in_local_env(|rt| rt.exec_have_fn_by_induc_verify_process_body(stmt))?;
        Ok(vec![])
    }

    fn exec_have_fn_by_induc_verify_process_body(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        self.define_have_fn_by_induc_current_params_and_domain(stmt)?;
        self.verify_have_fn_by_induc_integer_measure_and_lower_bound(stmt)?;
        self.register_have_fn_by_induc_recursive_fn(stmt)?;
        self.verify_have_fn_by_induc_case_list(stmt, &stmt.cases)
    }

    /// Mathematical contract: an inductive function declaration has a fresh
    /// name, a meaningful function signature, and well-defined measure and
    /// lower-bound expressions under its parameter domain. Integrality,
    /// descent, cases, and return values are checked in the proof phase.
    fn exec_have_fn_by_induc_verify_well_definedness(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.store_parameter_binding(&stmt.symbol_binding, ParamObjType::Identifier)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            let fn_set = rt
                .fn_set_from_fn_set_clause(&stmt.fn_set_clause)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            rt.verify_obj_well_defined_and_store_cache(
                &Obj::from(fn_set),
                &UseContextVerifyState::new(0, false),
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            rt.define_have_fn_by_induc_current_params_and_domain(stmt)?;
            rt.verify_obj_well_defined_and_store_cache(
                &stmt.measure,
                &UseContextVerifyState::new(0, false),
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            rt.verify_obj_well_defined_and_store_cache(
                &stmt.lower_bound,
                &UseContextVerifyState::new(0, false),
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            Ok(())
        })
    }

    fn define_have_fn_by_induc_current_params_and_domain(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        for param_def_with_set in stmt.fn_set_clause.params_def_with_set.iter() {
            self.define_params_with_set(param_def_with_set)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        }

        for dom_fact in stmt.fn_set_clause.dom_facts.iter() {
            self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                dom_fact.clone(),
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        }

        Ok(())
    }

    fn verify_have_fn_by_induc_integer_measure_and_lower_bound(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &stmt.measure,
            &UseContextVerifyState::new(0, false),
        )
        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        self.verify_obj_well_defined_and_store_cache(
            &stmt.lower_bound,
            &UseContextVerifyState::new(0, false),
        )
        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        for (label, obj) in [
            ("measure", &stmt.measure),
            ("lower bound", &stmt.lower_bound),
        ] {
            let integer_fact: AtomicFact =
                InFact::new(obj.clone(), StandardSet::Z.into(), stmt.line_file.clone()).into();
            let result = self
                .verify_atomic_fact(&integer_fact, &UseContextVerifyState::new(0, false))
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "have fn by induc: failed to verify that the {} is integer-valued",
                            label
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            if result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "have fn by induc: the {} must be provably integer-valued; failed to prove `{}`",
                        label, integer_fact
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let lower_fact: AtomicFact = GreaterEqualFact::new(
            stmt.measure.clone(),
            stmt.lower_bound.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let result = self
            .verify_atomic_fact(&lower_fact, &UseContextVerifyState::new(0, false))
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        if result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "have_fn_by_induc: failed to prove decreasing measure lower bound `{}`",
                    lower_fact
                ),
                None,
                vec![],
            ));
        }
        Ok(())
    }

    fn register_have_fn_by_induc_recursive_fn(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        self.store_parameter_binding(&stmt.symbol_binding, ParamObjType::Identifier)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let source_bindings = stmt
            .fn_set_clause
            .params_def_with_set
            .collect_param_bindings();
        let (_, param_to_generated_obj) =
            self.fresh_binder_retag_plan_for_bindings(&source_bindings, ParamObjType::FnSet);

        let generated_body = self
            .alpha_rename_fn_set_body(
                &FnSetBody::new(
                    stmt.fn_set_clause.params_def_with_set.clone(),
                    stmt.fn_set_clause.dom_facts.clone(),
                    stmt.fn_set_clause.ret_set.clone(),
                ),
                &param_to_generated_obj,
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        let generated_groups = generated_body.params_def_with_set;
        let mut recursive_dom_facts = generated_body.dom_facts;

        let generated_measure = self
            .inst_obj(
                &stmt.measure,
                &param_to_generated_obj,
                ParamObjType::AlphaRename,
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        recursive_dom_facts.push(OrAndChainAtomicFact::AtomicFact(
            LessFact::new(
                generated_measure.clone(),
                stmt.measure.clone(),
                stmt.line_file.clone(),
            )
            .into(),
        ));
        recursive_dom_facts.push(OrAndChainAtomicFact::AtomicFact(
            GreaterEqualFact::new(
                generated_measure,
                stmt.lower_bound.clone(),
                stmt.line_file.clone(),
            )
            .into(),
        ));

        let generated_ret_set = *generated_body.ret_set;
        let recursive_fn_set = self
            .new_fn_set(generated_groups, recursive_dom_facts, generated_ret_set)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let function_in_function_set_fact: Fact = InFact::new(
            self.declared_identifier_obj(&stmt.name),
            recursive_fn_set.into(),
            stmt.line_file.clone(),
        )
        .into();

        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
            function_in_function_set_fact,
        )
        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        Ok(())
    }

    fn verify_have_fn_by_induc_case_list(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
    ) -> Result<(), RuntimeError> {
        if cases.is_empty() {
            return Err(short_exec_error(
                stmt.clone().into(),
                "have_fn_by_induc: case list must not be empty".to_string(),
                None,
                vec![],
            ));
        }

        let coverage_cases: Vec<AndChainAtomicFact> =
            cases.iter().map(|c| c.case_fact.clone()).collect();
        let coverage: Fact = OrFact::new(coverage_cases, stmt.line_file.clone()).into();
        self.verify_fact_return_err_if_not_true(&coverage, &UseContextVerifyState::new(0, false))
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "have_fn_by_induc: cases do not cover all situations".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        self.verify_have_fn_by_induc_cases_mutually_exclusive(stmt, cases)?;

        for case in cases.iter() {
            self.run_in_local_env(|rt| {
                rt.verify_well_defined_and_store_and_infer_with_default_verify_state(Fact::from(
                    case.case_fact.clone(),
                ))
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

                match &case.body {
                    HaveFnByInducCaseBody::EqualTo(equal_to) => {
                        rt.verify_have_fn_by_induc_equal_to(stmt, equal_to)
                    }
                    HaveFnByInducCaseBody::NestedCases(nested) => {
                        rt.verify_have_fn_by_induc_case_list(stmt, nested)
                    }
                }
            })?;
        }

        Ok(())
    }

    fn verify_have_fn_by_induc_equal_to(
        &mut self,
        stmt: &HaveFnByInducStmt,
        equal_to: &Obj,
    ) -> Result<(), RuntimeError> {
        let verify_state = UseContextVerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(equal_to, &verify_state)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let equal_to_in_ret_set_atomic_fact: AtomicFact = InFact::new(
            equal_to.clone(),
            stmt.fn_set_clause.ret_set.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        if verify_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "have_fn_by_induc: {} is not in return set {}",
                    equal_to, stmt.fn_set_clause.ret_set
                ),
                None,
                vec![],
            ));
        }
        Ok(())
    }

    fn verify_have_fn_by_induc_cases_mutually_exclusive(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
    ) -> Result<(), RuntimeError> {
        for i in 0..cases.len() {
            for j in (i + 1)..cases.len() {
                if !case_conditions_are_disjoint(self, &cases[i].case_fact, &cases[j].case_fact)? {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "have_fn_by_induc: cases overlap or cannot be proved mutually exclusive: `{}` and `{}`",
                            cases[i].case_fact, cases[j].case_fact
                        ),
                        None,
                        vec![],
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn exec_have_fn_by_induc_stmt(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_fn_by_induc(stmt)
    }
}
