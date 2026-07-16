use crate::prelude::*;
use std::collections::HashMap;

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
        self.verify_have_fn_by_induc_measure_lower_bound(stmt)?;
        self.register_have_fn_by_induc_recursive_fn(stmt)?;
        self.verify_have_fn_by_induc_case_list(stmt, &stmt.cases)
    }

    fn exec_have_fn_by_induc_verify_well_definedness(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.store_free_param_or_identifier_name(&stmt.name, ParamObjType::Identifier)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            let fn_set = rt
                .fn_set_from_fn_set_clause(&stmt.fn_set_clause)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            rt.verify_obj_well_defined_and_store_cache(
                &Obj::from(fn_set),
                &VerifyState::new(0, false),
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            rt.define_have_fn_by_induc_current_params_and_domain(stmt)?;
            rt.verify_obj_well_defined_and_store_cache(&stmt.measure, &VerifyState::new(0, false))
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            rt.verify_obj_well_defined_and_store_cache(
                &stmt.lower_bound,
                &VerifyState::new(0, false),
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

    fn verify_have_fn_by_induc_measure_lower_bound(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.measure, &VerifyState::new(0, false))
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        self.verify_obj_well_defined_and_store_cache(
            &stmt.lower_bound,
            &VerifyState::new(0, false),
        )
        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let lower_fact: AtomicFact = GreaterEqualFact::new(
            stmt.measure.clone(),
            stmt.lower_bound.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let result = self
            .verify_atomic_fact(&lower_fact, &VerifyState::new(0, false))
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
        self.store_free_param_or_identifier_name(&stmt.name, ParamObjType::Identifier)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let param_names = stmt.param_names();
        let generated_names = self.generate_random_unused_names(param_names.len());
        let mut param_to_generated_obj: HashMap<String, Obj> = HashMap::new();
        for (param_name, generated_name) in param_names.iter().zip(generated_names.iter()) {
            param_to_generated_obj.insert(
                param_name.clone(),
                obj_for_bound_param_in_scope(generated_name.clone(), ParamObjType::FnSet),
            );
        }

        let mut generated_groups: Vec<ParamGroupWithSet> =
            Vec::with_capacity(stmt.fn_set_clause.params_def_with_set.len());
        let mut generated_index = 0;
        for group in stmt.fn_set_clause.params_def_with_set.iter() {
            let mut generated_group_names = Vec::with_capacity(group.params.len());
            for _ in group.params.iter() {
                generated_group_names.push(generated_names[generated_index].clone());
                generated_index += 1;
            }
            let generated_set = self
                .inst_obj(
                    group.set_obj(),
                    &param_to_generated_obj,
                    ParamObjType::FnSet,
                )
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            generated_groups.push(ParamGroupWithSet::new(generated_group_names, generated_set));
        }

        let mut recursive_dom_facts: Vec<OrAndChainAtomicFact> =
            Vec::with_capacity(stmt.fn_set_clause.dom_facts.len() + 2);
        for dom_fact in stmt.fn_set_clause.dom_facts.iter() {
            recursive_dom_facts.push(
                self.inst_or_and_chain_atomic_fact(
                    dom_fact,
                    &param_to_generated_obj,
                    ParamObjType::FnSet,
                    None,
                )
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?,
            );
        }

        let generated_measure = self
            .inst_obj(&stmt.measure, &param_to_generated_obj, ParamObjType::FnSet)
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

        let generated_ret_set = self
            .inst_obj(
                &stmt.fn_set_clause.ret_set,
                &param_to_generated_obj,
                ParamObjType::FnSet,
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        let recursive_fn_set = self
            .new_fn_set(generated_groups, recursive_dom_facts, generated_ret_set)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let function_in_function_set_fact: Fact = InFact::new(
            Identifier::new(stmt.name.clone()).into(),
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
        self.verify_fact_return_err_if_not_true(&coverage, &VerifyState::new(0, false))
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
        let verify_state = VerifyState::new(0, false);
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
                if !self
                    .have_fn_by_induc_cases_are_disjoint(&cases[i].case_fact, &cases[j].case_fact)?
                {
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

    fn have_fn_by_induc_cases_are_disjoint(
        &mut self,
        left: &AndChainAtomicFact,
        right: &AndChainAtomicFact,
    ) -> Result<bool, RuntimeError> {
        if self.have_fn_by_induc_case_implies_not_other(left, right)? {
            return Ok(true);
        }
        self.have_fn_by_induc_case_implies_not_other(right, left)
    }

    fn have_fn_by_induc_case_implies_not_other(
        &mut self,
        assumed: &AndChainAtomicFact,
        other: &AndChainAtomicFact,
    ) -> Result<bool, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.verify_well_defined_and_store_and_infer_with_default_verify_state(Fact::from(
                assumed.clone(),
            ))?;

            for atom in flatten_have_fn_by_induc_and_chain_to_atomic_facts(other) {
                let reversed = atom.make_reversed();
                let result = rt.verify_atomic_fact(&reversed, &VerifyState::new(0, false))?;
                if result.is_true() {
                    return Ok(true);
                }
            }
            Ok(false)
        })
    }

    pub fn exec_have_fn_by_induc_stmt(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_fn_by_induc(stmt)
    }
}

fn flatten_have_fn_by_induc_and_chain_to_atomic_facts(c: &AndChainAtomicFact) -> Vec<AtomicFact> {
    match c {
        AndChainAtomicFact::AtomicFact(a) => vec![a.clone()],
        AndChainAtomicFact::AndFact(af) => af.facts.clone(),
        AndChainAtomicFact::ChainFact(cf) => cf.facts().unwrap(),
    }
}
