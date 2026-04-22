use crate::prelude::*;
use crate::stmt::definition_stmt::induc_obj_plus_offset;

use super::exec_have_fn_equal_shared::inst_have_fn_forall_fact_for_store;

impl Runtime {
    pub fn exec_have_fn_by_induc(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.exec_have_fn_by_induc_verify_process(stmt))?;

        let infer_result = self.exec_have_fn_by_induc_store_process(stmt)?;

        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![])).into())
    }

    fn exec_have_fn_by_induc_verify_process(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        for special_case_equal_to in stmt.special_cases_equal_tos.iter() {
            self.verify_obj_well_defined_and_store_cache(
                special_case_equal_to,
                &VerifyState::new(0, false),
            )?;
        }

        self.run_in_local_env(|rt| rt.exec_have_fn_by_induc_verify_last_case(stmt))?;

        Ok(())
    }

    fn have_fn_by_induc_err(stmt: &HaveFnByInducStmt, cause: RuntimeError) -> RuntimeError {
        RuntimeError::ExecStmtError({
            let st: Stmt = stmt.clone().into();
            let lf = st.line_file();
            RuntimeErrorStruct::new(Some(st), String::new(), lf, Some(cause), vec![])
        })
    }

    // have fn by induc from 0: f(x Z: x >= 0) R: case 0: … case 1: …
    // Registers stmt.name in a new FnSet whose domain matches special-case indices.
    fn have_fn_by_induc_verify_last_case_register_fn(
        &mut self,
        stmt: &HaveFnByInducStmt,
        param_name: &str,
    ) -> Result<(), RuntimeError> {
        self.store_free_param_or_identifier_name(&stmt.name, ParamObjType::Identifier)?;

        let random_param = self.generate_random_unused_name();

        let param_minus_n: Obj = Sub::new(
            Identifier::new(param_name.to_string()).into(),
            stmt.special_cases_equal_tos.len().into(),
        )
        .into();

        let dom_facts: Vec<OrAndChainAtomicFact> = vec![
            GreaterEqualFact::new(
                obj_for_bound_param_in_scope(random_param.clone(), ParamObjType::FnSet),
                param_minus_n,
                stmt.line_file.clone(),
            )
            .into(),
            LessFact::new(
                obj_for_bound_param_in_scope(random_param.clone(), ParamObjType::FnSet),
                Identifier::new(param_name.to_string()).into(),
                stmt.line_file.clone(),
            )
            .into(),
        ];

        let fn_set = self.new_fn_set(
            vec![ParamGroupWithSet::new(
                vec![random_param.clone()],
                StandardSet::Z.into(),
            )],
            dom_facts,
            stmt.ret_set.clone(),
        )?;

        let function_in_function_set_fact: Fact = InFact::new(
            Identifier::new(stmt.name.clone()).into(),
            fn_set.into(),
            stmt.line_file.clone(),
        )
        .into();

        self.store_fact_without_well_defined_verified_and_infer(function_in_function_set_fact)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        Ok(())
    }

    fn have_fn_by_induc_verify_one_equal_to_well_defined(
        &mut self,
        stmt: &HaveFnByInducStmt,
        equal_to: &Obj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(equal_to, verify_state)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let equal_to_in_ret_set_atomic_fact: AtomicFact = InFact::new(
            equal_to.clone(),
            stmt.ret_set.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, verify_state)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        if verify_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "have_fn_by_induc: {} is not in return set {}",
                    equal_to, stmt.ret_set
                ),
                None,
                vec![],
            ));
        }
        Ok(())
    }

    // have fn by induc from 0: f(x Z: x >= 0) R:
    // case 0: 1
    // case 1: 2
    // case >= 2:
    //      case x % 2 = 0: f(x - 1)
    //      case x % 2 = 2: f(x - 1) + f(x - 2)
    fn exec_have_fn_by_induc_verify_last_case(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        let n = stmt.special_cases_equal_tos.len();
        let line_file = stmt.line_file.clone();

        let param_name_str = stmt.param.clone();

        let left_id: Obj =
            obj_for_bound_param_in_scope(param_name_str.clone(), ParamObjType::Induc);

        self.store_free_param_or_identifier_name(&param_name_str, ParamObjType::Induc)?;

        self.define_parameter_by_binding_param_type(
            &param_name_str,
            &ParamType::Obj(StandardSet::Z.into()),
            ParamObjType::Induc,
        )?;

        let param_larger_than_induc_plus_offset: AndChainAtomicFact = GreaterEqualFact::new(
            left_id,
            induc_obj_plus_offset(&stmt.induc_from, n),
            line_file.clone(),
        )
        .into();

        self.store_fact_without_well_defined_verified_and_infer(
            param_larger_than_induc_plus_offset.into(),
        )
        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        // Induction step needs f(x-1)..f(x-n); cache alone skips fn membership, so store FnObj and in ret_set.
        for i in 1..=n {
            let arg: Obj = Sub::new(
                obj_for_bound_param_in_scope(param_name_str.clone(), ParamObjType::Induc),
                i.into(),
            )
            .into();
            let fn_obj: Obj = FnObj::new(
                FnObjHead::Identifier(Identifier::new(stmt.name.clone())),
                vec![vec![Box::new(arg.clone())]],
            )
            .into();
            self.store_well_defined_obj_cache(&fn_obj);
            let fn_in_ret: Fact =
                InFact::new(fn_obj, stmt.ret_set.clone(), line_file.clone()).into();
            self.store_fact_without_well_defined_verified_and_infer(fn_in_ret)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        }

        self.have_fn_by_induc_verify_last_case_register_fn(stmt, &param_name_str)?;

        match &stmt.last_case {
            HaveFnByInducLastCase::EqualTo(eq) => {
                self.have_fn_by_induc_verify_one_equal_to_well_defined(stmt, eq, &verify_state)?;
            }
            HaveFnByInducLastCase::NestedCases(last_pairs) if !last_pairs.is_empty() => {
                let coverage_cases: Vec<AndChainAtomicFact> =
                    last_pairs.iter().map(|c| c.case_fact.clone()).collect();
                let coverage: Fact = OrFact::new(coverage_cases, line_file.clone()).into();
                self.verify_fact_return_err_if_not_true(&coverage, &verify_state)
                    .map_err(|e| {
                        short_exec_error(
                            stmt.clone().into(),
                            "have_fn_by_induc: nested last cases do not cover all situations"
                                .to_string(),
                            Some(e),
                            vec![],
                        )
                    })?;

                for nested in last_pairs.iter() {
                    self.run_in_local_env(|rt| {
                        rt.store_fact_without_well_defined_verified_and_infer(
                            nested.case_fact.clone().into(),
                        )
                        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
                        rt.have_fn_by_induc_verify_one_equal_to_well_defined(
                            stmt,
                            &nested.equal_to,
                            &verify_state,
                        )
                    })?;
                }
            }
            HaveFnByInducLastCase::NestedCases(_) => {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    "have_fn_by_induc: nested last case list must not be empty".to_string(),
                    None,
                    vec![],
                ));
            }
        }

        Ok(())
    }

    // When store_*_and_infer yields an empty chain, record the stored fact for infer_facts display.
    fn merge_store_infer_with_fallback_fact(
        infer_result: &mut InferResult,
        store_infer: InferResult,
        fallback_fact: &Fact,
    ) {
        let empty = store_infer.is_empty();
        infer_result.new_infer_result_inside(store_infer);
        if empty {
            infer_result.new_fact(fallback_fact);
        }
    }

    fn exec_have_fn_by_induc_store_process(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<InferResult, RuntimeError> {
        // stmt.induc_from 得是 Z
        let in_fact: AtomicFact = InFact::new(
            stmt.induc_from.clone(),
            StandardSet::Z.into(),
            stmt.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_atomic_fact(&in_fact, &VerifyState::new(0, false))
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        if verify_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                "have_fn_by_induc: induc_from is not in Z".to_string(),
                None,
                vec![],
            ));
        }

        let mut infer_result = InferResult::new();
        let fs = self.fn_set_from_fn_set_clause(&stmt.fn_user_fn_set_clause())?;

        let bind_infer = self.define_parameter_by_binding_param_type(
            &stmt.name,
            &ParamType::Obj(fs.clone().into()),
            ParamObjType::Identifier,
        )?;
        let bind_fact: Fact = InFact::new(
            Identifier::new(stmt.name.clone()).into(),
            fs.clone().into(),
            stmt.line_file.clone(),
        )
        .into();
        Self::merge_store_infer_with_fallback_fact(&mut infer_result, bind_infer, &bind_fact);

        // Special cases: stmt.name(induc_from + i) = equal_to[i]
        for i in 0..stmt.special_cases_equal_tos.len() {
            let raw_arg = if i == 0 {
                stmt.induc_from.clone()
            } else {
                Add::new(stmt.induc_from.clone(), i.into()).into()
            };
            // Fold numeric adds so we store f(1) not f(0 + 1)
            let arg = raw_arg.replace_with_numeric_result_if_can_be_calculated().0;

            let equal_to = &stmt.special_cases_equal_tos[i];

            let fn_obj: Obj = FnObj::new(
                FnObjHead::Identifier(Identifier::new(stmt.name.clone())),
                vec![vec![Box::new(arg.clone())]],
            )
            .into();

            let equal_fact: Fact =
                EqualFact::new(fn_obj.clone(), equal_to.clone(), stmt.line_file.clone()).into();

            let result = self
                .store_fact_without_well_defined_verified_and_infer(equal_fact.clone())
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

            Self::merge_store_infer_with_fallback_fact(&mut infer_result, result, &equal_fact);
        }

        match &stmt.last_case {
            HaveFnByInducLastCase::EqualTo(eq) => {
                let param_name = stmt.param.clone();
                let param_def = vec![ParamGroupWithParamType::new(
                    vec![param_name.clone()],
                    ParamType::Obj(StandardSet::Z.into()),
                )];

                let mut dom: Vec<Fact> = stmt.forall_fn_base_dom_exist_or_facts();

                let induc_plus_n =
                    induc_obj_plus_offset(&stmt.induc_from, stmt.special_cases_equal_tos.len())
                        .replace_with_numeric_result_if_can_be_calculated()
                        .0;
                dom.push(
                    GreaterEqualFact::new(
                        obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Forall),
                        induc_plus_n,
                        stmt.line_file.clone(),
                    )
                    .into(),
                );

                let forall_fact_raw = ForallFact::new(
                    ParamDefWithType::new(param_def),
                    dom,
                    vec![EqualFact::new(
                        FnObj::new(
                            FnObjHead::Identifier(Identifier::new(stmt.name.clone())),
                            vec![vec![Box::new(obj_for_bound_param_in_scope(
                                param_name.clone(),
                                ParamObjType::Forall,
                            ))]],
                        )
                        .into(),
                        eq.clone(),
                        stmt.line_file.clone(),
                    )
                    .into()],
                    stmt.line_file.clone(),
                );

                let forall_fact = inst_have_fn_forall_fact_for_store(self, forall_fact_raw)
                    .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

                let result = self
                    .store_fact_without_well_defined_verified_and_infer(forall_fact.clone())
                    .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
                Self::merge_store_infer_with_fallback_fact(&mut infer_result, result, &forall_fact);
            }
            HaveFnByInducLastCase::NestedCases(last_pairs) => {
                for nested in last_pairs.iter() {
                    let param_name = stmt.param.clone();
                    let param_def = vec![ParamGroupWithParamType::new(
                        vec![param_name.clone()],
                        ParamType::Obj(StandardSet::Z.into()),
                    )];
                    let eq = nested.equal_to.clone();

                    let mut dom: Vec<Fact> = stmt.forall_fn_base_dom_exist_or_facts();

                    let induc_plus_n =
                        induc_obj_plus_offset(&stmt.induc_from, stmt.special_cases_equal_tos.len())
                            .replace_with_numeric_result_if_can_be_calculated()
                            .0;
                    dom.push(
                        GreaterEqualFact::new(
                            obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Forall),
                            induc_plus_n,
                            stmt.line_file.clone(),
                        )
                        .into(),
                    );

                    let c: AndChainAtomicFact = nested.case_fact.clone();
                    dom.push(c.into());

                    let forall_fact_raw = ForallFact::new(
                        ParamDefWithType::new(param_def),
                        dom,
                        vec![EqualFact::new(
                            FnObj::new(
                                FnObjHead::Identifier(Identifier::new(stmt.name.clone())),
                                vec![vec![Box::new(obj_for_bound_param_in_scope(
                                    param_name.clone(),
                                    ParamObjType::Forall,
                                ))]],
                            )
                            .into(),
                            eq.clone(),
                            stmt.line_file.clone(),
                        )
                        .into()],
                        stmt.line_file.clone(),
                    );

                    let forall_fact = inst_have_fn_forall_fact_for_store(self, forall_fact_raw)
                        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

                    let result = self
                        .store_fact_without_well_defined_verified_and_infer(forall_fact.clone())
                        .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
                    Self::merge_store_infer_with_fallback_fact(
                        &mut infer_result,
                        result,
                        &forall_fact,
                    );
                }
            }
        }

        Ok(infer_result)
    }

    pub fn exec_have_fn_by_induc_stmt(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_fn_by_induc(stmt)
    }
}
