use crate::prelude::*;
use crate::stmt::definition_stmt::induc_obj_plus_offset;

impl Runtime {
    pub fn exec_have_fn_by_induc(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.exec_have_fn_by_induc_verify_process(stmt))?;

        let result = self.exec_have_fn_by_induc_store_process(stmt)?;

        Ok(result)
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
        RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_new_with_stmt(
            Stmt::HaveFnByInducStmt(stmt.clone()),
            String::new(),
            Some(cause),
            vec![],
        ))
    }

    // have fn by induc from 0: f(x Z: x >= 0) R
    /// 先按 `stmt.fn_set` 声明归纳参数 `param_name`，再登记 `stmt.name` 属于一个形式参数为**新生成名字**的 `FnSet`，
    /// 其定义域满足 `random_param < param_name` 且 `random_param >= param_name - len(special_cases)`（与特例下标区间一致）。
    fn have_fn_by_induc_verify_last_case_register_fn(
        &mut self,
        stmt: &HaveFnByInducStmt,
        param_name: &str,
    ) -> Result<(), RuntimeError> {
        self.store_identifier_obj(&stmt.name)
            .map_err(RuntimeError::from)?;

        let random_param = self.generate_random_unused_names(1)[0].clone();

        let param_minus_n = Obj::Sub(Sub::new(
            Obj::Identifier(Identifier::new(param_name.to_string())),
            Obj::Number(Number::new(stmt.special_cases_equal_tos.len().to_string())),
        ));

        let dom_facts: Vec<OrAndChainAtomicFact> = vec![
            OrAndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                Obj::Identifier(Identifier::new(random_param.to_string())),
                param_minus_n,
                stmt.line_file.clone(),
            ))),
            OrAndChainAtomicFact::AtomicFact(AtomicFact::LessFact(LessFact::new(
                Obj::Identifier(Identifier::new(random_param.clone())),
                Obj::Identifier(Identifier::new(param_name.to_string())),
                stmt.line_file.clone(),
            ))),
        ];

        let restricted_fn_set = FnSet::new(
            vec![ParamGroupWithSet::new(
                vec![random_param.clone()],
                Obj::StandardSet(StandardSet::Z),
            )],
            dom_facts,
            stmt.fn_set.ret_set.as_ref().clone(),
        );

        let function_in_function_set_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            Obj::Identifier(Identifier::new(stmt.name.clone())),
            Obj::FnSet(restricted_fn_set),
            stmt.line_file.clone(),
        )));

        self.store_fact_without_well_defined_verified_and_infer(function_in_function_set_fact)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;

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

        let equal_to_in_ret_set_atomic_fact = AtomicFact::InFact(InFact::new(
            equal_to.clone(),
            stmt.fn_set.ret_set.as_ref().clone(),
            stmt.line_file.clone(),
        ));
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, verify_state)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        if verify_result.is_unknown() {
            return Err(RuntimeError::ExecStmtError(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    Stmt::HaveFnByInducStmt(stmt.clone()),
                    format!(
                        "have_fn_by_induc: {} is not in return set {}",
                        equal_to, stmt.fn_set.ret_set
                    ),
                    None,
                    vec![],
                ),
            ));
        }
        Ok(())
    }

    // have fn by induc from 0: f(x Z: x > = 0) R:
    // case x = 0: 1
    // case x = 1: 2
    // case x >= 2:
    //      case x % 2 = 0: f(x - 1)
    //      case x % 2 = 2: f(x - 1) + f(x - 2)
    fn exec_have_fn_by_induc_verify_last_case(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        let n = stmt.special_cases_equal_tos.len();
        let line_file = stmt.line_file.clone();

        let param_name_str = stmt.fn_set.get_params()[0].clone();
        let left_id = Obj::Identifier(Identifier::new(param_name_str.clone()));
        let param_larger_than_induc_plus_offset =
            AndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                left_id,
                induc_obj_plus_offset(&stmt.induc_from, n),
                line_file.clone(),
            )));

        self.store_fact_without_well_defined_verified_and_infer(
            param_larger_than_induc_plus_offset.to_fact(),
        )
        .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;

        // stmt.name(param_name_str - 1) ... stmt.name(param_name_str - n) all well-defined
        for i in 1..=n {
            let param_name = Obj::Sub(Sub::new(
                Obj::Identifier(Identifier::new(param_name_str.to_string())),
                Obj::Number(Number::new(i.to_string())),
            ));
            self.store_well_defined_obj_cache(&param_name)
        }

        self.have_fn_by_induc_verify_last_case_register_fn(stmt, &param_name_str)?;

        match &stmt.last_case {
            HaveFnByInducLastCase::EqualTo(eq) => {
                self.have_fn_by_induc_verify_one_equal_to_well_defined(stmt, eq, &verify_state)?;
            }
            HaveFnByInducLastCase::NestedCases(last_pairs) if !last_pairs.is_empty() => {
                let coverage_cases: Vec<AndChainAtomicFact> =
                    last_pairs.iter().map(|c| c.case_fact.clone()).collect();
                let coverage = Fact::OrFact(OrFact::new(coverage_cases, line_file.clone()));
                self.verify_fact_return_err_if_not_true(&coverage, &verify_state)
                    .map_err(|e| {
                        RuntimeError::ExecStmtError(
                            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                Stmt::HaveFnByInducStmt(stmt.clone()),
                                "have_fn_by_induc: nested last cases do not cover all situations"
                                    .to_string(),
                                Some(e),
                                vec![],
                            ),
                        )
                    })?;

                for nested in last_pairs.iter() {
                    self.run_in_local_env(|rt| {
                        rt.store_fact_without_well_defined_verified_and_infer(
                            nested.case_fact.to_fact(),
                        )
                        .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
                        rt.have_fn_by_induc_verify_one_equal_to_well_defined(
                            stmt,
                            &nested.equal_to,
                            &verify_state,
                        )
                    })?;
                }
            }
            HaveFnByInducLastCase::NestedCases(_) => {
                return Err(RuntimeError::ExecStmtError(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        Stmt::HaveFnByInducStmt(stmt.clone()),
                        "have_fn_by_induc: nested last case list must not be empty".to_string(),
                        None,
                        vec![],
                    ),
                ));
            }
        }

        Ok(())
    }

    fn exec_have_fn_by_induc_store_process(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        // 定义函数：stmt.name 是 符合 fn_set 的
        self.define_parameter_by_binding_param_type(
            &stmt.name,
            &ParamType::Obj(Obj::FnSet(stmt.fn_set.clone())),
        )?;

        // 遍历所有special case，让 stmt.name(induc_from + i) = equal_to[i]
        for i in 0..stmt.special_cases_equal_tos.len() {
            let arg = if i == 0 {
                stmt.induc_from.clone()
            } else {
                Obj::Add(Add::new(
                    stmt.induc_from.clone(),
                    Obj::Number(Number::new(i.to_string())),
                ))
            };

            let equal_to = &stmt.special_cases_equal_tos[i];

            let fn_obj = Obj::FnObj(FnObj {
                head: Box::new(Atom::Identifier(Identifier::new(stmt.name.clone()))),
                body: vec![vec![Box::new(arg.clone())]],
            });

            let equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                fn_obj.clone(),
                equal_to.clone(),
                stmt.line_file.clone(),
            )));

            self.store_fact_without_well_defined_verified_and_infer(equal_fact)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
        }

        match &stmt.last_case {
            HaveFnByInducLastCase::EqualTo(eq) => {
                let param_name = stmt.fn_set.get_params()[0].clone();
                let param_def = vec![ParamGroupWithParamType::new(
                    vec![param_name.clone()],
                    ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
                )];

                let mut dom: Vec<ExistOrAndChainAtomicFact> = stmt
                    .fn_set
                    .dom_facts
                    .clone()
                    .into_iter()
                    .map(|f| f.to_exist_or_and_chain_atomic_fact())
                    .collect();

                dom.push(ExistOrAndChainAtomicFact::AtomicFact(
                    AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                        Obj::Identifier(Identifier::new(param_name.clone())),
                        Obj::Number(Number::new(
                            induc_obj_plus_offset(
                                &stmt.induc_from,
                                stmt.special_cases_equal_tos.len(),
                            )
                            .to_string(),
                        )),
                        stmt.line_file.clone(),
                    )),
                ));

                let forall_fact = Fact::ForallFact(ForallFact::new(
                    param_def,
                    dom,
                    vec![ExistOrAndChainAtomicFact::AtomicFact(
                        AtomicFact::EqualFact(EqualFact::new(
                            Obj::FnObj(FnObj {
                                head: Box::new(Atom::Identifier(Identifier::new(
                                    stmt.name.clone(),
                                ))),
                                body: vec![vec![Box::new(Obj::Identifier(Identifier::new(
                                    param_name.clone(),
                                )))]],
                            }),
                            eq.clone(),
                            stmt.line_file.clone(),
                        )),
                    )],
                    stmt.line_file.clone(),
                ));

                self.store_fact_without_well_defined_verified_and_infer(forall_fact)
                    .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
            }
            HaveFnByInducLastCase::NestedCases(last_pairs) => {
                panic!("not implemented");
            }
        }

        panic!("not implemented");
    }
}
