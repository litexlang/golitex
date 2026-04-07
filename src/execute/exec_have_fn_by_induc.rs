use crate::prelude::*;
use crate::stmt::definition_stmt::induc_obj_plus_offset;

impl Runtime {
    pub fn exec_have_fn_by_induc(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.push_env();
        let result = self.exec_have_fn_by_induc_verify_process(stmt);
        self.pop_env();
        if let Err(e) = result {
            return Err(e);
        }

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

        self.push_env();
        let result = self.exec_have_fn_by_induc_verify_last_case(stmt);
        self.pop_env();
        if let Err(e) = result {
            return Err(e);
        }

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

    fn have_fn_by_induc_flatten_and_chain_to_atomic_facts(
        c: &AndChainAtomicFact,
    ) -> Result<Vec<AtomicFact>, RuntimeErrorStruct> {
        match c {
            AndChainAtomicFact::AtomicFact(a) => Ok(vec![a.clone()]),
            AndChainAtomicFact::AndFact(af) => Ok(af.facts.clone()),
            AndChainAtomicFact::ChainFact(cf) => cf.facts(),
        }
    }

    fn have_fn_by_induc_merge_step_and_when(
        step: AndChainAtomicFact,
        when: AndChainAtomicFact,
        line_file: LineFile,
    ) -> Result<AndChainAtomicFact, RuntimeErrorStruct> {
        let mut atoms = Self::have_fn_by_induc_flatten_and_chain_to_atomic_facts(&step)?;
        atoms.extend(Self::have_fn_by_induc_flatten_and_chain_to_atomic_facts(
            &when,
        )?);
        Ok(AndChainAtomicFact::AndFact(AndFact::new(atoms, line_file)))
    }

    // have fn by induc from 0: f(x Z: x >= 0) R
    /// 先按 `stmt.fn_set` 声明归纳参数 `param_name`，再登记 `stmt.name` 属于一个形式参数为**新生成名字**的 `FnSet`，
    /// 其定义域满足 `random_param < param_name` 且 `random_param >= param_name - len(special_cases)`（与特例下标区间一致）。
    fn have_fn_by_induc_verify_last_case_register_fn_and_store_dom(
        &mut self,
        stmt: &HaveFnByInducStmt,
        param_name: &str,
    ) -> Result<(), RuntimeError> {
        let n = stmt.special_cases_equal_tos.len();
        let line_file = stmt.line_file.clone();

        self.store_identifier_obj(&stmt.name)
            .map_err(RuntimeError::from)?;

        let random_param = self.generate_random_unused_names(1)[0].clone();

        let param_minus_n = Obj::Sub(Sub::new(
            Obj::Identifier(Identifier::new(param_name.to_string())),
            Obj::Number(Number::new(n.to_string())),
        ));

        let dom_facts: Vec<OrAndChainAtomicFact> = vec![
            OrAndChainAtomicFact::AtomicFact(AtomicFact::LessFact(LessFact::new(
                Obj::Identifier(Identifier::new(random_param.clone())),
                Obj::Identifier(Identifier::new(param_name.to_string())),
                line_file.clone(),
            ))),
            OrAndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                Obj::Identifier(Identifier::new(random_param.to_string())),
                param_minus_n,
                line_file.clone(),
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

        let function_identifier_obj = Obj::Identifier(Identifier::new(stmt.name.clone()));
        let function_in_function_set_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            function_identifier_obj,
            Obj::FnSet(restricted_fn_set),
            line_file.clone(),
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
        let step = AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            left_id,
            induc_obj_plus_offset(&stmt.induc_from, n),
            line_file.clone(),
        )));

        match (&stmt.last_case_equal_to, &stmt.last_case_cases) {
            (Some(eq), None) => {
                self.have_fn_by_induc_verify_last_case_register_fn_and_store_dom(
                    stmt,
                    &param_name_str,
                )?;
                self.store_fact_without_well_defined_verified_and_infer(step.to_fact())
                    .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
                self.have_fn_by_induc_verify_one_equal_to_well_defined(stmt, eq, &verify_state)?;
            }
            (None, Some(last_pairs)) if !last_pairs.is_empty() => {
                self.have_fn_by_induc_verify_last_case_register_fn_and_store_dom(
                    stmt,
                    &param_name_str,
                )?;
                self.store_fact_without_well_defined_verified_and_infer(step.to_fact())
                    .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;

                let coverage_cases: Vec<AndChainAtomicFact> =
                    last_pairs.iter().map(|(w, _)| w.clone()).collect();
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

                for (when, eq_to) in last_pairs.iter() {
                    self.push_env();
                    let branch = (|| -> Result<(), RuntimeError> {
                        self.have_fn_by_induc_verify_last_case_register_fn_and_store_dom(
                            stmt,
                            &param_name_str,
                        )?;
                        let merged = Self::have_fn_by_induc_merge_step_and_when(
                            step.clone(),
                            when.clone(),
                            line_file.clone(),
                        )
                        .map_err(RuntimeError::from)?;
                        self.store_fact_without_well_defined_verified_and_infer(merged.to_fact())
                            .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
                        self.have_fn_by_induc_verify_one_equal_to_well_defined(
                            stmt,
                            eq_to,
                            &verify_state,
                        )
                    })();
                    self.pop_env();
                    branch?;
                }
            }
            _ => {
                return Err(RuntimeError::ExecStmtError(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        Stmt::HaveFnByInducStmt(stmt.clone()),
                        "have_fn_by_induc: last case must be either `: obj` or nested `case` blocks, not both or neither".to_string(),
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
        _stmt: &HaveFnByInducStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        panic!("not implemented");
    }
}
