use crate::prelude::*;
use crate::stmt::definition_stmt::induc_obj_plus_offset;

impl Runtime {
    pub fn exec_have_fn_by_induc(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.exec_have_fn_by_induc_verify_process(stmt))?;

        let infer_result = self.exec_have_fn_by_induc_store_process(stmt)?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(Stmt::HaveFnByInducStmt(stmt.clone()), infer_result, vec![]),
        ))
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

    // have fn by induc from 0: f(x Z: x >= 0) R: case 0: … case 1: …
    /// 先按 `stmt.fn_set` 声明归纳参数 `param_name`，再登记 `stmt.name` 属于一个形式参数为**新生成名字**的 `FnSet`，
    /// 其定义域满足 `random_param < param_name` 且 `random_param >= param_name - len(special_cases)`（与特例下标区间一致）。
    fn have_fn_by_induc_verify_last_case_register_fn(
        &mut self,
        stmt: &HaveFnByInducStmt,
        param_name: &str,
    ) -> Result<(), RuntimeError> {
        self.store_identifier_obj(&stmt.name)
            .map_err(RuntimeError::from)?;

        let random_param_with_mangled_prefix = format!(
            "{}{}",
            DEFAULT_MANGLED_FN_PARAM_PREFIX,
            self.generate_random_unused_names(1)[0].clone()
        );

        let param_minus_n = Obj::Sub(Sub::new(
            Obj::Identifier(Identifier::new(param_name.to_string())),
            Obj::Number(Number::new(stmt.special_cases_equal_tos.len().to_string())),
        ));

        let dom_facts: Vec<OrAndChainAtomicFact> = vec![
            OrAndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                Obj::Identifier(Identifier::new(random_param_with_mangled_prefix.clone())),
                param_minus_n,
                stmt.line_file.clone(),
            ))),
            OrAndChainAtomicFact::AtomicFact(AtomicFact::LessFact(LessFact::new(
                Obj::Identifier(Identifier::new(random_param_with_mangled_prefix.clone())),
                Obj::Identifier(Identifier::new(param_name.to_string())),
                stmt.line_file.clone(),
            ))),
        ];

        let restricted_fn_set = FnSet::new(
            vec![ParamGroupWithSet::new(
                vec![random_param_with_mangled_prefix.clone()],
                Obj::StandardSet(StandardSet::Z),
            )],
            dom_facts,
            stmt.ret_set.clone(),
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
            stmt.ret_set.clone(),
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
                        equal_to, stmt.ret_set
                    ),
                    None,
                    vec![],
                ),
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

        let left_id = Obj::Identifier(Identifier::new(param_name_str.clone()));

        self.store_identifier_obj(&param_name_str)
            .map_err(RuntimeError::from)?;

        self.define_parameter_by_binding_param_type(
            &param_name_str,
            &ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
        )?;

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

        // 归纳步里要用到 f(x-1), …, f(x-n)。仅 `store_well_defined_obj_cache` 不够：`verify_add_well_defined`
        // 会对每个加数做 `require_obj_in_r`；若命中 well-defined 缓存则不会走 `verify_fn_obj_well_defined`，
        // 也就不会登记 `f(x-i) ∈ ret_set` 的中间事实，加法会失败。这里显式登记与源码同形的 `FnObj` 的成员关系。
        for i in 1..=n {
            let arg = Obj::Sub(Sub::new(
                Obj::Identifier(Identifier::new(param_name_str.to_string())),
                Obj::Number(Number::new(i.to_string())),
            ));
            let fn_obj = Obj::FnObj(FnObj {
                head: Box::new(Atom::Identifier(Identifier::new(stmt.name.clone()))),
                body: vec![vec![Box::new(arg.clone())]],
            });
            self.store_well_defined_obj_cache(&fn_obj);
            let fn_in_ret = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                fn_obj,
                stmt.ret_set.clone(),
                line_file.clone(),
            )));
            self.store_fact_without_well_defined_verified_and_infer(fn_in_ret)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
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

    /// [`Runtime::infer`] 对 `ForallFact`、`f $in FnSet` 等常返回空的 [`InferResult`]，JSON 里 `infer_facts` 会误以为没有推出任何东西。
    /// 若本步 `store_*_and_infer` 的链式推导为空，则把刚存入的 [`Fact`] 记入列表，便于展示「本语句提交的事实」。
    fn merge_store_infer_with_fallback_fact(
        infer_result: &mut InferResult,
        store_infer: InferResult,
        fallback_fact: &Fact,
    ) {
        let empty = store_infer.infer_facts.is_empty();
        infer_result.new_infer_result_inside(store_infer);
        if empty {
            infer_result.new_fact(fallback_fact);
        }
    }

    fn exec_have_fn_by_induc_store_process(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        let fs = self.fn_set_for_storage_from_have_fn_clause(
            &stmt.fn_user_fn_set_clause(),
            stmt.line_file.clone(),
        )?;

        let bind_infer = self.define_parameter_by_binding_param_type(
            &stmt.name,
            &ParamType::Obj(Obj::FnSet(fs.clone())),
        )?;
        let bind_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            Obj::Identifier(Identifier::new(stmt.name.clone())),
            Obj::FnSet(fs.clone()),
            stmt.line_file.clone(),
        )));
        Self::merge_store_infer_with_fallback_fact(&mut infer_result, bind_infer, &bind_fact);

        // 遍历所有special case，让 stmt.name(induc_from + i) = equal_to[i]
        for i in 0..stmt.special_cases_equal_tos.len() {
            let raw_arg = if i == 0 {
                stmt.induc_from.clone()
            } else {
                Obj::Add(Add::new(
                    stmt.induc_from.clone(),
                    Obj::Number(Number::new(i.to_string())),
                ))
            };
            // 纯数字加法等折叠成字面量，避免存成 f(0 + 1) 而应 f(1)
            let arg = raw_arg.replace_with_numeric_result_if_can_be_calculated().0;

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

            let result = self
                .store_fact_without_well_defined_verified_and_infer(equal_fact.clone())
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;

            Self::merge_store_infer_with_fallback_fact(&mut infer_result, result, &equal_fact);
        }

        match &stmt.last_case {
            HaveFnByInducLastCase::EqualTo(eq) => {
                let param_name = stmt.param.clone();
                let param_def = vec![ParamGroupWithParamType::new(
                    vec![param_name.clone()],
                    ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
                )];

                let mut dom: Vec<ExistOrAndChainAtomicFact> =
                    stmt.forall_fn_base_dom_exist_or_facts();

                let induc_plus_n = induc_obj_plus_offset(
                    &stmt.induc_from,
                    stmt.special_cases_equal_tos.len(),
                )
                .replace_with_numeric_result_if_can_be_calculated()
                .0;
                dom.push(ExistOrAndChainAtomicFact::AtomicFact(
                    AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                        Obj::Identifier(Identifier::new(param_name.clone())),
                        induc_plus_n,
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

                let result = self
                    .store_fact_without_well_defined_verified_and_infer(forall_fact.clone())
                    .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
                Self::merge_store_infer_with_fallback_fact(&mut infer_result, result, &forall_fact);
            }
            HaveFnByInducLastCase::NestedCases(last_pairs) => {
                for nested in last_pairs.iter() {
                    let param_name = stmt.param.clone();
                    let param_def = vec![ParamGroupWithParamType::new(
                        vec![param_name.clone()],
                        ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
                    )];
                    let eq = nested.equal_to.clone();

                    let mut dom: Vec<ExistOrAndChainAtomicFact> =
                        stmt.forall_fn_base_dom_exist_or_facts();

                    let induc_plus_n = induc_obj_plus_offset(
                        &stmt.induc_from,
                        stmt.special_cases_equal_tos.len(),
                    )
                    .replace_with_numeric_result_if_can_be_calculated()
                    .0;
                    dom.push(ExistOrAndChainAtomicFact::AtomicFact(
                        AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            Obj::Identifier(Identifier::new(param_name.clone())),
                            induc_plus_n,
                            stmt.line_file.clone(),
                        )),
                    ));

                    dom.push(nested.case_fact.to_exist_or_and_chain_atomic_fact());

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

                    let result = self
                        .store_fact_without_well_defined_verified_and_infer(forall_fact.clone())
                        .map_err(|e| Self::have_fn_by_induc_err(stmt, e.into()))?;
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
}
