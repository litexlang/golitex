use crate::prelude::*;

impl Runtime {
    pub fn exec_have_seq_stmt(&mut self, stmt: &HaveSeqStmt) -> Result<StmtResult, RuntimeError> {
        let anonymous_fn = build_have_seq_anonymous_fn(stmt)
            .map_err(|e| short_exec_error(stmt.clone().into(), String::new(), Some(e), vec![]))?;
        self.exec_have_indexed_fn_definition(
            stmt.clone().into(),
            &stmt.name,
            stmt.seq_set.clone().into(),
            anonymous_fn,
            HaveSeqStmt::store_reason(),
            stmt.line_file.clone(),
            vec![],
        )
    }

    pub fn exec_have_finite_seq_stmt(
        &mut self,
        stmt: &HaveFiniteSeqStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let mut check_results = Vec::new();
        check_results.extend(self.verify_have_indexed_fn_bound(
            stmt.clone().into(),
            &stmt.bound,
            stmt.finite_seq_set.n.as_ref(),
            "have finite_seq by-bound must match finite_seq length",
            stmt.line_file.clone(),
        )?);

        let anonymous_fn = build_have_finite_seq_anonymous_fn(stmt)
            .map_err(|e| short_exec_error(stmt.clone().into(), String::new(), Some(e), vec![]))?;
        self.exec_have_indexed_fn_definition(
            stmt.clone().into(),
            &stmt.name,
            stmt.finite_seq_set.clone().into(),
            anonymous_fn,
            HaveFiniteSeqStmt::store_reason(),
            stmt.line_file.clone(),
            check_results,
        )
    }

    pub fn exec_have_matrix_stmt(
        &mut self,
        stmt: &HaveMatrixStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let mut check_results = Vec::new();
        check_results.extend(self.verify_have_indexed_fn_bound(
            stmt.clone().into(),
            &stmt.row_bound,
            stmt.matrix_set.row_len.as_ref(),
            "have matrix row by-bound must match matrix row count",
            stmt.line_file.clone(),
        )?);
        check_results.extend(self.verify_have_indexed_fn_bound(
            stmt.clone().into(),
            &stmt.col_bound,
            stmt.matrix_set.col_len.as_ref(),
            "have matrix column by-bound must match matrix column count",
            stmt.line_file.clone(),
        )?);

        let anonymous_fn = build_have_matrix_anonymous_fn(stmt)
            .map_err(|e| short_exec_error(stmt.clone().into(), String::new(), Some(e), vec![]))?;
        self.exec_have_indexed_fn_definition(
            stmt.clone().into(),
            &stmt.name,
            stmt.matrix_set.clone().into(),
            anonymous_fn,
            HaveMatrixStmt::store_reason(),
            stmt.line_file.clone(),
            check_results,
        )
    }

    fn exec_have_indexed_fn_definition(
        &mut self,
        stmt: Stmt,
        name: &str,
        surface_set: Obj,
        anonymous_fn: AnonymousFn,
        store_reason: &'static str,
        line_file: LineFile,
        check_results: Vec<StmtResult>,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set = FnSet::from_body(anonymous_fn.body.clone())
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;

        self.verify_have_indexed_fn_definition_well_defined(
            stmt.clone(),
            &anonymous_fn,
            &surface_set,
            &fn_set,
            store_reason,
            line_file.clone(),
        )?;

        self.store_free_param_or_identifier_name(name, ParamObjType::Identifier)
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;

        let function_identifier_obj: Obj = Identifier::new(name.to_string()).into();
        let surface_membership_fact: AtomicFact = InFact::new(
            function_identifier_obj.clone(),
            surface_set,
            line_file.clone(),
        )
        .into();

        let mut infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(
                surface_membership_fact.into(),
            )
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        infer_result.relabel_all_added_facts_with_store_reason(store_reason);

        self.register_known_objs_in_fn_sets_for_element_body(
            &function_identifier_obj,
            fn_set.body.clone(),
            Some((*anonymous_fn.equal_to).clone()),
            line_file.clone(),
            line_file.clone(),
        );

        let function_equals_anonymous_fn_fact: AtomicFact =
            EqualFact::new(function_identifier_obj, anonymous_fn.into(), line_file).into();
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                function_equals_anonymous_fn_fact,
                store_reason,
            )
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?,
        );

        Ok(NonFactualStmtSuccess::new(stmt, infer_result, check_results).into())
    }

    fn verify_have_indexed_fn_definition_well_defined(
        &mut self,
        stmt: Stmt,
        anonymous_fn: &AnonymousFn,
        surface_set: &Obj,
        fn_set: &FnSet,
        store_reason: &'static str,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.verify_have_indexed_fn_definition_well_defined_body(
                stmt,
                anonymous_fn,
                surface_set,
                fn_set,
                store_reason,
                line_file,
            )
        })
    }

    fn verify_have_indexed_fn_definition_well_defined_body(
        &mut self,
        stmt: Stmt,
        anonymous_fn: &AnonymousFn,
        surface_set: &Obj,
        fn_set: &FnSet,
        store_reason: &'static str,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(surface_set, &verify_state)
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        self.verify_obj_well_defined_and_store_cache(&anonymous_fn.clone().into(), &verify_state)
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        self.verify_obj_well_defined_and_store_cache(&fn_set.clone().into(), &verify_state)
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;

        let verify_result = self
            .run_in_local_env(|rt| {
                for param_def_with_set in anonymous_fn.body.params_def_with_set.iter() {
                    rt.define_params_with_set(param_def_with_set)?;
                }
                for dom_fact in anonymous_fn.body.dom_facts.iter() {
                    let _ = rt
                        .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                            dom_fact.clone(),
                        )?;
                }
                let value_membership: AtomicFact = InFact::new(
                    (*anonymous_fn.equal_to).clone(),
                    (*anonymous_fn.body.ret_set).clone(),
                    line_file,
                )
                .into();
                rt.verify_atomic_fact(&value_membership, &verify_state)
            })
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        if verify_result.is_unknown() {
            return Err(short_exec_error(
                stmt,
                format!(
                    "{}: {} is not in return set {}",
                    store_reason, anonymous_fn.equal_to, anonymous_fn.body.ret_set,
                ),
                None,
                vec![verify_result],
            ));
        }
        Ok(())
    }

    fn verify_have_indexed_fn_bound(
        &mut self,
        stmt: Stmt,
        bound: &Obj,
        expected: &Obj,
        mismatch_msg: &str,
        line_file: LineFile,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut check_results = Vec::new();
        let in_n_pos: AtomicFact =
            InFact::new(bound.clone(), StandardSet::NPos.into(), line_file.clone()).into();
        let in_n_pos_result = self
            .verify_atomic_fact(&in_n_pos, &VerifyState::new(0, false))
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        if in_n_pos_result.is_unknown() {
            return Err(short_exec_error(
                stmt,
                format!("{} needs {} $in N_pos", mismatch_msg, bound),
                None,
                vec![in_n_pos_result],
            ));
        }
        check_results.push(in_n_pos_result);

        let equal_fact: AtomicFact =
            EqualFact::new(bound.clone(), expected.clone(), line_file).into();
        let equal_result = self
            .verify_atomic_fact(&equal_fact, &VerifyState::new(0, false))
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        if equal_result.is_unknown() {
            return Err(short_exec_error(
                stmt,
                mismatch_msg.to_string(),
                None,
                vec![equal_result],
            ));
        }
        check_results.push(equal_result);
        Ok(check_results)
    }
}

fn build_have_seq_anonymous_fn(stmt: &HaveSeqStmt) -> Result<AnonymousFn, RuntimeError> {
    AnonymousFn::new(
        vec![ParamGroupWithSet::new(
            vec![stmt.index_name.clone()],
            StandardSet::NPos.into(),
        )],
        vec![],
        (*stmt.seq_set.set).clone(),
        stmt.value.clone(),
    )
}

fn build_have_finite_seq_anonymous_fn(
    stmt: &HaveFiniteSeqStmt,
) -> Result<AnonymousFn, RuntimeError> {
    let index_obj = obj_for_bound_param_in_scope(stmt.index_name.clone(), ParamObjType::FnSet);
    AnonymousFn::new(
        vec![ParamGroupWithSet::new(
            vec![stmt.index_name.clone()],
            StandardSet::NPos.into(),
        )],
        vec![AtomicFact::from(LessEqualFact::new(
            index_obj,
            stmt.bound.clone(),
            stmt.line_file.clone(),
        ))
        .into()],
        (*stmt.finite_seq_set.set).clone(),
        stmt.value.clone(),
    )
}

fn build_have_matrix_anonymous_fn(stmt: &HaveMatrixStmt) -> Result<AnonymousFn, RuntimeError> {
    let row_obj = obj_for_bound_param_in_scope(stmt.row_index_name.clone(), ParamObjType::FnSet);
    let col_obj = obj_for_bound_param_in_scope(stmt.col_index_name.clone(), ParamObjType::FnSet);
    AnonymousFn::new(
        vec![
            ParamGroupWithSet::new(vec![stmt.row_index_name.clone()], StandardSet::NPos.into()),
            ParamGroupWithSet::new(vec![stmt.col_index_name.clone()], StandardSet::NPos.into()),
        ],
        vec![
            AtomicFact::from(LessEqualFact::new(
                row_obj,
                stmt.row_bound.clone(),
                stmt.line_file.clone(),
            ))
            .into(),
            AtomicFact::from(LessEqualFact::new(
                col_obj,
                stmt.col_bound.clone(),
                stmt.line_file.clone(),
            ))
            .into(),
        ],
        (*stmt.matrix_set.set).clone(),
        stmt.value.clone(),
    )
}
