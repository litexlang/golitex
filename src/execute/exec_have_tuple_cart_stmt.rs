use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_have_tuple_stmt(
        &mut self,
        stmt: &HaveTupleStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_tuple_stmt_verify_well_definedness(stmt)?;
        let check_results = self.exec_have_tuple_stmt_verify_process(stmt)?;
        let infer_result = self.exec_have_tuple_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, check_results).into())
    }

    pub fn exec_have_cart_stmt(&mut self, stmt: &HaveCartStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_have_cart_stmt_verify_well_definedness(stmt)?;
        let check_results = self.exec_have_cart_stmt_verify_process(stmt)?;
        let infer_result = self.exec_have_cart_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, check_results).into())
    }

    fn exec_have_tuple_stmt_verify_well_definedness(
        &mut self,
        stmt: &HaveTupleStmt,
    ) -> Result<(), RuntimeError> {
        self.verify_tuple_or_cart_name_available(stmt.clone().into(), &stmt.name)?;
        self.verify_tuple_or_cart_value_before_defining_name(
            stmt.clone().into(),
            ParamObjType::TupleIndex,
            &stmt.index_name,
            &stmt.dimension,
            &stmt.value,
        )
    }

    fn exec_have_tuple_stmt_verify_process(
        &mut self,
        stmt: &HaveTupleStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.verify_tuple_or_cart_dimension(
            stmt.clone().into(),
            &stmt.dimension,
            stmt.line_file.clone(),
        )
    }

    fn exec_have_tuple_stmt_affect_environment(
        &mut self,
        stmt: &HaveTupleStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.store_free_param_or_identifier_name(&stmt.name, ParamObjType::Identifier)
            .map_err(|e| short_exec_error(stmt.clone().into(), String::new(), Some(e), vec![]))?;

        let mut infer_result = InferResult::new();
        let target: Obj = Identifier::new(stmt.name.clone()).into();
        infer_result.new_infer_result_inside(self.store_have_tuple_or_cart_fact(
            IsTupleFact::new(target.clone(), stmt.line_file.clone()).into(),
            HaveTupleStmt::store_reason(),
        )?);
        infer_result.new_infer_result_inside(
            self.store_have_tuple_or_cart_fact(
                EqualFact::new(
                    TupleDim::new(target.clone()).into(),
                    stmt.dimension.clone(),
                    stmt.line_file.clone(),
                )
                .into(),
                HaveTupleStmt::store_reason(),
            )?,
        );

        let forall_fact = self.tuple_coordinate_forall_fact(stmt)?;
        infer_result.new_infer_result_inside(
            self.store_have_tuple_or_cart_fact(forall_fact.into(), HaveTupleStmt::store_reason())?,
        );

        Ok(infer_result)
    }

    fn exec_have_cart_stmt_verify_well_definedness(
        &mut self,
        stmt: &HaveCartStmt,
    ) -> Result<(), RuntimeError> {
        self.verify_tuple_or_cart_name_available(stmt.clone().into(), &stmt.name)?;
        self.verify_tuple_or_cart_value_before_defining_name(
            stmt.clone().into(),
            ParamObjType::CartIndex,
            &stmt.index_name,
            &stmt.dimension,
            &stmt.value,
        )
    }

    fn exec_have_cart_stmt_verify_process(
        &mut self,
        stmt: &HaveCartStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.verify_tuple_or_cart_dimension(
            stmt.clone().into(),
            &stmt.dimension,
            stmt.line_file.clone(),
        )
    }

    fn exec_have_cart_stmt_affect_environment(
        &mut self,
        stmt: &HaveCartStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.store_free_param_or_identifier_name(&stmt.name, ParamObjType::Identifier)
            .map_err(|e| short_exec_error(stmt.clone().into(), String::new(), Some(e), vec![]))?;

        let mut infer_result = InferResult::new();
        let target: Obj = Identifier::new(stmt.name.clone()).into();
        infer_result.new_infer_result_inside(self.store_have_tuple_or_cart_fact(
            IsSetFact::new(target.clone(), stmt.line_file.clone()).into(),
            HaveCartStmt::store_reason(),
        )?);
        infer_result.new_infer_result_inside(self.store_have_tuple_or_cart_fact(
            IsCartFact::new(target.clone(), stmt.line_file.clone()).into(),
            HaveCartStmt::store_reason(),
        )?);
        infer_result.new_infer_result_inside(
            self.store_have_tuple_or_cart_fact(
                EqualFact::new(
                    CartDim::new(target.clone()).into(),
                    stmt.dimension.clone(),
                    stmt.line_file.clone(),
                )
                .into(),
                HaveCartStmt::store_reason(),
            )?,
        );

        let forall_fact = self.cart_coordinate_forall_fact(stmt)?;
        infer_result.new_infer_result_inside(
            self.store_have_tuple_or_cart_fact(forall_fact.into(), HaveCartStmt::store_reason())?,
        );

        Ok(infer_result)
    }

    fn verify_tuple_or_cart_name_available(
        &mut self,
        stmt: Stmt,
        name: &str,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.store_free_param_or_identifier_name(name, ParamObjType::Identifier)
                .map_err(|e| short_exec_error(stmt, String::new(), Some(e), vec![]))
        })
    }

    fn verify_tuple_or_cart_dimension(
        &mut self,
        stmt: Stmt,
        dimension: &Obj,
        line_file: LineFile,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut check_results = Vec::new();
        let in_n_pos: AtomicFact = InFact::new(
            dimension.clone(),
            StandardSet::NPos.into(),
            line_file.clone(),
        )
        .into();
        let in_n_pos_result = self
            .verify_atomic_fact(&in_n_pos, &VerifyState::new(0, false))
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        if in_n_pos_result.is_unknown() {
            return Err(short_exec_error(
                stmt,
                format!("have tuple/cart needs {} $in N_pos", dimension),
                None,
                vec![in_n_pos_result],
            ));
        }
        check_results.push(in_n_pos_result);

        let two: Obj = Number::new("2".to_string()).into();
        let at_least_two: AtomicFact = LessEqualFact::new(two, dimension.clone(), line_file).into();
        let at_least_two_result = self
            .verify_atomic_fact(&at_least_two, &VerifyState::new(0, false))
            .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
        if at_least_two_result.is_unknown() {
            return Err(short_exec_error(
                stmt,
                format!("have tuple/cart needs 2 <= {}", dimension),
                None,
                vec![at_least_two_result],
            ));
        }
        check_results.push(at_least_two_result);
        Ok(check_results)
    }

    fn verify_tuple_or_cart_value_before_defining_name(
        &mut self,
        stmt: Stmt,
        index_kind: ParamObjType,
        index_name: &str,
        dimension: &Obj,
        value: &Obj,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            let index_params = tuple_or_cart_index_param_def(index_name, dimension.clone());
            rt.define_params_with_type(&index_params, true, index_kind)
                .map_err(|e| short_exec_error(stmt.clone(), String::new(), Some(e), vec![]))?;
            rt.verify_obj_well_defined_and_store_cache(value, &VerifyState::new(0, false))
                .map_err(|e| short_exec_error(stmt, String::new(), Some(e), vec![]))
        })
    }

    fn store_have_tuple_or_cart_fact(
        &mut self,
        fact: Fact,
        reason: &'static str,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result =
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(fact)?;
        infer_result.relabel_all_added_facts_with_store_reason(reason);
        Ok(infer_result)
    }

    fn tuple_coordinate_forall_fact(
        &self,
        stmt: &HaveTupleStmt,
    ) -> Result<ForallFact, RuntimeError> {
        let index_obj = obj_for_bound_param_in_scope(stmt.index_name.clone(), ParamObjType::Forall);
        let value = self.value_with_public_forall_index(
            &stmt.value,
            &stmt.index_name,
            ParamObjType::TupleIndex,
        )?;
        let target: Obj = Identifier::new(stmt.name.clone()).into();
        let left: Obj = ObjAtIndex::new(target, index_obj).into();
        let equal_fact = EqualFact::new(left, value, stmt.line_file.clone());
        ForallFact::new(
            tuple_or_cart_index_param_def(&stmt.index_name, stmt.dimension.clone()),
            vec![],
            vec![equal_fact.into()],
            stmt.line_file.clone(),
        )
    }

    fn cart_coordinate_forall_fact(&self, stmt: &HaveCartStmt) -> Result<ForallFact, RuntimeError> {
        let index_obj = obj_for_bound_param_in_scope(stmt.index_name.clone(), ParamObjType::Forall);
        let value = self.value_with_public_forall_index(
            &stmt.value,
            &stmt.index_name,
            ParamObjType::CartIndex,
        )?;
        let target: Obj = Identifier::new(stmt.name.clone()).into();
        let left: Obj = Proj::new(target, index_obj).into();
        let equal_fact = EqualFact::new(left, value, stmt.line_file.clone());
        ForallFact::new(
            tuple_or_cart_index_param_def(&stmt.index_name, stmt.dimension.clone()),
            vec![],
            vec![equal_fact.into()],
            stmt.line_file.clone(),
        )
    }

    fn value_with_public_forall_index(
        &self,
        value: &Obj,
        index_name: &str,
        index_kind: ParamObjType,
    ) -> Result<Obj, RuntimeError> {
        let mut param_to_arg_map = HashMap::new();
        param_to_arg_map.insert(
            index_name.to_string(),
            obj_for_bound_param_in_scope(index_name.to_string(), ParamObjType::Forall),
        );
        self.inst_obj(value, &param_to_arg_map, index_kind)
    }
}

fn tuple_or_cart_index_param_def(index_name: &str, dimension: Obj) -> ParamDefWithType {
    let one: Obj = Number::new("1".to_string()).into();
    let index_set: Obj = ClosedRange::new(one, dimension).into();
    ParamDefWithType::new(vec![ParamGroupWithParamType::new(
        vec![index_name.to_string()],
        ParamType::Obj(index_set),
    )])
}
