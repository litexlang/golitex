use crate::prelude::*;

impl Runtime {
    pub fn exec_have_by_preimage_stmt(
        &mut self,
        stmt: &HaveByPreimageStmt,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::Replacement(replacement) = &stmt.range_membership.set {
            if stmt.preimage_names.len() != 1 {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "have by preimage: expected 1 preimage name(s), got {}",
                        stmt.preimage_names.len()
                    ),
                    None,
                    vec![],
                ));
            }
            let source_result = self.verify_preimage_source_membership(stmt)?;
            return self.exec_have_by_replacement_preimage_stmt(stmt, replacement, source_result);
        }

        let (function, fn_body) = self.preimage_function_and_body(stmt)?;
        let param_count = fn_body.params_def_with_set.number_of_params();
        if stmt.preimage_names.len() != param_count {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "have by preimage: expected {} preimage name(s), got {}",
                    param_count,
                    stmt.preimage_names.len()
                ),
                None,
                vec![],
            ));
        }
        let source_result = self.verify_preimage_source_membership(stmt)?;

        for name in stmt.preimage_names.iter() {
            self.store_free_param_or_identifier_name(name, ParamObjType::Exist)
                .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        }

        let preimage_objs: Vec<Obj> = stmt
            .preimage_names
            .iter()
            .map(|name| Identifier::new(name.clone()).into())
            .collect();

        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(self.store_preimage_param_set_facts(
            stmt,
            &fn_body,
            &preimage_objs,
        )?);
        infer_result.new_infer_result_inside(self.store_preimage_domain_facts(
            stmt,
            &fn_body,
            &preimage_objs,
        )?);
        infer_result.new_infer_result_inside(self.store_preimage_value_equality(
            stmt,
            &function,
            &preimage_objs,
        )?);

        Ok(
            NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![source_result])
                .into(),
        )
    }

    fn verify_preimage_source_membership(
        &mut self,
        stmt: &HaveByPreimageStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let source_atomic: AtomicFact = stmt.range_membership.clone().into();
        let verify_state = VerifyState::new(0, false);
        let source_result = self
            .verify_atomic_fact(&source_atomic, &verify_state)
            .map_err(|verify_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), verify_error)
            })?;
        if source_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                "have by preimage: source range membership is not verified".to_string(),
                None,
                vec![],
            ));
        }
        Ok(source_result)
    }

    fn exec_have_by_replacement_preimage_stmt(
        &mut self,
        stmt: &HaveByPreimageStmt,
        replacement: &Replacement,
        source_result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let preimage_name = &stmt.preimage_names[0];
        self.store_free_param_or_identifier_name(preimage_name, ParamObjType::Exist)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        let preimage_obj: Obj = Identifier::new(preimage_name.clone()).into();

        let preimage_in_source: Fact = InFact::new(
            preimage_obj.clone(),
            replacement.source_set.as_ref().clone(),
            stmt.line_file.clone(),
        )
        .into();
        let relation_fact: Fact = NormalAtomicFact::new(
            replacement.prop_name.clone(),
            vec![preimage_obj, stmt.range_membership.element.clone()],
            stmt.line_file.clone(),
        )
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(
            self.verify_well_defined_and_store_and_infer(
                preimage_in_source,
                &VerifyState::new(0, false),
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?,
        );
        infer_result.new_infer_result_inside(
            self.verify_well_defined_and_store_and_infer(
                relation_fact,
                &VerifyState::new(0, false),
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?,
        );

        Ok(
            NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![source_result])
                .into(),
        )
    }

    fn preimage_function_and_body(
        &self,
        stmt: &HaveByPreimageStmt,
    ) -> Result<(Obj, FnSetBody), RuntimeError> {
        match &stmt.range_membership.set {
            Obj::FnRange(fn_range) => {
                let fn_body = self
                    .get_fn_range_function_body(&fn_range.function)
                    .ok_or_else(|| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "have by preimage: function `{}` has no known function set",
                                fn_range.function
                            ),
                            None,
                            vec![],
                        )
                    })?;
                Ok((fn_range.function.as_ref().clone(), fn_body))
            }
            Obj::FnRangeOn(fn_range_on) => {
                let fn_set = self
                    .fn_range_on_target_fn_set(fn_range_on, stmt.line_file.clone())
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
                Ok((fn_range_on.function.as_ref().clone(), fn_set.body.clone()))
            }
            _ => Err(short_exec_error(
                stmt.clone().into(),
                "have by preimage expects `from z $in fn_range(f)`, `from z $in fn_range_on(f, S)`, or `from z $in replacement(P, A)`".to_string(),
                None,
                vec![],
            )),
        }
    }

    fn store_preimage_param_set_facts(
        &mut self,
        stmt: &HaveByPreimageStmt,
        fn_body: &FnSetBody,
        preimage_objs: &Vec<Obj>,
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_param_sets = self
            .inst_param_def_with_set_one_by_one(
                &fn_body.params_def_with_set,
                preimage_objs,
                ParamObjType::FnSet,
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        let flat_param_sets = fn_body
            .params_def_with_set
            .flat_instantiated_param_sets_for_args(&instantiated_param_sets);

        let mut infer_result = InferResult::new();
        for (preimage_obj, param_set) in preimage_objs.iter().zip(flat_param_sets.iter()) {
            let fact: Fact = InFact::new(
                preimage_obj.clone(),
                param_set.clone(),
                stmt.line_file.clone(),
            )
            .into();
            infer_result.new_infer_result_inside(
                self.verify_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false))
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?,
            );
        }
        Ok(infer_result)
    }

    fn store_preimage_domain_facts(
        &mut self,
        stmt: &HaveByPreimageStmt,
        fn_body: &FnSetBody,
        preimage_objs: &Vec<Obj>,
    ) -> Result<InferResult, RuntimeError> {
        let param_to_obj_map = fn_body
            .params_def_with_set
            .param_defs_and_args_to_param_to_arg_map(preimage_objs);
        let mut infer_result = InferResult::new();
        for dom_fact in fn_body.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    &param_to_obj_map,
                    ParamObjType::FnSet,
                    Some(&stmt.line_file),
                )
                .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?
                .to_fact();
            infer_result.new_infer_result_inside(
                self.verify_well_defined_and_store_and_infer(
                    instantiated_dom_fact,
                    &VerifyState::new(0, false),
                )
                .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?,
            );
        }
        Ok(infer_result)
    }

    fn store_preimage_value_equality(
        &mut self,
        stmt: &HaveByPreimageStmt,
        function: &Obj,
        preimage_objs: &Vec<Obj>,
    ) -> Result<InferResult, RuntimeError> {
        let application = preimage_application_obj(function, preimage_objs).ok_or_else(|| {
            short_exec_error(
                stmt.clone().into(),
                format!(
                    "have by preimage: cannot build a function application for `{}`",
                    function
                ),
                None,
                vec![],
            )
        })?;
        let equality_fact: Fact = EqualFact::new(
            stmt.range_membership.element.clone(),
            application,
            stmt.line_file.clone(),
        )
        .into();
        self.verify_well_defined_and_store_and_infer(equality_fact, &VerifyState::new(0, false))
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))
    }
}

fn preimage_application_obj(function: &Obj, args: &Vec<Obj>) -> Option<Obj> {
    let head = match function {
        Obj::AnonymousFn(anonymous_fn) => {
            FnObjHead::AnonymousFnLiteral(Box::new(anonymous_fn.clone()))
        }
        Obj::FiniteSeqListObj(list) => FnObjHead::FiniteSeqListObj(list.clone()),
        Obj::InstantiatedTemplateObj(template_obj) => {
            FnObjHead::InstantiatedTemplateObj(template_obj.clone())
        }
        _ => FnObjHead::given_an_atom_return_a_fn_obj_head(function.clone())?,
    };
    let group = args.iter().cloned().map(Box::new).collect();
    Some(FnObj::new(head, vec![group]).into())
}
