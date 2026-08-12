use crate::prelude::*;
use std::collections::HashMap;

use super::exec_have_fn_equal_shared::build_declared_function_obj_with_param_bindings;

struct HaveFnByForallExistUniqueShape {
    fn_set_clause: FnSetClause,
    witness_name: String,
    witness_binding: SymbolBinding,
    witness_param_type: ParamType,
    exist_body_facts: Vec<ExistBodyFact>,
}

impl Runtime {
    pub fn exec_have_fn_by_forall_exist_unique_stmt(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let shape = self.exec_have_fn_by_forall_exist_unique_verify_well_definedness(stmt)?;
        let inside_results = self.exec_have_fn_by_forall_exist_unique_verify_process(stmt)?;
        let infer_result =
            self.exec_have_fn_by_forall_exist_unique_affect_environment(stmt, shape)?;

        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results)).into())
    }

    /// Mathematical contract: choice of a function from unique existence is
    /// meaningful only when the source universal-existential statement and
    /// its derived function signature are structurally valid and the complete
    /// quantified fact is well-defined.
    fn exec_have_fn_by_forall_exist_unique_verify_well_definedness(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<HaveFnByForallExistUniqueShape, RuntimeError> {
        let shape = self.have_fn_by_forall_exist_unique_shape(stmt)?;
        self.verify_fact_well_defined(
            &Fact::ForallFact(stmt.forall.clone()),
            &UseContextVerifyState::new(0, false),
        )
        .map_err(|e| {
            short_exec_error(
                stmt.clone().into(),
                "have_fn_by_forall_exist_unique: forall fact is not well defined".to_string(),
                Some(e),
                vec![],
            )
        })?;
        Ok(shape)
    }

    fn exec_have_fn_by_forall_exist_unique_verify_process(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        if stmt.prove_process.is_empty() {
            let forall_fact: Fact = stmt.forall.clone().into();
            let result = self
                .verify_fact_return_err_if_not_true(
                    &forall_fact,
                    &UseContextVerifyState::new(0, false),
                )
                .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
            Ok(vec![result])
        } else {
            self.exec_have_fn_by_forall_exist_unique_prove_process(stmt)
        }
    }

    fn exec_have_fn_by_forall_exist_unique_prove_process(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.verify_fact_well_defined(
            &Fact::ForallFact(stmt.forall.clone()),
            &UseContextVerifyState::new(0, false),
        )
        .map_err(|e| {
            short_exec_error(
                stmt.clone().into(),
                "have_fn_by_forall_exist_unique: forall fact is not well defined".to_string(),
                Some(e),
                vec![],
            )
        })?;

        self.run_in_local_env(|rt| {
            rt.define_params_with_type(
                &stmt.forall.params_def_with_type,
                false,
                ParamObjType::Forall,
            )
            .map_err(|define_params_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
            })?;

            for dom_fact in stmt.forall.dom_facts.iter() {
                rt.store_with_well_defined_verification_and_infer(
                    dom_fact.clone(),
                    &UseContextVerifyState::new(0, false),
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
                                "have fn `{}` by exist! failed: proof step is unknown",
                                stmt.fn_name()
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

            let then_count = stmt.forall.then_facts.len();
            let then_verify_state = UseContextVerifyState::new(0, false);
            for (then_index, then_fact) in stmt.forall.then_facts.iter().enumerate() {
                let mut result =
                    rt.verify_exist_or_and_chain_atomic_fact(then_fact, &then_verify_state)?;
                if result.is_unknown() {
                    let then_goal = then_fact.clone().to_fact();
                    result = rt.structured_unknown_result_for_failed_fact(
                        &then_goal,
                        &then_verify_state,
                        result,
                    )?;
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(then_goal.clone().into()),
                            format!(
                                "have fn `{}` by exist! failed: cannot prove then-clause",
                                stmt.fn_name()
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

            Ok(inside_results)
        })
    }

    fn exec_have_fn_by_forall_exist_unique_affect_environment(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: HaveFnByForallExistUniqueShape,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        let fn_set = self
            .fn_set_from_fn_set_clause(&shape.fn_set_clause)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;

        self.store_parameter_binding(&stmt.symbol_binding, ParamObjType::Identifier)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        let function_binding = self
            .visible_symbol_definition(stmt.fn_name())
            .expect("function symbol was just stored")
            .binding()
            .clone();

        let bind_infer = self
            .define_parameter_by_binding_param_type(
                &function_binding,
                &ParamType::Obj(fn_set.clone().into()),
                ParamObjType::Identifier,
            )
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        let function_identifier_obj = self.declared_identifier_obj(stmt.fn_name());
        let bind_fact: Fact = InFact::new(
            function_identifier_obj,
            fn_set.clone().into(),
            stmt.line_file.clone(),
        )
        .into();
        Self::merge_have_fn_by_forall_exist_unique_infer(&mut infer_result, bind_infer, &bind_fact);

        let property_forall = self.have_fn_by_forall_exist_unique_property_forall(stmt, &shape)?;
        let property_fact = self
            .inst_have_fn_forall_fact_for_store(property_forall)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        let property_infer = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                property_fact.clone(),
            )
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        Self::merge_have_fn_by_forall_exist_unique_infer(
            &mut infer_result,
            property_infer,
            &property_fact,
        );

        let uniqueness_forall =
            self.have_fn_by_forall_exist_unique_uniqueness_forall(stmt, &shape)?;
        let uniqueness_fact = self
            .inst_have_fn_forall_fact_for_store(uniqueness_forall)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        // Derived from the same `exist!`: if a witness satisfies the body, it is the chosen value.
        self.store_fact_without_forall_coverage_check_and_infer(uniqueness_fact)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;

        Ok(infer_result)
    }

    pub(crate) fn exec_have_fn_by_forall_exist_unique_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let shape = self.have_fn_by_forall_exist_unique_shape(stmt)?;
        let infer_result =
            self.exec_have_fn_by_forall_exist_unique_affect_environment(stmt, shape)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn have_fn_by_forall_exist_unique_shape(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<HaveFnByForallExistUniqueShape, RuntimeError> {
        // Preconditions: the source forall must already be true; every forall parameter type must
        // be an Obj; the forall must have exactly one then fact; that then fact must be an exist!;
        // and the exist! must bind exactly one Obj-typed witness. Effect: define f as a set-theoretic
        // function and store that f satisfies the witness body for each input.
        let (params_def_with_set, forall_param_to_fn_set_param) = self
            .param_groups_with_set_from_obj_param_defs(stmt, &stmt.forall.params_def_with_type)?;
        if stmt.forall.then_facts.len() != 1 {
            return Err(Self::have_fn_by_forall_exist_unique_msg(
                stmt,
                "forall must have exactly one then fact".to_string(),
            ));
        }

        let exist_body = match &stmt.forall.then_facts[0] {
            ExistOrAndChainAtomicFact::ExistFact(ExistFactEnum::ExistUniqueFact(body)) => body,
            _ => {
                return Err(Self::have_fn_by_forall_exist_unique_msg(
                    stmt,
                    "the only then fact must be an exist! fact".to_string(),
                ));
            }
        };

        if exist_body.params_def_with_type.number_of_params() != 1 {
            return Err(Self::have_fn_by_forall_exist_unique_msg(
                stmt,
                "exist! must bind exactly one witness".to_string(),
            ));
        }

        let mut witness_name = String::new();
        let mut witness_binding: Option<SymbolBinding> = None;
        let mut witness_param_type: Option<ParamType> = None;
        let mut ret_set: Option<Obj> = None;
        for group in exist_body.params_def_with_type.groups.iter() {
            match &group.param_type {
                ParamType::Obj(obj) => {
                    if !group.params.is_empty() {
                        witness_name = group.params[0].name().to_string();
                        witness_binding = Some(group.params[0].clone());
                        witness_param_type = Some(group.param_type.clone());
                        ret_set = Some(obj.clone());
                    }
                }
                _ => {
                    return Err(Self::have_fn_by_forall_exist_unique_msg(
                        stmt,
                        "exist! witness type must be Obj".to_string(),
                    ));
                }
            }
        }

        let ret_set = match ret_set {
            Some(obj) => obj,
            None => {
                return Err(Self::have_fn_by_forall_exist_unique_msg(
                    stmt,
                    "exist! must bind exactly one witness".to_string(),
                ));
            }
        };
        let witness_param_type = match witness_param_type {
            Some(param_type) => param_type,
            None => {
                return Err(Self::have_fn_by_forall_exist_unique_msg(
                    stmt,
                    "exist! must bind exactly one witness".to_string(),
                ));
            }
        };
        let witness_binding = witness_binding.expect("exist! witness binding was checked present");

        let mut dom_facts = Vec::with_capacity(stmt.forall.dom_facts.len());
        for dom_fact in stmt.forall.dom_facts.iter() {
            let rebound_dom_fact = self.inst_fact(
                dom_fact,
                &forall_param_to_fn_set_param,
                ParamObjType::BinderRetag(BinderRetagSource::Forall),
                None,
            )?;
            dom_facts.push(Self::fn_set_dom_fact_from_fact(stmt, &rebound_dom_fact)?);
        }

        for body_fact in exist_body.facts.iter() {
            if matches!(body_fact, ExistBodyFact::InlineForall(_)) {
                return Err(Self::have_fn_by_forall_exist_unique_msg(
                    stmt,
                    "exist! body cannot contain inline forall when defining a function".to_string(),
                ));
            }
        }

        Ok(HaveFnByForallExistUniqueShape {
            fn_set_clause: FnSetClause::new(params_def_with_set, dom_facts, ret_set)?,
            witness_name,
            witness_binding,
            witness_param_type,
            exist_body_facts: exist_body.facts.clone(),
        })
    }

    fn have_fn_by_forall_exist_unique_property_forall(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByForallExistUniqueShape,
    ) -> Result<ForallFact, RuntimeError> {
        let forall_param_bindings = stmt.forall.params_def_with_type.collect_param_bindings();
        let function_obj = build_declared_function_obj_with_param_bindings(
            self.declared_identifier_obj(stmt.fn_name()),
            &forall_param_bindings,
        );
        self.have_fn_by_forall_exist_unique_property_forall_with_function(stmt, shape, function_obj)
    }

    fn have_fn_by_forall_exist_unique_property_forall_with_function(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByForallExistUniqueShape,
        function_obj: Obj,
    ) -> Result<ForallFact, RuntimeError> {
        let mut witness_map = HashMap::new();
        insert_symbol_substitution(&mut witness_map, &shape.witness_binding, function_obj);

        let mut then_facts = Vec::with_capacity(shape.exist_body_facts.len());
        for body_fact in shape.exist_body_facts.iter() {
            let inst_body_fact = self
                .inst_exist_body_fact(
                    body_fact,
                    &witness_map,
                    ParamObjType::BinderRetag(BinderRetagSource::Exist),
                    Some(&stmt.line_file),
                )
                .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
            then_facts.push(Self::then_fact_from_exist_body_fact(stmt, inst_body_fact)?);
        }

        ForallFact::new_canonical_forall(
            stmt.forall.params_def_with_type.clone(),
            stmt.forall.dom_facts.clone(),
            then_facts,
            stmt.line_file.clone(),
        )
        .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))
    }

    pub(crate) fn store_instantiated_template_choice_property(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        template_obj: &InstantiatedTemplateObj,
    ) -> Result<(), RuntimeError> {
        let shape = self.have_fn_by_forall_exist_unique_shape(stmt)?;
        let forall_param_bindings = stmt.forall.params_def_with_type.collect_param_bindings();
        let head = FnObjHead::InstantiatedTemplateObj(template_obj.clone());
        let args = forall_param_bindings
            .iter()
            .map(|binding| Box::new(obj_for_bound_param_in_scope(binding, ParamObjType::Forall)))
            .collect();
        let function_obj: Obj = FnObj::new(head, vec![args]).into();
        let property_forall = self.have_fn_by_forall_exist_unique_property_forall_with_function(
            stmt,
            &shape,
            function_obj,
        )?;
        let property_fact = self
            .inst_have_fn_forall_fact_for_store(property_forall)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        self.store_fact_without_forall_coverage_check_and_infer(property_fact)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        Ok(())
    }

    fn have_fn_by_forall_exist_unique_uniqueness_forall(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByForallExistUniqueShape,
    ) -> Result<ForallFact, RuntimeError> {
        let forall_param_bindings = stmt.forall.params_def_with_type.collect_param_bindings();
        let function_obj = build_declared_function_obj_with_param_bindings(
            self.declared_identifier_obj(stmt.fn_name()),
            &forall_param_bindings,
        );
        let (witness_names, witness_map) = self.fresh_binder_retag_plan_for_bindings(
            std::slice::from_ref(&shape.witness_binding),
            ParamObjType::Forall,
        );
        let witness_obj = witness_map[&shape.witness_name].clone();

        let mut params = stmt.forall.params_def_with_type.groups.clone();
        params.push(ParamGroupWithParamType::new(
            witness_names,
            shape.witness_param_type.clone(),
        ));

        let mut dom_facts = stmt.forall.dom_facts.clone();
        for body_fact in shape.exist_body_facts.iter() {
            let inst_body_fact = self
                .inst_exist_body_fact(
                    body_fact,
                    &witness_map,
                    ParamObjType::BinderRetag(BinderRetagSource::Exist),
                    Some(&stmt.line_file),
                )
                .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
            dom_facts.push(inst_body_fact.to_fact());
        }

        let equal_fact = EqualFact::new(witness_obj, function_obj, stmt.line_file.clone());
        ForallFact::new_canonical_forall(
            ParamDefWithType::new(params),
            dom_facts,
            vec![ExistOrAndChainAtomicFact::AtomicFact(equal_fact.into())],
            stmt.line_file.clone(),
        )
        .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))
    }

    fn param_groups_with_set_from_obj_param_defs(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
        param_defs: &ParamDefWithType,
    ) -> Result<(Vec<ParamGroupWithSet>, HashMap<String, Obj>), RuntimeError> {
        let mut result = Vec::with_capacity(param_defs.groups.len());
        // The source signature uses Forall binders; its stored function type uses FnSet binders.
        let source_bindings = param_defs.collect_param_bindings();
        let (fn_set_names, full_forall_param_to_fn_set_param) =
            self.fresh_binder_retag_plan_for_bindings(&source_bindings, ParamObjType::FnSet);
        let mut forall_param_to_fn_set_param = HashMap::new();
        let mut name_index = 0;
        for group in param_defs.groups.iter() {
            match &group.param_type {
                ParamType::Obj(obj) => {
                    let rebound_param_set = self.inst_obj(
                        obj,
                        &forall_param_to_fn_set_param,
                        ParamObjType::BinderRetag(BinderRetagSource::Forall),
                    )?;
                    let group_fn_set_names =
                        fn_set_names[name_index..name_index + group.params.len()].to_vec();
                    result.push(ParamGroupWithSet::new(
                        group_fn_set_names,
                        rebound_param_set,
                    ));
                    for param_binding in group.params.iter() {
                        let param_name = param_binding.name();
                        insert_symbol_substitution(
                            &mut forall_param_to_fn_set_param,
                            param_binding,
                            full_forall_param_to_fn_set_param[param_name].clone(),
                        );
                    }
                    name_index += group.params.len();
                }
                _ => {
                    return Err(Self::have_fn_by_forall_exist_unique_msg(
                        stmt,
                        "forall parameter types must all be Obj".to_string(),
                    ));
                }
            }
        }
        Ok((result, forall_param_to_fn_set_param))
    }

    fn fn_set_dom_fact_from_fact(
        stmt: &HaveFnByForallExistUniqueStmt,
        fact: &Fact,
    ) -> Result<OrAndChainAtomicFact, RuntimeError> {
        match fact {
            Fact::AtomicFact(a) => Ok(OrAndChainAtomicFact::AtomicFact(a.clone())),
            Fact::AndFact(a) => Ok(OrAndChainAtomicFact::AndFact(a.clone())),
            Fact::ChainFact(c) => Ok(OrAndChainAtomicFact::ChainFact(c.clone())),
            Fact::OrFact(o) => Ok(OrAndChainAtomicFact::OrFact(o.clone())),
            _ => Err(Self::have_fn_by_forall_exist_unique_msg(
                stmt,
                "forall domain facts must be usable as fn domain facts".to_string(),
            )),
        }
    }

    fn then_fact_from_exist_body_fact(
        stmt: &HaveFnByForallExistUniqueStmt,
        fact: ExistBodyFact,
    ) -> Result<ExistOrAndChainAtomicFact, RuntimeError> {
        match fact {
            ExistBodyFact::AtomicFact(a) => Ok(ExistOrAndChainAtomicFact::AtomicFact(a)),
            ExistBodyFact::AndFact(a) => Ok(ExistOrAndChainAtomicFact::AndFact(a)),
            ExistBodyFact::ChainFact(c) => Ok(ExistOrAndChainAtomicFact::ChainFact(c)),
            ExistBodyFact::OrFact(o) => Ok(ExistOrAndChainAtomicFact::OrFact(o)),
            ExistBodyFact::InlineForall(_) => Err(Self::have_fn_by_forall_exist_unique_msg(
                stmt,
                "exist! body cannot contain inline forall when defining a function".to_string(),
            )),
        }
    }

    fn merge_have_fn_by_forall_exist_unique_infer(
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

    fn have_fn_by_forall_exist_unique_msg(
        stmt: &HaveFnByForallExistUniqueStmt,
        msg: String,
    ) -> RuntimeError {
        short_exec_error(
            stmt.clone().into(),
            format!("have_fn_by_forall_exist_unique: {}", msg),
            None,
            vec![],
        )
    }

    fn have_fn_by_forall_exist_unique_err(
        stmt: &HaveFnByForallExistUniqueStmt,
        cause: RuntimeError,
    ) -> RuntimeError {
        short_exec_error(
            stmt.clone().into(),
            "have_fn_by_forall_exist_unique failed".to_string(),
            Some(cause),
            vec![],
        )
    }
}
