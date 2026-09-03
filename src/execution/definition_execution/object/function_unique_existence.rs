use crate::prelude::*;
use std::collections::HashMap;

use super::function_equality_support::build_defined_function_obj_with_parameter_bindings;

struct HaveFnByForallExistUniqueShape {
    fn_set_clause: FnSetClause,
    witness_name: String,
    witness_binding: SymbolBinding,
    witness_param_type: ParamType,
    quantifier_free_facts: Vec<QuantifierFreeFact>,
}

impl Runtime {
    pub fn exec_have_fn_by_forall_exist_unique_stmt(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let (shape, well_definedness) =
            self.exec_have_fn_by_forall_exist_unique_verify_well_definedness(stmt)?;
        let verification =
            self.exec_have_fn_by_forall_exist_unique_verify_process(stmt, well_definedness)?;
        let (infer_result, published_property_well_definedness) =
            self.exec_have_fn_by_forall_exist_unique_affect_environment(stmt, shape)?;

        Ok(
            SuccessDefinitionStmtResult::HaveFnByForallExistUniqueStmt(Box::new(
                SuccessHaveFnByForallExistUniqueStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(verification),
                    published_property_well_definedness: Some(published_property_well_definedness),
                },
            ))
            .into(),
        )
    }

    /// Mathematical contract: choice of a function from unique existence is
    /// meaningful only when the source universal-existential statement and
    /// its derived function signature are structurally valid and the complete
    /// quantified fact is well-defined.
    fn exec_have_fn_by_forall_exist_unique_verify_well_definedness(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<(HaveFnByForallExistUniqueShape, WellDefinedFactResult), RuntimeError> {
        let shape = self.have_fn_by_forall_exist_unique_shape(stmt)?;
        let well_definedness = self
            .verify_fact_well_defined_result(
                &Fact::ForallFact(stmt.forall.clone()),
                &VerifyState::initial(),
            )
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "have_fn_by_forall_exist_unique: forall fact is not well defined".to_string(),
                    Some(e),
                    vec![],
                )
            })?;
        Ok((shape, well_definedness))
    }

    fn exec_have_fn_by_forall_exist_unique_verify_process(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        well_definedness: WellDefinedFactResult,
    ) -> Result<SuccessVerifyFunctionFromUniqueExistenceResult, RuntimeError> {
        if stmt.prove_process.is_empty() {
            let forall_fact: Fact = stmt.forall.clone().into();
            let mut result = self
                .verify_fact_or_error(&forall_fact, &VerifyState::initial())
                .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
            self.attach_known_fact_ids_to_verify_fact_result(&mut result)?;
            Ok(SuccessVerifyFunctionFromUniqueExistenceResult::new(
                well_definedness,
                SuccessVerifyLocalProofScopeResult::new(SuccessInferResult::new(), Vec::new()),
                Some(result),
                vec![],
                vec![],
            ))
        } else {
            self.exec_have_fn_by_forall_exist_unique_prove_process(stmt, well_definedness)
        }
    }

    fn exec_have_fn_by_forall_exist_unique_prove_process(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        well_definedness: WellDefinedFactResult,
    ) -> Result<SuccessVerifyFunctionFromUniqueExistenceResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let mut assumption_infers = rt
                .define_params_with_type(
                    &stmt.forall.typed_parameters,
                    false,
                    BindingScope::LocalBinder,
                )
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;

            for dom_fact in stmt.forall.dom_facts.iter() {
                let mut domain_infers = rt.store_with_well_defined_verification_and_infer(
                    dom_fact.clone(),
                    &VerifyState::initial(),
                )?;
                domain_infers
                    .relabel_all_added_facts_with_store_reason(ForallFact::premise_store_reason());
                assumption_infers.new_infer_result_inside(domain_infers);
            }

            let mut proof_steps = vec![];
            let proof_len = stmt.prove_process.len();
            for (proof_index, proof_stmt) in stmt.prove_process.iter().enumerate() {
                let result = rt.execute_statement(proof_stmt)?;
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
                proof_steps.push(result);
            }

            let mut conclusion_checks = Vec::new();
            let then_count = stmt.forall.then_facts.len();
            let then_verify_state = VerifyState::initial();
            for (then_index, then_fact) in stmt.forall.then_facts.iter().enumerate() {
                let then_goal = then_fact.clone().to_fact();
                let result = rt.verify_fact_allow_unknown(&then_goal, &then_verify_state)?;
                if result.is_unknown() {
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
                            RuntimeErrorOutput::then_clause_unknown_fact(
                                then_goal,
                                then_index + 1,
                                then_count,
                                result
                                    .as_fact_unknown()
                                    .expect("unknown fact verification carries an unknown result"),
                            ),
                        ),
                    )));
                }
                conclusion_checks.push(result);
            }

            rt.attach_known_fact_ids_to_infer_result(&mut assumption_infers)?;
            for result in proof_steps.iter_mut() {
                rt.attach_known_fact_ids_to_stmt_result(result)?;
            }
            for result in conclusion_checks.iter_mut() {
                rt.attach_known_fact_ids_to_verify_fact_result(result)?;
            }

            Ok(SuccessVerifyFunctionFromUniqueExistenceResult::new(
                well_definedness,
                SuccessVerifyLocalProofScopeResult::new(assumption_infers, Vec::new()),
                None,
                proof_steps,
                conclusion_checks,
            ))
        })
    }

    fn exec_have_fn_by_forall_exist_unique_affect_environment(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: HaveFnByForallExistUniqueShape,
    ) -> Result<(SuccessInferResult, WellDefinedFactResult), RuntimeError> {
        let mut infer_result = SuccessInferResult::new();
        let fn_set = self
            .fn_set_from_fn_set_clause(&shape.fn_set_clause)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;

        self.store_parameter_binding(&stmt.symbol_binding, BindingScope::DefinitionBinding)
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
                BindingScope::DefinitionBinding,
            )
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        let function_identifier_obj = self.definition_identifier_obj(stmt.fn_name());
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
        let published_property_well_definedness = self
            .verify_fact_well_defined_result(&property_fact, &VerifyState::initial())
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

        Ok((infer_result, published_property_well_definedness))
    }

    pub fn exec_have_fn_by_forall_exist_unique_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let shape = self.have_fn_by_forall_exist_unique_shape(stmt)?;
        let (infer_result, _) =
            self.exec_have_fn_by_forall_exist_unique_affect_environment(stmt, shape)?;
        Ok(
            SuccessDefinitionStmtResult::HaveFnByForallExistUniqueStmt(Box::new(
                SuccessHaveFnByForallExistUniqueStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                    published_property_well_definedness: None,
                },
            ))
            .into(),
        )
    }

    fn have_fn_by_forall_exist_unique_shape(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<HaveFnByForallExistUniqueShape, RuntimeError> {
        // Preconditions: the source forall must already be true; every forall parameter type must
        // be an Obj; the forall must have exactly one then fact; that then fact must be an exist!;
        // and the exist! must bind exactly one Obj-typed witness. Effect: define f as a set-theoretic
        // function and store that f satisfies the witness body for each input.
        let (set_bound_parameters, forall_param_to_fn_set_param) =
            self.param_groups_with_set_from_obj_param_defs(stmt, &stmt.forall.typed_parameters)?;
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

        if exist_body.typed_parameters.number_of_params() != 1 {
            return Err(Self::have_fn_by_forall_exist_unique_msg(
                stmt,
                "exist! must bind exactly one witness".to_string(),
            ));
        }

        let mut witness_name = String::new();
        let mut witness_binding: Option<SymbolBinding> = None;
        let mut witness_param_type: Option<ParamType> = None;
        let mut ret_set: Option<Obj> = None;
        for group in exist_body.typed_parameters.groups.iter() {
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
                SubstitutionMode::Exact,
                None,
            )?;
            dom_facts.push(Self::fn_set_dom_fact_from_fact(stmt, &rebound_dom_fact)?);
        }

        Ok(HaveFnByForallExistUniqueShape {
            fn_set_clause: FnSetClause::new(set_bound_parameters, dom_facts, ret_set)?,
            witness_name,
            witness_binding,
            witness_param_type,
            quantifier_free_facts: exist_body.facts.clone(),
        })
    }

    pub fn direct_fn_set_body_for_have_fn_by_forall_exist_unique(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<FnSetBody, RuntimeError> {
        let clause = self
            .have_fn_by_forall_exist_unique_shape(stmt)?
            .fn_set_clause;
        Ok(FnSetBody::new(
            clause.set_bound_parameters,
            clause.dom_facts,
            clause.ret_set,
        ))
    }

    /// Return the exact function-property theorem stored by
    /// `have fn ... by exist!`.  The Result-to-Lean compiler uses this
    /// constructor to validate that the two published outer effects are the
    /// function membership and the property derived from the same source
    /// `exist!`; it must not infer that relationship from names or output
    /// order alone.
    pub fn direct_property_forall_for_have_fn_by_forall_exist_unique(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
    ) -> Result<ForallFact, RuntimeError> {
        let shape = self.have_fn_by_forall_exist_unique_shape(stmt)?;
        let forall_param_bindings = stmt.forall.typed_parameters.collect_param_bindings();
        let function_obj = build_defined_function_obj_with_parameter_bindings(
            Identifier::new_bound(stmt.fn_name().to_string(), stmt.symbol_binding.as_ref()).into(),
            &forall_param_bindings,
        );
        self.have_fn_by_forall_exist_unique_property_forall_with_function(
            stmt,
            &shape,
            function_obj,
        )
    }

    fn have_fn_by_forall_exist_unique_property_forall(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByForallExistUniqueShape,
    ) -> Result<ForallFact, RuntimeError> {
        let forall_param_bindings = stmt.forall.typed_parameters.collect_param_bindings();
        let function_obj = build_defined_function_obj_with_parameter_bindings(
            self.definition_identifier_obj(stmt.fn_name()),
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

        let mut then_facts = Vec::with_capacity(shape.quantifier_free_facts.len());
        for body_fact in shape.quantifier_free_facts.iter() {
            let inst_body_fact = self
                .inst_quantifier_free_fact(
                    body_fact,
                    &witness_map,
                    SubstitutionMode::Exact,
                    Some(&stmt.line_file),
                )
                .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
            then_facts.push(Self::then_fact_from_quantifier_free_fact(inst_body_fact));
        }

        ForallFact::new_canonical_forall(
            stmt.forall.typed_parameters.clone(),
            stmt.forall.dom_facts.clone(),
            then_facts,
            stmt.line_file.clone(),
        )
        .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))
    }

    pub fn store_instantiated_template_choice_property(
        &mut self,
        stmt: &HaveFnByForallExistUniqueStmt,
        template_obj: &InstantiatedTemplateObj,
    ) -> Result<SuccessStoreFactResult, RuntimeError> {
        let shape = self.have_fn_by_forall_exist_unique_shape(stmt)?;
        let forall_param_bindings = stmt.forall.typed_parameters.collect_param_bindings();
        let head = FnObjHead::InstantiatedTemplateObj(template_obj.clone());
        let args = forall_param_bindings
            .iter()
            .map(|binding| Box::new(obj_for_bound_param_in_scope(binding)))
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
        let fact = property_fact.clone();
        let mut infers = self
            .store_fact_without_forall_coverage_check_and_infer(property_fact)
            .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        Ok(SuccessStoreFactResult {
            fact: fact.clone(),
            fact_id: self.known_fact_id_for_fact(&fact)?,
            infers,
        })
    }

    fn have_fn_by_forall_exist_unique_uniqueness_forall(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
        shape: &HaveFnByForallExistUniqueShape,
    ) -> Result<ForallFact, RuntimeError> {
        let forall_param_bindings = stmt.forall.typed_parameters.collect_param_bindings();
        let function_obj = build_defined_function_obj_with_parameter_bindings(
            self.definition_identifier_obj(stmt.fn_name()),
            &forall_param_bindings,
        );
        let (witness_names, witness_map) =
            self.fresh_binder_retag_plan_for_bindings(std::slice::from_ref(&shape.witness_binding));
        let witness_obj = witness_map[&shape.witness_name].clone();

        let mut params = stmt.forall.typed_parameters.groups.clone();
        params.push(TypedParameterGroup::new(
            witness_names,
            shape.witness_param_type.clone(),
        ));

        let mut dom_facts = stmt.forall.dom_facts.clone();
        for body_fact in shape.quantifier_free_facts.iter() {
            let inst_body_fact = self
                .inst_quantifier_free_fact(
                    body_fact,
                    &witness_map,
                    SubstitutionMode::Exact,
                    Some(&stmt.line_file),
                )
                .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))?;
            dom_facts.push(inst_body_fact.to_fact());
        }

        let equal_fact = EqualFact::new(witness_obj, function_obj, stmt.line_file.clone());
        ForallFact::new_canonical_forall(
            TypedParameterList::new(params),
            dom_facts,
            vec![ExistOrAndChainAtomicFact::AtomicFact(equal_fact.into())],
            stmt.line_file.clone(),
        )
        .map_err(|e| Self::have_fn_by_forall_exist_unique_err(stmt, e))
    }

    fn param_groups_with_set_from_obj_param_defs(
        &self,
        stmt: &HaveFnByForallExistUniqueStmt,
        param_defs: &TypedParameterList,
    ) -> Result<(Vec<SetBoundParameterGroup>, HashMap<String, Obj>), RuntimeError> {
        let mut result = Vec::with_capacity(param_defs.groups.len());
        // The source signature uses Forall binders; its stored function type uses FnSet binders.
        let source_bindings = param_defs.collect_param_bindings();
        let (fn_set_names, full_forall_param_to_fn_set_param) =
            self.fresh_binder_retag_plan_for_bindings(&source_bindings);
        let mut forall_param_to_fn_set_param = HashMap::new();
        let mut name_index = 0;
        for group in param_defs.groups.iter() {
            match &group.param_type {
                ParamType::Obj(obj) => {
                    let rebound_param_set =
                        self.inst_obj(obj, &forall_param_to_fn_set_param, SubstitutionMode::Exact)?;
                    let group_fn_set_names =
                        fn_set_names[name_index..name_index + group.params.len()].to_vec();
                    result.push(SetBoundParameterGroup::new(
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
    ) -> Result<QuantifierFreeFact, RuntimeError> {
        match fact {
            Fact::AtomicFact(a) => Ok(QuantifierFreeFact::AtomicFact(a.clone())),
            Fact::AndFact(a) => Ok(QuantifierFreeFact::AndFact(a.clone())),
            Fact::ChainFact(c) => Ok(QuantifierFreeFact::ChainFact(c.clone())),
            Fact::OrFact(o) => Ok(QuantifierFreeFact::OrFact(o.clone())),
            _ => Err(Self::have_fn_by_forall_exist_unique_msg(
                stmt,
                "forall domain facts must be usable as fn domain facts".to_string(),
            )),
        }
    }

    fn then_fact_from_quantifier_free_fact(fact: QuantifierFreeFact) -> ExistOrAndChainAtomicFact {
        match fact {
            QuantifierFreeFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            QuantifierFreeFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
            QuantifierFreeFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
            QuantifierFreeFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
        }
    }

    fn merge_have_fn_by_forall_exist_unique_infer(
        infer_result: &mut SuccessInferResult,
        store_infer: SuccessInferResult,
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
