use crate::prelude::*;

impl Runtime {
    pub fn verify_restrict_fact_using_its_definition(
        &mut self,
        restrict_fact: &RestrictFact,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        let function = &restrict_fact.obj;

        let function_set = self.get_cloned_fn_set_where_fn_belongs_to(function);

        match function_set {
            Some(fn_set) => match fn_set {
                FnSetObj::FnSetWithDom(fn_set_with_dom) => {
                    return self.verify_restrict_fact_with_fn_set_with_dom(
                        restrict_fact,
                        &fn_set_with_dom,
                        verify_state,
                    );
                }
                FnSetObj::FnSetWithoutParams(fn_set_without_dom) => {
                    return self.verify_restrict_fact_with_fn_set_without_dom(
                        restrict_fact,
                        &fn_set_without_dom,
                        verify_state,
                    );
                }
            },
            None => {
                return Err(VerifyError::new(
                    Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                    String::new(),
                    restrict_fact.line_file,
                    Some(RuntimeError::WellDefinedError(WellDefinedError::new(
                        format!(
                            "function `{}` belongs to what function set is unknown",
                            function.to_string()
                        ),
                        None,
                        DEFAULT_LINE_FILE.clone(),
                    ))),
                ));
            }
        }
    }

    fn verify_restrict_fact_with_fn_set_with_dom(
        &mut self,
        restrict_fact: &RestrictFact,
        original_fn_set: &FnSetWithParams,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        let restrict_to = match &restrict_fact.obj_can_restrict_to_fn_set {
            Obj::FnSetWithParams(fn_set_with_params) => fn_set_with_params.clone(),
            _ => return Ok(None),
        };

        if !restrict_to.dom_facts.is_empty() {
            return Ok(None);
        }

        let mut original_flat_param_sets: Vec<Obj> = Vec::new();
        for param_def_with_set in &original_fn_set.params_def_with_set {
            for _param_name in param_def_with_set.0.iter() {
                original_flat_param_sets.push(param_def_with_set.1.clone());
            }
        }

        let mut restrict_flat_param_names: Vec<String> = Vec::new();
        for param_def_with_set in &restrict_to.params_def_with_set {
            for param_name in param_def_with_set.0.iter() {
                restrict_flat_param_names.push(param_name.clone());
            }
        }

        if restrict_flat_param_names.len() != original_flat_param_sets.len() {
            return Ok(None);
        }

        let mut forall_params: Vec<ParamDefWithParamType> = Vec::new();
        for param_def_with_set in &restrict_to.params_def_with_set {
            forall_params.push(ParamDefWithParamType(
                param_def_with_set.0.clone(),
                ParamType::Obj(param_def_with_set.1.clone()),
            ));
        }

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        let mut index: usize = 0;
        while index < restrict_flat_param_names.len() {
            let param_name = restrict_flat_param_names[index].clone();
            let original_set = original_flat_param_sets[index].clone();
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact::new(
                    Obj::Identifier(Identifier::new(param_name)),
                    original_set,
                    restrict_fact.line_file,
                ),
            )));
            index += 1;
        }

        let params_in_original_sets_forall =
            ForallFact::new(forall_params, vec![], then_facts, restrict_fact.line_file);
        let forall_result =
            self.verify_forall_fact(&params_in_original_sets_forall, verify_state)?;
        if !forall_result.is_true() {
            return Ok(None);
        }

        let ret_equal_fact = EqualFact::new(
            (*restrict_to.ret_set).clone(),
            (*original_fn_set.ret_set).clone(),
            restrict_fact.line_file,
        );
        let ret_equal_result = self.verify_equal_fact(&ret_equal_fact, verify_state)?;
        if !ret_equal_result.is_true() {
            return Ok(None);
        }

        Ok(Some(NonErrStmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules(
                Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                InferResult::new(),
                "restrict by definition (forall param sets narrower, same ret set)".to_string(),
                Vec::new(),
            ),
        )))
    }

    fn verify_restrict_fact_with_fn_set_without_dom(
        &mut self,
        restrict_fact: &RestrictFact,
        original_fn_set: &FnSetWithoutParams,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        match &restrict_fact.obj_can_restrict_to_fn_set {
            Obj::FnSetWithParams(restrict_to) => {
                let mut restrict_flat_param_names: Vec<String> = Vec::new();
                for param_def_with_set in &restrict_to.params_def_with_set {
                    for param_name in param_def_with_set.0.iter() {
                        restrict_flat_param_names.push(param_name.clone());
                    }
                }

                if restrict_flat_param_names.len() != original_fn_set.param_sets.len() {
                    return Ok(None);
                }

                let mut forall_params: Vec<ParamDefWithParamType> = Vec::new();
                for param_def_with_set in &restrict_to.params_def_with_set {
                    forall_params.push(ParamDefWithParamType(
                        param_def_with_set.0.clone(),
                        ParamType::Obj(param_def_with_set.1.clone()),
                    ));
                }

                let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
                let mut index: usize = 0;
                while index < restrict_flat_param_names.len() {
                    let param_name = restrict_flat_param_names[index].clone();
                    let original_set = (*original_fn_set.param_sets[index]).clone();
                    then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                        InFact::new(
                            Obj::Identifier(Identifier::new(param_name)),
                            original_set,
                            restrict_fact.line_file,
                        ),
                    )));
                    index += 1;
                }

                let params_in_original_sets_forall =
                    ForallFact::new(forall_params, vec![], then_facts, restrict_fact.line_file);
                let forall_result =
                    self.verify_forall_fact(&params_in_original_sets_forall, verify_state)?;
                if !forall_result.is_true() {
                    return Ok(None);
                }

                let ret_equal_fact = EqualFact::new(
                    (*restrict_to.ret_set).clone(),
                    (*original_fn_set.ret_set).clone(),
                    restrict_fact.line_file,
                );
                let ret_equal_result = self.verify_equal_fact(&ret_equal_fact, verify_state)?;
                if !ret_equal_result.is_true() {
                    return Ok(None);
                }

                Ok(Some(NonErrStmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules(
                        Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                        InferResult::new(),
                        "restrict by definition (forall param sets narrower, same ret set)"
                            .to_string(),
                        Vec::new(),
                    ),
                )))
            }
            Obj::FnSetWithoutParams(restrict_to) => {
                if restrict_to.param_sets.len() != original_fn_set.param_sets.len() {
                    return Ok(None);
                }

                let mut generated_param_names: Vec<String> =
                    Vec::with_capacity(restrict_to.param_sets.len());
                let mut slot_index: usize = 0;
                while slot_index < restrict_to.param_sets.len() {
                    generated_param_names.push(self.generate_a_random_unused_name());
                    slot_index += 1;
                }

                let mut forall_params: Vec<ParamDefWithParamType> = Vec::new();
                let mut slot_index: usize = 0;
                while slot_index < generated_param_names.len() {
                    forall_params.push(ParamDefWithParamType(
                        vec![generated_param_names[slot_index].clone()],
                        ParamType::Obj((*restrict_to.param_sets[slot_index]).clone()),
                    ));
                    slot_index += 1;
                }

                let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
                let mut slot_index: usize = 0;
                while slot_index < generated_param_names.len() {
                    let param_name = generated_param_names[slot_index].clone();
                    let original_set = (*original_fn_set.param_sets[slot_index]).clone();
                    then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                        InFact::new(
                            Obj::Identifier(Identifier::new(param_name)),
                            original_set,
                            restrict_fact.line_file,
                        ),
                    )));
                    slot_index += 1;
                }

                let params_in_original_sets_forall = ForallFact::new(
                    forall_params,
                    vec![],
                    then_facts,
                    restrict_fact.line_file,
                );
                let forall_result =
                    self.verify_forall_fact(&params_in_original_sets_forall, verify_state)?;
                if !forall_result.is_true() {
                    return Ok(None);
                }

                let ret_equal_fact = EqualFact::new(
                    (*restrict_to.ret_set).clone(),
                    (*original_fn_set.ret_set).clone(),
                    restrict_fact.line_file,
                );
                let ret_equal_result = self.verify_equal_fact(&ret_equal_fact, verify_state)?;
                if !ret_equal_result.is_true() {
                    return Ok(None);
                }

                Ok(Some(NonErrStmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules(
                        Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                        InferResult::new(),
                        "restrict by definition (forall param sets narrower, same ret set)"
                            .to_string(),
                        Vec::new(),
                    ),
                )))
            }
            _ => return Ok(None),
        }
    }
}
