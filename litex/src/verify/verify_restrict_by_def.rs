use crate::prelude::*;
use std::collections::HashMap;

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
        let mut original_flat_param_names: Vec<String> = Vec::new();
        for param_def_with_set in &original_fn_set.params_def_with_set {
            for param_name in param_def_with_set.0.iter() {
                original_flat_param_names.push(param_name.clone());
            }
        }

        match &restrict_fact.obj_can_restrict_to_fn_set {
            Obj::FnSetWithParams(restrict_to) => self
                .verify_restrict_to_fn_set_with_params_against_original_with_dom(
                    restrict_fact,
                    restrict_to,
                    original_fn_set,
                    &original_flat_param_names,
                    verify_state,
                ),
            Obj::FnSetWithoutParams(restrict_to) => self
                .verify_restrict_to_fn_set_without_params_against_original_with_dom(
                    restrict_fact,
                    restrict_to,
                    original_fn_set,
                    &original_flat_param_names,
                    verify_state,
                ),
            _ => Ok(None),
        }
    }

    fn verify_restrict_to_fn_set_with_params_against_original_with_dom(
        &mut self,
        restrict_fact: &RestrictFact,
        restrict_to: &FnSetWithParams,
        original_fn_set: &FnSetWithParams,
        original_flat_param_names: &Vec<String>,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        let mut restrict_flat_param_names: Vec<String> = Vec::new();
        for param_def_with_set in &restrict_to.params_def_with_set {
            for param_name in param_def_with_set.0.iter() {
                restrict_flat_param_names.push(param_name.clone());
            }
        }

        if restrict_flat_param_names.len() != original_flat_param_names.len() {
            return Ok(None);
        }

        let original_to_restrict_param_map = Self::build_original_to_restrict_param_map(
            original_flat_param_names,
            &restrict_flat_param_names,
        );

        let mut forall_params: Vec<ParamDefWithParamType> = Vec::new();
        for param_def_with_set in &restrict_to.params_def_with_set {
            forall_params.push(ParamDefWithParamType(
                param_def_with_set.0.clone(),
                ParamType::Obj(param_def_with_set.1.clone()),
            ));
        }

        let then_facts = Self::build_then_facts_for_original_with_dom(
            original_fn_set,
            &original_to_restrict_param_map,
            &restrict_flat_param_names,
            &(*restrict_to.ret_set).clone(),
            restrict_fact.line_file,
        );

        self.verify_forall_and_return_restrict_success(
            restrict_fact,
            forall_params,
            then_facts,
            verify_state,
        )
    }

    fn verify_restrict_to_fn_set_without_params_against_original_with_dom(
        &mut self,
        restrict_fact: &RestrictFact,
        restrict_to: &FnSetWithoutParams,
        original_fn_set: &FnSetWithParams,
        original_flat_param_names: &Vec<String>,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        if restrict_to.param_sets.len() != original_flat_param_names.len() {
            return Ok(None);
        }

        let mut generated_param_names: Vec<String> =
            Vec::with_capacity(restrict_to.param_sets.len());
        let mut slot_index: usize = 0;
        while slot_index < restrict_to.param_sets.len() {
            generated_param_names.push(self.generate_a_random_unused_name());
            slot_index += 1;
        }

        let original_to_restrict_param_map = Self::build_original_to_restrict_param_map(
            original_flat_param_names,
            &generated_param_names,
        );

        let mut forall_params: Vec<ParamDefWithParamType> = Vec::new();
        let mut slot_index: usize = 0;
        while slot_index < generated_param_names.len() {
            forall_params.push(ParamDefWithParamType(
                vec![generated_param_names[slot_index].clone()],
                ParamType::Obj((*restrict_to.param_sets[slot_index]).clone()),
            ));
            slot_index += 1;
        }

        let then_facts = Self::build_then_facts_for_original_with_dom(
            original_fn_set,
            &original_to_restrict_param_map,
            &generated_param_names,
            &(*restrict_to.ret_set).clone(),
            restrict_fact.line_file,
        );

        self.verify_forall_and_return_restrict_success(
            restrict_fact,
            forall_params,
            then_facts,
            verify_state,
        )
    }

    fn build_original_to_restrict_param_map(
        original_flat_param_names: &Vec<String>,
        restrict_flat_param_names: &Vec<String>,
    ) -> HashMap<String, Obj> {
        let mut original_to_restrict_param_map: HashMap<String, Obj> = HashMap::new();
        let mut mapping_index: usize = 0;
        while mapping_index < original_flat_param_names.len() {
            original_to_restrict_param_map.insert(
                original_flat_param_names[mapping_index].clone(),
                Obj::Identifier(Identifier::new(
                    restrict_flat_param_names[mapping_index].clone(),
                )),
            );
            mapping_index += 1;
        }
        original_to_restrict_param_map
    }

    fn build_then_facts_for_original_with_dom(
        original_fn_set: &FnSetWithParams,
        original_to_restrict_param_map: &HashMap<String, Obj>,
        restrict_flat_param_names: &Vec<String>,
        restrict_ret_set: &Obj,
        line_file: (usize, usize),
    ) -> Vec<ExistOrAndChainAtomicFact> {
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        let mut index: usize = 0;
        for param_def_with_set in &original_fn_set.params_def_with_set {
            let instantiated_original_set = param_def_with_set
                .1
                .instantiate(original_to_restrict_param_map);
            for _param_name in param_def_with_set.0.iter() {
                let restrict_param_name = restrict_flat_param_names[index].clone();
                then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                    InFact::new(
                        Obj::Identifier(Identifier::new(restrict_param_name)),
                        instantiated_original_set.clone(),
                        line_file,
                    ),
                )));
                index += 1;
            }
        }

        for dom_fact in &original_fn_set.dom_facts {
            let instantiated_dom_fact = dom_fact.instantiate(original_to_restrict_param_map);
            then_facts.push(instantiated_dom_fact.to_exist_or_and_chain_atomic_fact());
        }

        let instantiated_original_ret_set = original_fn_set
            .ret_set
            .instantiate(original_to_restrict_param_map);
        then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(
            AtomicFact::EqualFact(EqualFact::new(
                restrict_ret_set.clone(),
                instantiated_original_ret_set,
                line_file,
            )),
        ));

        then_facts
    }

    fn verify_forall_and_return_restrict_success(
        &mut self,
        restrict_fact: &RestrictFact,
        forall_params: Vec<ParamDefWithParamType>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        let params_in_original_sets_forall =
            ForallFact::new(forall_params, vec![], then_facts, restrict_fact.line_file);
        let forall_result =
            self.verify_forall_fact(&params_in_original_sets_forall, verify_state)?;
        if !forall_result.is_true() {
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
            _ => return Ok(None),
        }
    }
}
