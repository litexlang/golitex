use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn verify_restrict_fact_using_its_definition(
        &mut self,
        restrict_fact: &RestrictFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let function = &restrict_fact.obj;

        let original_fn_set =
            match self.get_cloned_object_in_fn_set(function) {
                Some(fn_set) => fn_set,
                None => {
                    return Err(RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                    Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                    String::new(),
                    restrict_fact.line_file.clone(),
                    Some(RuntimeError::new_well_defined_error_with_msg_previous_error_position(
                        format!(
                            "function `{}` belongs to what function set is unknown",
                            function.to_string()
                        ),
                        None,
                        default_line_file(),
                    )),
                ));
                }
            };

        self.verify_restrict_to_fn_set_with_params_against_original_with_params(
            restrict_fact,
            &original_fn_set,
            verify_state,
        )
    }

    fn verify_restrict_to_fn_set_with_params_against_original_with_params(
        &mut self,
        restrict_fact: &RestrictFact,
        original_fn_set: &FnSet,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let restrict_to_ref = match &restrict_fact.obj_can_restrict_to_fn_set {
            Obj::FnSet(r) => r,
            _ => return Ok(None),
        };

        let mut restrict_flat_param_names: Vec<String> = Vec::new();
        for param_def_with_set in &restrict_to_ref.params_def_with_set {
            for param_name in param_def_with_set.params.iter() {
                restrict_flat_param_names.push(param_name.clone());
            }
        }

        let mut original_flat_param_names: Vec<String> = Vec::new();
        for param_def_with_set in &original_fn_set.params_def_with_set {
            for param_name in param_def_with_set.params.iter() {
                original_flat_param_names.push(param_name.clone());
            }
        }

        if restrict_flat_param_names.len() != original_flat_param_names.len() {
            return Ok(None);
        }

        let original_to_restrict_param_map = Self::build_original_to_restrict_param_map(
            &original_flat_param_names,
            &restrict_flat_param_names,
        );

        let mut forall_params: Vec<ParamGroupWithParamType> = Vec::new();
        for param_def_with_set in &restrict_to_ref.params_def_with_set {
            forall_params.push(ParamGroupWithParamType::new(
                param_def_with_set.params.clone(),
                ParamType::Obj(param_def_with_set.set.clone()),
            ));
        }

        let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        for dom_fact in &restrict_to_ref.dom_facts {
            forall_dom_facts.push(dom_fact.clone().to_exist_or_and_chain_atomic_fact());
        }

        let then_facts = Self::build_then_facts_for_original_with_params(
            self,
            original_fn_set,
            &original_to_restrict_param_map,
            &restrict_flat_param_names,
            restrict_fact.line_file.clone(),
        )
        .map_err(|e| {
            RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                String::new(),
                restrict_fact.line_file.clone(),
                Some(e),
            )
        })?;

        self.verify_forall_and_return_restrict_success(
            restrict_fact,
            forall_params,
            forall_dom_facts,
            then_facts,
            &(*restrict_to_ref.ret_set).clone(),
            &(*original_fn_set.ret_set).clone(),
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
                restrict_flat_param_names[mapping_index].clone().into(),
            );
            mapping_index += 1;
        }
        original_to_restrict_param_map
    }

    fn build_then_facts_for_original_with_params(
        runtime: &Runtime,
        original_fn_set: &FnSet,
        original_to_restrict_param_map: &HashMap<String, Obj>,
        restrict_flat_param_names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<Vec<ExistOrAndChainAtomicFact>, RuntimeError> {
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        let mut index: usize = 0;
        for param_def_with_set in &original_fn_set.params_def_with_set {
            let instantiated_original_set =
                runtime.inst_obj(&param_def_with_set.set, original_to_restrict_param_map)?;
            for _param_name in param_def_with_set.params.iter() {
                let restrict_param_name = restrict_flat_param_names[index].clone();
                then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                    InFact::new(
                        restrict_param_name.into(),
                        instantiated_original_set.clone(),
                        line_file.clone(),
                    ),
                )));
                index += 1;
            }
        }

        for dom_fact in &original_fn_set.dom_facts {
            let instantiated_dom_fact =
                runtime.inst_or_and_chain_atomic_fact(dom_fact, original_to_restrict_param_map)?;
            then_facts.push(instantiated_dom_fact.to_exist_or_and_chain_atomic_fact());
        }

        Ok(then_facts)
    }

    fn verify_forall_and_return_restrict_success(
        &mut self,
        restrict_fact: &RestrictFact,
        forall_params: Vec<ParamGroupWithParamType>,
        forall_dom_facts: Vec<ExistOrAndChainAtomicFact>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        restrict_ret_set: &Obj,
        original_ret_set: &Obj,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let params_in_original_sets_forall = ForallFact::new(
            forall_params,
            forall_dom_facts,
            then_facts,
            restrict_fact.line_file.clone(),
        );
        let forall_result =
            self.verify_forall_fact(&params_in_original_sets_forall, verify_state)?;
        if !forall_result.is_true() {
            return Ok(None);
        }

        let ret_equal_fact = EqualFact::new(
            restrict_ret_set.clone(),
            original_ret_set.clone(),
            restrict_fact.line_file.clone(),
        );
        let ret_equal_result = self.verify_equal_fact(&ret_equal_fact, verify_state)?;
        if !ret_equal_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                "restrict by definition (forall param sets narrower, same ret set)".to_string(),
                Vec::new(),
            ))
            .into(),
        ))
    }
}
