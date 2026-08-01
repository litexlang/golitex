use crate::prelude::*;
use std::collections::HashMap;

struct FnMembershipProofFlow {
    in_fact: InFact,
    forall_params: ParamDefWithType,
    forall_dom_facts: Vec<Fact>,
    pointwise_ret_set: Obj,
    applied_fn_obj: Obj,
}

impl Runtime {
    /// A named function with the same input signature belongs to a narrower
    /// function space when its values are known to lie in the target return set.
    /// Example: `forall x I: f(x) $in X` proves `f $in fn(x I) X`.
    pub fn verify_in_fact_element_in_fn_set_by_pointwise_values(
        &mut self,
        element: &Obj,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(flow) = self.build_fn_membership_proof_flow(element, expected_fn_set, in_fact)?
        else {
            return Ok(None);
        };

        self.verify_fn_membership_application_well_defined(&flow, verify_state)?;

        let then_facts = vec![InFact::new(
            flow.applied_fn_obj.clone(),
            flow.pointwise_ret_set,
            flow.in_fact.line_file.clone(),
        )
        .into()];
        let forall = ForallFact::new(
            flow.forall_params,
            flow.forall_dom_facts,
            then_facts,
            flow.in_fact.line_file.clone(),
        )?;
        let forall_result = self.verify_forall_fact(&forall, verify_state)?;
        if !forall_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                flow.in_fact.into(),
                "fn membership: same input domain and pointwise values lie in the target return set"
                    .to_string(),
                Vec::new(),
            ))
            .into(),
        ))
    }

    fn build_fn_membership_proof_flow(
        &mut self,
        element: &Obj,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
    ) -> Result<Option<FnMembershipProofFlow>, RuntimeError> {
        let Some(known_fn_body) = self.get_cloned_object_in_fn_set(element) else {
            return Ok(None);
        };
        let expected_flat_param_names = Self::collect_fn_param_names(&expected_fn_set.body);
        let known_flat_param_names = Self::collect_fn_param_names(&known_fn_body);
        if expected_flat_param_names.len() != known_flat_param_names.len() {
            return Ok(None);
        }
        if !self.fn_inputs_match_expected_fn_set(&known_fn_body, expected_fn_set)? {
            return Ok(None);
        }

        let Some(fn_head) = FnObjHead::given_an_atom_return_a_fn_obj_head(element.clone()) else {
            return Ok(None);
        };
        let expected_flat_param_bindings = expected_fn_set
            .body
            .params_def_with_set
            .iter()
            .flat_map(|group| group.params.iter().cloned())
            .collect::<Vec<_>>();
        let (forall_param_names, full_param_to_forall_obj) = self
            .fresh_binder_retag_plan_for_bindings(
                &expected_flat_param_bindings,
                ParamObjType::Forall,
            );
        let mut active_param_to_forall_obj = HashMap::new();
        let mut forall_param_type_groups = Vec::new();
        let mut name_index = 0;
        for group in expected_fn_set.body.params_def_with_set.iter() {
            let param_set = self.inst_obj(
                group.set_obj(),
                &active_param_to_forall_obj,
                ParamObjType::BinderRetag(BinderRetagSource::FnSet),
            )?;
            let group_forall_names =
                forall_param_names[name_index..name_index + group.params.len()].to_vec();
            forall_param_type_groups.push(ParamGroupWithParamType::new(
                group_forall_names,
                ParamType::Obj(param_set),
            ));
            for binding in group.params.iter() {
                insert_symbol_substitution(
                    &mut active_param_to_forall_obj,
                    binding,
                    full_param_to_forall_obj[&binding.substitution_key()].clone(),
                );
            }
            name_index += group.params.len();
        }
        let mut forall_dom_facts = Vec::with_capacity(expected_fn_set.body.dom_facts.len());
        for fact in expected_fn_set.body.dom_facts.iter() {
            forall_dom_facts.push(
                self.inst_or_and_chain_atomic_fact(
                    fact,
                    &full_param_to_forall_obj,
                    ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                    None,
                )?
                .into(),
            );
        }
        let pointwise_ret_set = self.inst_obj(
            expected_fn_set.body.ret_set.as_ref(),
            &full_param_to_forall_obj,
            ParamObjType::BinderRetag(BinderRetagSource::FnSet),
        )?;
        let applied_fn_obj: Obj = FnObj::new(
            fn_head,
            Self::build_full_application_arg_groups(&known_fn_body, &forall_param_names),
        )
        .into();

        Ok(Some(FnMembershipProofFlow {
            in_fact: in_fact.clone(),
            forall_params: ParamDefWithType::new(forall_param_type_groups),
            forall_dom_facts,
            pointwise_ret_set,
            applied_fn_obj,
        }))
    }

    fn fn_inputs_match_expected_fn_set(
        &mut self,
        known_fn_body: &FnSetBody,
        expected_fn_set: &FnSet,
    ) -> Result<bool, RuntimeError> {
        let shared_names =
            self.generate_random_unused_names(Self::collect_fn_param_names(known_fn_body).len());
        let shared_return_set: Obj = StandardSet::R.into();
        let known_with_expected_return = FnSetBody::new(
            known_fn_body.params_def_with_set.clone(),
            known_fn_body.dom_facts.clone(),
            shared_return_set.clone(),
        );
        let expected_with_shared_return = FnSetBody::new(
            expected_fn_set.body.params_def_with_set.clone(),
            expected_fn_set.body.dom_facts.clone(),
            shared_return_set,
        );
        let known_norm = self
            .fn_set_alpha_renamed_for_display_compare(&known_with_expected_return, &shared_names)?;
        let expected_norm = self.fn_set_alpha_renamed_for_display_compare(
            &expected_with_shared_return,
            &shared_names,
        )?;
        Ok(known_norm.to_string() == expected_norm.to_string())
    }

    fn verify_fn_membership_application_well_defined(
        &mut self,
        flow: &FnMembershipProofFlow,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let stub = ForallFact::new(
            flow.forall_params.clone(),
            flow.forall_dom_facts.clone(),
            Vec::new(),
            flow.in_fact.line_file.clone(),
        )?;
        self.run_in_local_env(|rt| {
            rt.forall_assume_params_and_dom_in_current_env(&stub, verify_state)?;
            rt.verify_obj_well_defined_and_store_cache(&flow.applied_fn_obj, verify_state)
        })
    }

    fn collect_fn_param_names(body: &FnSetBody) -> Vec<String> {
        let mut out = Vec::new();
        for group in body.params_def_with_set.iter() {
            for binding in group.params.iter() {
                out.push(binding.name().to_string());
            }
        }
        out
    }

    fn build_full_application_arg_groups(
        known_fn_body: &FnSetBody,
        expected_flat_param_names: &[SymbolBinding],
    ) -> Vec<Vec<Box<Obj>>> {
        let mut args = Vec::new();
        let mut index = 0;
        for group in known_fn_body.params_def_with_set.iter() {
            for _ in group.params.iter() {
                args.push(Box::new(obj_for_bound_param_in_scope(
                    &expected_flat_param_names[index],
                    ParamObjType::Forall,
                )));
                index += 1;
            }
        }
        vec![args]
    }
}
