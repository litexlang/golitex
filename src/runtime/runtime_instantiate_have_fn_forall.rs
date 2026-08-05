// Normalize ForallFact from have fn / recursive have fn before storage.
//
// The same source spelling can refer to different bindings in non-overlapping scopes.
// from the fn header parse. Stored foralls should use one ForallFreeParamObj per quantified name
// from the header. The dedicated retagging mode converts only those binder-tagged atoms; concrete
// identifiers with the same spelling remain rigid.

use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn inst_have_fn_forall_fact_for_store(
        &self,
        forall_fact: ForallFact,
    ) -> Result<Fact, RuntimeError> {
        let source_bindings = forall_fact.params_def_with_type.collect_param_bindings();
        let (target_names, full_param_to_arg_map) =
            self.fresh_binder_retag_plan_for_bindings(&source_bindings, ParamObjType::Forall);
        let mut active_param_to_arg_map = HashMap::new();
        let mut groups = Vec::with_capacity(forall_fact.params_def_with_type.groups.len());
        let mut name_index = 0;
        for group in &forall_fact.params_def_with_type.groups {
            let renamed_param_type = self.inst_param_type(
                &group.param_type,
                &active_param_to_arg_map,
                ParamObjType::AlphaRename,
            )?;
            let param_type = self.inst_param_type(
                &renamed_param_type,
                &active_param_to_arg_map,
                ParamObjType::BinderRetag(BinderRetagSource::FnSet),
            )?;
            let group_target_names =
                target_names[name_index..name_index + group.params.len()].to_vec();
            groups.push(ParamGroupWithParamType::new(group_target_names, param_type));
            for source_binding in &group.params {
                let source_name = source_binding.name();
                insert_symbol_substitution(
                    &mut active_param_to_arg_map,
                    source_binding,
                    full_param_to_arg_map[source_name].clone(),
                );
            }
            name_index += group.params.len();
        }

        let mut dom_facts = Vec::with_capacity(forall_fact.dom_facts.len());
        for fact in &forall_fact.dom_facts {
            let renamed_fact = self.inst_fact(
                fact,
                &full_param_to_arg_map,
                ParamObjType::AlphaRename,
                None,
            )?;
            dom_facts.push(self.inst_fact(
                &renamed_fact,
                &full_param_to_arg_map,
                ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                None,
            )?);
        }
        let mut then_facts = Vec::with_capacity(forall_fact.then_facts.len());
        for fact in &forall_fact.then_facts {
            let renamed_fact = self.inst_exist_or_and_chain_atomic_fact(
                fact,
                &full_param_to_arg_map,
                ParamObjType::AlphaRename,
                None,
            )?;
            then_facts.push(self.inst_exist_or_and_chain_atomic_fact(
                &renamed_fact,
                &full_param_to_arg_map,
                ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                None,
            )?);
        }

        Ok(ForallFact::new_canonical_forall(
            ParamDefWithType::new(groups),
            dom_facts,
            then_facts,
            forall_fact.line_file,
        )?
        .into())
    }
}
