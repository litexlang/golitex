// Normalize ForallFact from have fn / have fn by decreasing before storage.
//
// The same source name (e.g. x) can appear as different free-param tags: Forall (~1) or FnSet (~5)
// from the fn header parse. Stored foralls should use one ForallFreeParamObj per quantified name
// from the header. We build name -> ForallFreeParamObj, then inst_fact(..., ParamObjType::FnSet).
// inst_obj substitutes FnSet, Forall, and Induc atoms when the name is in that map and ctx is FnSet
// (see runtime_instantiate_obj.rs).

use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn inst_have_fn_forall_fact_for_store(
        &self,
        forall_fact: ForallFact,
    ) -> Result<Fact, RuntimeError> {
        let param_to_arg_map = have_fn_forall_store_binding_map(&forall_fact);
        let fact: Fact = forall_fact.into();
        self.inst_fact(&fact, &param_to_arg_map, ParamObjType::FnSet, None)
    }
}

fn have_fn_forall_store_binding_map(forall_fact: &ForallFact) -> HashMap<String, Obj> {
    let mut param_to_arg_map = HashMap::new();
    for group in forall_fact.params_def_with_type.groups.iter() {
        for name in group.params.iter() {
            param_to_arg_map.insert(name.clone(), ForallFreeParamObj::new(name.clone()).into());
        }
    }
    param_to_arg_map
}
