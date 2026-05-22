use crate::prelude::*;

impl Runtime {
    pub fn verify_obj_well_defined_with_its_local_def(
        &mut self,
        params_def: impl Into<ParamDefWithSet>,
        define_params_to_be_param_obj_type: ParamObjType,
        obj: Obj,
    ) -> Result<(), RuntimeError> {
        let params_def = params_def.into();
        self.run_in_local_env(|rt| {
            for param_def in params_def.iter() {
                rt.define_params_with_set_in_scope(param_def, define_params_to_be_param_obj_type)?;
            }
            rt.verify_obj_well_defined_and_store_cache(&obj, &VerifyState::new(0, false))
        })
    }
}
