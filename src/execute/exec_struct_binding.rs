use crate::prelude::*;

impl Runtime {
    pub(crate) fn define_parameter_by_binding_struct(
        &mut self,
        name: &str,
        struct_ty: &StructParamType,
    ) -> Result<InferResult, RuntimeError> {
        self.register_param_as_struct_instance(name, struct_ty.clone());
        Ok(InferResult::new())
    }

    pub fn register_param_as_struct_instance(&mut self, env_key: &str, inst: StructParamType) {
        let key = env_key.to_string();
        self.top_level_env()
            .known_identifier_satisfy_struct
            .insert(key.clone(), inst);
        self.top_level_env()
            .cache_well_defined_obj
            .insert(key.clone(), ());
        self.top_level_env().defined_identifiers.insert(key, ());
    }
}
