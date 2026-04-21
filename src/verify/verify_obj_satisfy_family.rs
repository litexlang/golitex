use crate::prelude::*;

impl Runtime {
    pub fn verify_obj_satisfies_family(
        &mut self,
        obj: Obj,
        family_ty: &FamilyObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let family_name = family_ty.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                None,
                format!("family `{}` is not defined", family_name),
                default_line_file(),
                None,
                vec![],
            ))
            .into(),
                );
            }
        };
        let expected_count = def.params_def_with_type.number_of_params();
        if family_ty.params.len() != expected_count {
            return Err(
                VerifyRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                        "family `{}` expects {} type argument(s), got {}",
                        family_name,
                        expected_count,
                        family_ty.params.len()
                    ),
                default_line_file(),
                None,
                vec![],
            ))
            .into(),
            );
        }
        let param_to_arg_map = def
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(family_ty.params.as_slice());
        let member_set = self.inst_obj(&def.equal_to, &param_to_arg_map, ParamObjType::DefProp)?;
        let fact = InFact::new(obj, member_set, default_line_file()).into();
        self.verify_atomic_fact(&fact, verify_state)
    }
}
