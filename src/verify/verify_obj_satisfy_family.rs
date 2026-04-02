use crate::prelude::*;

impl Runtime {
    pub fn verify_obj_satisfies_family(
        &mut self,
        obj: Obj,
        family_ty: &FamilyParamType,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let family_name = family_ty.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(VerifyError::new_message_only(
                    format!("family `{}` is not defined", family_name),
                    default_line_file(),
                    None,
                ));
            }
        };
        let expected_count =
            ParamDefWithParamType::number_of_params(&def.params_def_with_type);
        if family_ty.params.len() != expected_count {
            return Err(VerifyError::new_message_only(
                format!(
                    "family `{}` expects {} type argument(s), got {}",
                    family_name,
                    expected_count,
                    family_ty.params.len()
                ),
                default_line_file(),
                None,
            ));
        }
        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &family_ty.params,
        );
        let member_set = self.inst_obj(&def.equal_to, &param_to_arg_map).map_err(|e| {
            VerifyError::new_message_only(String::new(), default_line_file(), Some(e))
        })?;
        let fact = AtomicFact::InFact(InFact::new(
            obj,
            member_set,
            default_line_file(),
        ));
        self.verify_atomic_fact(&fact, verify_state)
    }
}