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
                return Err(VerifyError::new(
                    Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                        obj.clone(),
                        Obj::Identifier(Identifier::new(String::from("_"))),
                        DEFAULT_LINE_FILE.clone(),
                    ))),
                    format!("family `{}` is not defined", family_name),
                    DEFAULT_LINE_FILE,
                    None,
                ));
            }
        };
        let expected_count =
            ParamDefWithParamType::number_of_params(&def.params_def_with_type);
        if family_ty.params.len() != expected_count {
            return Err(VerifyError::new(
                Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    obj.clone(),
                    Obj::Identifier(Identifier::new(String::from("_"))),
                    DEFAULT_LINE_FILE.clone(),
                ))),
                format!(
                    "family `{}` expects {} type argument(s), got {}",
                    family_name,
                    expected_count,
                    family_ty.params.len()
                ),
                DEFAULT_LINE_FILE,
                None,
            ));
        }
        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &family_ty.params,
        );
        let member_set = self.inst_obj(&def.equal_to, &param_to_arg_map).map_err(|e| {
            VerifyError::new(
                Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    obj.clone(),
                    Obj::Identifier(Identifier::new(String::from("_"))),
                    DEFAULT_LINE_FILE.clone(),
                ))),
                String::new(),
                DEFAULT_LINE_FILE,
                Some(e),
            )
        })?;
        let fact = AtomicFact::InFact(InFact::new(
            obj,
            member_set,
            DEFAULT_LINE_FILE.clone(),
        ));
        self.verify_atomic_fact(&fact, verify_state)
    }
}