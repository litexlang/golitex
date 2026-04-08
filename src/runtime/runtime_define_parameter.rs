use crate::prelude::*;

impl Runtime {
    /// After `store_identifier_obj`, run param-type-specific work (type facts, storage, and later hooks).
    pub(crate) fn define_parameter_by_binding_param_type(
        &mut self,
        name: &str,
        param_type: &ParamType,
    ) -> Result<InferResult, RuntimeError> {
        match param_type {
            ParamType::Obj(obj) => match obj {
                Obj::FamilyObj(family_ty) => {
                    self.define_parameter_by_binding_family(name, family_ty)
                }
                _ => self.define_parameter_by_binding_obj(name, obj),
            },
            ParamType::Set(set) => self.define_parameter_by_binding_set(name, set),
            ParamType::NonemptySet(nonempty_set) => {
                self.define_parameter_by_binding_nonempty_set(name, nonempty_set)
            }
            ParamType::FiniteSet(finite_set) => {
                self.define_parameter_by_binding_finite_set(name, finite_set)
            }
            ParamType::Struct(struct_ty) => {
                self.define_parameter_by_binding_struct(name, struct_ty)
            }
        }
    }

    fn define_parameter_by_binding_family(
        &mut self,
        name: &str,
        family_ty: &FamilyObj,
    ) -> Result<InferResult, RuntimeError> {
        self.infer_membership_in_family_for_param_binding(name, family_ty)
    }

    fn define_parameter_by_binding_obj(
        &mut self,
        name: &str,
        obj: &Obj,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            Obj::Identifier(Identifier::new(name.to_string())),
            obj.clone(),
            default_line_file(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    fn define_parameter_by_binding_set(
        &mut self,
        name: &str,
        _set: &Set,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
            Obj::Identifier(Identifier::new(name.to_string())),
            default_line_file(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    fn define_parameter_by_binding_nonempty_set(
        &mut self,
        name: &str,
        _nonempty_set: &NonemptySet,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
            Obj::Identifier(Identifier::new(name.to_string())),
            default_line_file(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    fn define_parameter_by_binding_finite_set(
        &mut self,
        name: &str,
        _finite_set: &FiniteSet,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
            Obj::Identifier(Identifier::new(name.to_string())),
            default_line_file(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    pub(crate) fn define_parameter_by_binding_struct(
        &mut self,
        name: &str,
        struct_ty: &StructObj,
    ) -> Result<InferResult, RuntimeError> {
        self.register_param_as_struct_instance(name, struct_ty.clone());

        let new_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            Obj::Identifier(Identifier::new(name.to_string())),
            Obj::StructObj(struct_ty.clone()),
            default_line_file(),
        )));

        let infer_result = self.store_fact_without_well_defined_verified_and_infer(new_fact)?;

        Ok(infer_result)
    }

    pub fn register_param_as_struct_instance(&mut self, env_key: &str, inst: StructObj) {
        let key = env_key.to_string();
        self.top_level_env()
            .known_identifier_satisfy_struct
            .insert(key.clone(), inst);
        self.top_level_env()
            .cache_well_defined_obj
            .insert(key.clone(), ());
        self.top_level_env().defined_identifiers.insert(key, ());
    }

    pub fn define_params_with_type(
        &mut self,
        param_defs: &[ParamGroupWithParamType],
        check_type_nonempty: bool,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for param_def in param_defs.iter() {
            self.verify_param_type_well_defined(&param_def.param_type, &VerifyState::new(0, false))
                .map_err(|well_defined_error| {
                    let param_names_text = param_def.params.join(", ");
                    let error_line_file = well_defined_error.line_file().clone();
                    RuntimeError::new_define_params_error_with_msg_previous_error_position(
                        format!(
                            "define params with type: failed to verify type well-defined for params [{}] with type {}",
                            param_names_text, param_def.param_type
                        ),
                        Some(well_defined_error.into()),
                        error_line_file,
                    )
                })?;
            self.verify_param_type_nonempty_if_required(&param_def.param_type, check_type_nonempty)
                .map_err(|inner_exec_error| {
                    let param_names_text = param_def.params.join(", ");
                    RuntimeError::new_define_params_error_with_msg_previous_error_position(
                        format!(
                            "define params with type: nonempty check failed for params [{}] with type {}",
                            param_names_text, param_def.param_type
                        ),
                        Some(RuntimeError::from(inner_exec_error)),
                        default_line_file(),
                    )
                })?;

            for name in param_def.params.iter() {
                self.store_identifier_obj(name).map_err(|runtime_error| {
                    RuntimeError::new_define_params_error_with_msg_previous_error_position(
                        format!(
                            "define params with type: failed to declare parameter `{}`",
                            name
                        ),
                        Some(RuntimeError::from(runtime_error)),
                        default_line_file(),
                    )
                })?;
                let fact_infer_result = self
                    .define_parameter_by_binding_param_type(name, &param_def.param_type)
                    .map_err(|runtime_error| {
                        RuntimeError::new_define_params_error_with_msg_previous_error_position(
                            format!(
                                "define params with type: failed to apply param type for parameter `{}` with type {}",
                                name, param_def.param_type
                            ),
                            Some(runtime_error),
                            default_line_file(),
                        )
                    })?;
                infer_result.new_infer_result_inside(fact_infer_result);
            }
        }
        Ok(infer_result)
    }
}
