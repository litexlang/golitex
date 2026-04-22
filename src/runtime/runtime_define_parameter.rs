use crate::prelude::*;

impl Runtime {
    /// After `store_identifier_obj`, run param-type-specific work (type facts, storage, and later hooks).
    pub fn define_parameter_by_binding_param_type(
        &mut self,
        name: &str,
        param_type: &ParamType,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        match param_type {
            ParamType::Obj(obj) => match obj {
                Obj::FamilyObj(family_ty) => {
                    self.define_parameter_by_binding_family(name, family_ty, binding_kind)
                }
                Obj::FiniteSeqSet(fs) => {
                    let fn_set = self.finite_seq_set_to_fn_set(fs, default_line_file());
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(name.to_string(), binding_kind),
                        fn_set.into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_fact_without_well_defined_verified_and_infer(type_fact)
                }
                Obj::SeqSet(ss) => {
                    let fn_set = self.seq_set_to_fn_set(ss, default_line_file());
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(name.to_string(), binding_kind),
                        fn_set.into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_fact_without_well_defined_verified_and_infer(type_fact)
                }
                Obj::MatrixSet(ms) => {
                    let fn_set = self.matrix_set_to_fn_set(ms, default_line_file());
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(name.to_string(), binding_kind),
                        fn_set.into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_fact_without_well_defined_verified_and_infer(type_fact)
                }
                _ => self.define_parameter_by_binding_obj(name, obj, binding_kind),
            },
            ParamType::Set(set) => self.define_parameter_by_binding_set(name, set, binding_kind),
            ParamType::NonemptySet(nonempty_set) => {
                self.define_parameter_by_binding_nonempty_set(name, nonempty_set, binding_kind)
            }
            ParamType::FiniteSet(finite_set) => {
                self.define_parameter_by_binding_finite_set(name, finite_set, binding_kind)
            }
        }
    }

    fn define_parameter_by_binding_family(
        &mut self,
        name: &str,
        family_ty: &FamilyObj,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        self.infer_membership_in_family_for_param_binding(name, family_ty, binding_kind)
    }

    fn define_parameter_by_binding_obj(
        &mut self,
        name: &str,
        obj: &Obj,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = InFact::new(
            param_binding_element_obj_for_store(name.to_string(), binding_kind),
            obj.clone(),
            default_line_file(),
        )
        .into();
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
    }

    fn define_parameter_by_binding_set(
        &mut self,
        name: &str,
        _set: &Set,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = IsSetFact::new(
            param_binding_element_obj_for_store(name.to_string(), binding_kind),
            default_line_file(),
        )
        .into();
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
    }

    fn define_parameter_by_binding_nonempty_set(
        &mut self,
        name: &str,
        _nonempty_set: &NonemptySet,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = IsNonemptySetFact::new(
            param_binding_element_obj_for_store(name.to_string(), binding_kind),
            default_line_file(),
        )
        .into();
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
    }

    fn define_parameter_by_binding_finite_set(
        &mut self,
        name: &str,
        _finite_set: &FiniteSet,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = IsFiniteSetFact::new(
            param_binding_element_obj_for_store(name.to_string(), binding_kind),
            default_line_file(),
        )
        .into();
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
    }

    pub fn define_params_with_type(
        &mut self,
        param_defs: &ParamDefWithType,
        check_type_nonempty: bool,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for param_def in param_defs.groups.iter() {
            self.verify_param_type_well_defined(&param_def.param_type, &VerifyState::new(0, false))
                .map_err(|well_defined_error| {
                    let param_names_text = param_def.params.join(", ");
                    let error_line_file = well_defined_error.line_file().clone();
                    RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                            "define params with type: failed to verify type well-defined for params [{}] with type {}",
                            param_names_text, param_def.param_type
                        ),
                error_line_file,
                Some(well_defined_error),
                vec![],
            )))
                })?;
            self.verify_param_type_nonempty_if_required(&param_def.param_type, check_type_nonempty)
                .map_err(|inner_exec_error| {
                    let param_names_text = param_def.params.join(", ");
                    RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                            "define params with type: nonempty check failed for params [{}] with type {}",
                            param_names_text, param_def.param_type
                        ),
                default_line_file(),
                Some(inner_exec_error),
                vec![],
            )))
                })?;

            for name in param_def.params.iter() {
                self.store_free_param_or_identifier_name(name, binding_kind)
                    .map_err(|runtime_error| {
                        RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new(
                            None,
                            format!(
                                "define params with type: failed to declare parameter `{}`",
                                name
                            ),
                            default_line_file(),
                            Some(runtime_error),
                            vec![],
                        )))
                    })?;
                let fact_infer_result = self
                    .define_parameter_by_binding_param_type(
                        name,
                        &param_def.param_type,
                        binding_kind,
                    )
                    .map_err(|runtime_error| {
                        RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                                "define params with type: failed to apply param type for parameter `{}` with type {}",
                                name, param_def.param_type
                            ),
                default_line_file(),
                Some(runtime_error),
                vec![],
            )))
                    })?;
                infer_result.new_infer_result_inside(fact_infer_result);
            }
        }
        Ok(infer_result)
    }
}
