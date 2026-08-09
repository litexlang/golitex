use crate::prelude::*;

impl Runtime {
    /// After `store_identifier_obj`, run param-type-specific work (type facts, storage, and later hooks).
    pub fn define_parameter_by_binding_param_type(
        &mut self,
        binding: &SymbolBinding,
        param_type: &ParamType,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        match param_type {
            ParamType::Obj(obj) => match obj {
                Obj::FiniteSeqSet(fs) => {
                    let fn_set = self.finite_seq_set_to_fn_set(fs, default_line_file());
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(binding, binding_kind),
                        fn_set.into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
                        type_fact,
                        InferReason::ParameterDefinition,
                    )
                }
                Obj::SeqSet(ss) => {
                    let fn_set = self.seq_set_to_fn_set(ss, default_line_file());
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(binding, binding_kind),
                        fn_set.into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
                        type_fact,
                        InferReason::ParameterDefinition,
                    )
                }
                Obj::MatrixSet(ms) => {
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(binding, binding_kind),
                        ms.clone().into(),
                        default_line_file(),
                    )
                    .into();
                    self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
                        type_fact,
                        InferReason::ParameterDefinition,
                    )
                }
                _ => self.define_parameter_by_binding_obj(binding, obj, binding_kind),
            },
            ParamType::Set(set) => self.define_parameter_by_binding_set(binding, set, binding_kind),
            ParamType::NonemptySet(nonempty_set) => {
                self.define_parameter_by_binding_nonempty_set(binding, nonempty_set, binding_kind)
            }
            ParamType::FiniteSet(finite_set) => {
                self.define_parameter_by_binding_finite_set(binding, finite_set, binding_kind)
            }
        }
    }

    fn define_parameter_by_binding_obj(
        &mut self,
        binding: &SymbolBinding,
        obj: &Obj,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact: Fact = InFact::new(
            param_binding_element_obj_for_store(binding, binding_kind),
            obj.clone(),
            default_line_file(),
        )
        .into();
        self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
            type_fact,
            InferReason::ParameterDefinition,
        )
    }

    fn define_parameter_by_binding_set(
        &mut self,
        binding: &SymbolBinding,
        _set: &Set,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = IsSetFact::new(
            param_binding_element_obj_for_store(binding, binding_kind),
            default_line_file(),
        )
        .into();
        self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
            type_fact,
            InferReason::ParameterDefinition,
        )
    }

    fn define_parameter_by_binding_nonempty_set(
        &mut self,
        binding: &SymbolBinding,
        _nonempty_set: &NonemptySet,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = IsNonemptySetFact::new(
            param_binding_element_obj_for_store(binding, binding_kind),
            default_line_file(),
        )
        .into();
        self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
            type_fact,
            InferReason::ParameterDefinition,
        )
    }

    fn define_parameter_by_binding_finite_set(
        &mut self,
        binding: &SymbolBinding,
        _finite_set: &FiniteSet,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let type_fact = IsFiniteSetFact::new(
            param_binding_element_obj_for_store(binding, binding_kind),
            default_line_file(),
        )
        .into();
        self.store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
            type_fact,
            InferReason::ParameterDefinition,
        )
    }

    pub fn define_params_with_type(
        &mut self,
        param_defs: &ParamDefWithType,
        check_type_nonempty: bool,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for param_def in param_defs.groups.iter() {
            self.verify_param_type_well_defined(&param_def.param_type, &UseContextVerifyState::new(0, false))
                .map_err(|well_defined_error| {
                    let param_names_text = vec_to_string_join_by_comma(&param_def.params);
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
                    let param_names_text = vec_to_string_join_by_comma(&param_def.params);
                    RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                            "define params with type: nonempty check failed for params [{}] with type {}",
                            param_names_text, param_def.param_type
                        ), inner_exec_error)))
                })?;

            for binding in param_def.params.iter() {
                let name = binding.name();
                self.store_parameter_binding(binding, binding_kind)
                    .map_err(|runtime_error| {
                        RuntimeError::from(DefineParamsRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "define params with type: failed to declare parameter `{}`",
                                    name
                                ),
                                runtime_error,
                            ),
                        ))
                    })?;
                let fact_infer_result = self
                    .define_parameter_by_binding_param_type(
                        binding,
                        &param_def.param_type,
                        binding_kind,
                    )
                    .map_err(|runtime_error| {
                        RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                                "define params with type: failed to apply param type for parameter `{}` with type {}",
                                name, param_def.param_type
                            ), runtime_error)))
                    })?;
                infer_result.new_infer_result_inside(fact_infer_result);
            }
        }
        Ok(infer_result)
    }

    pub fn define_params_with_type_trusted(
        &mut self,
        param_defs: &ParamDefWithType,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for param_def in param_defs.groups.iter() {
            for binding in param_def.params.iter() {
                self.store_parameter_binding(binding, binding_kind)?;
                let param_obj = param_binding_element_obj_for_store(binding, binding_kind);
                let fact: Fact = match &param_def.param_type {
                    ParamType::Obj(obj) => InFact::new(
                        param_obj,
                        match obj {
                            Obj::FiniteSeqSet(fs) => self
                                .finite_seq_set_to_fn_set(fs, default_line_file())
                                .into(),
                            Obj::SeqSet(ss) => {
                                self.seq_set_to_fn_set(ss, default_line_file()).into()
                            }
                            Obj::MatrixSet(ms) => {
                                self.matrix_set_to_fn_set(ms, default_line_file()).into()
                            }
                            _ => obj.clone(),
                        },
                        default_line_file(),
                    )
                    .into(),
                    ParamType::Set(_) => IsSetFact::new(param_obj, default_line_file()).into(),
                    ParamType::NonemptySet(_) => {
                        IsNonemptySetFact::new(param_obj, default_line_file()).into()
                    }
                    ParamType::FiniteSet(_) => {
                        IsFiniteSetFact::new(param_obj, default_line_file()).into()
                    }
                };
                infer_result.new_infer_result_inside(
                    self.store_trusted_fact_and_infer_with_reason(
                        fact,
                        InferReason::ParameterDefinition,
                    )?,
                );
            }
        }
        Ok(infer_result)
    }
}
