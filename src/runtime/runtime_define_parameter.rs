use crate::prelude::*;
use std::collections::HashMap;

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
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        type_fact,
                    )
                }
                Obj::SeqSet(ss) => {
                    let fn_set = self.seq_set_to_fn_set(ss, default_line_file());
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(name.to_string(), binding_kind),
                        fn_set.into(),
                        default_line_file(),
                    )
                    .into();
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        type_fact,
                    )
                }
                Obj::MatrixSet(ms) => {
                    let fn_set = self.matrix_set_to_fn_set(ms, default_line_file());
                    let type_fact = InFact::new(
                        param_binding_element_obj_for_store(name.to_string(), binding_kind),
                        fn_set.into(),
                        default_line_file(),
                    )
                    .into();
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        type_fact,
                    )
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
            ParamType::Struct(struct_ty) => {
                self.define_parameter_by_binding_struct(name, struct_ty, binding_kind)
            }
        }
    }

    fn define_parameter_by_binding_struct(
        &mut self,
        name: &str,
        struct_ty: &StructAsParamType,
        _binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        let struct_name = struct_ty.struct_name();
        let def = self
            .get_struct_definition_by_name(&struct_name)
            .cloned()
            .ok_or_else(|| {
                RuntimeError::from(DefineParamsRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "struct `{}` is not defined",
                        struct_name
                    )),
                ))
            })?;

        self.store_name_belong_to_struct(name, &struct_name)?;

        let param_to_arg_map = match &def.param_def_with_dom {
            Some((param_def, _)) => {
                param_def.param_defs_and_boxed_args_to_param_to_arg_map(struct_ty.args.as_slice())
            }
            None => HashMap::new(),
        };

        let mut infer_result = InferResult::new();
        for (field_name, field_type) in def.fields.iter() {
            let instantiated_field_type =
                self.inst_obj(field_type, &param_to_arg_map, ParamObjType::DefHeader)?;
            let field_obj: Obj = FieldAccess::new(name.to_string(), field_name.clone()).into();
            let field_type_fact: Fact =
                InFact::new(field_obj, instantiated_field_type, default_line_file()).into();
            infer_result.new_infer_result_inside(
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                    field_type_fact,
                )?,
            );
        }

        let mut field_to_obj_map = HashMap::new();
        for (field_name, _) in def.fields.iter() {
            field_to_obj_map.insert(
                field_name.clone(),
                FieldAccess::new(name.to_string(), field_name.clone()).into(),
            );
        }
        for fact in def.equivalent_facts.iter() {
            let header_instantiated_fact =
                self.inst_fact(fact, &param_to_arg_map, ParamObjType::DefHeader, None)?;
            let field_instantiated_fact = self.inst_fact(
                &header_instantiated_fact,
                &field_to_obj_map,
                ParamObjType::DefStructField,
                None,
            )?;
            infer_result.new_infer_result_inside(
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                    field_instantiated_fact,
                )?,
            );
        }

        Ok(infer_result)
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
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(type_fact)
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
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(type_fact)
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
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(type_fact)
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
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(type_fact)
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
                    RuntimeError::from(DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                            "define params with type: nonempty check failed for params [{}] with type {}",
                            param_names_text, param_def.param_type
                        ), inner_exec_error)))
                })?;

            for name in param_def.params.iter() {
                self.store_free_param_or_identifier_name(name, binding_kind)
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
                        name,
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
}

#[cfg(test)]
mod struct_param_type_tests {
    use crate::prelude::*;

    fn group_struct_definition() -> DefStructStmt {
        group_struct_definition_with_header_type(ParamType::Set(Set::new()))
    }

    fn group_struct_definition_with_header_type(param_type: ParamType) -> DefStructStmt {
        DefStructStmt::new(
            "Group".to_string(),
            Some((
                ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec!["s".to_string()],
                    param_type,
                )]),
                vec![],
            )),
            vec![(
                "zero".to_string(),
                DefHeaderFreeParamObj::new("s".to_string()).into(),
            )],
            vec![],
            default_line_file(),
        )
    }

    fn group_struct_param_type(arg: Obj) -> ParamType {
        ParamType::Struct(StructAsParamType::new(
            NameOrNameWithMod::new_name("Group".to_string()),
            vec![arg],
        ))
    }

    #[test]
    fn defining_struct_param_releases_membership_information() {
        let mut rt = Runtime::new();
        rt.store_def_struct(&group_struct_definition()).unwrap();

        let param_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec!["G".to_string()],
            group_struct_param_type(StandardSet::R.into()),
        )]);
        rt.define_params_with_type(&param_def, false, ParamObjType::Identifier)
            .unwrap();

        assert_eq!(
            rt.top_level_env()
                .known_name_belong_to_struct
                .get("G")
                .cloned(),
            Some("Group".to_string())
        );

        let zero: Obj = FieldAccess::new("G".to_string(), "zero".to_string()).into();
        assert!(rt
            .verify_obj_well_defined_and_store_cache(&zero, &VerifyState::new(0, false))
            .is_ok());

        let fact: AtomicFact = InFact::new(zero, StandardSet::R.into(), default_line_file()).into();
        assert!(!rt
            .verify_atomic_fact(&fact, &VerifyState::new(0, false))
            .unwrap()
            .is_unknown());
    }

    #[test]
    fn struct_param_type_checks_header_param_types() {
        let mut rt = Runtime::new();
        rt.store_def_struct(&group_struct_definition()).unwrap();

        assert!(rt
            .verify_param_type_well_defined(
                &group_struct_param_type(StandardSet::R.into()),
                &VerifyState::new(0, false)
            )
            .is_ok());

        let mut rt = Runtime::new();
        rt.store_def_struct(&group_struct_definition_with_header_type(ParamType::Obj(
            StandardSet::R.into(),
        )))
        .unwrap();
        assert!(rt
            .verify_param_type_well_defined(
                &group_struct_param_type(Number::new("1".to_string()).into()),
                &VerifyState::new(0, false)
            )
            .is_ok());
        assert!(rt
            .verify_param_type_well_defined(
                &group_struct_param_type(StandardSet::R.into()),
                &VerifyState::new(0, false)
            )
            .is_err());
    }

    #[test]
    fn struct_param_type_is_not_known_nonempty() {
        let mut rt = Runtime::new();
        rt.store_def_struct(&group_struct_definition()).unwrap();

        assert!(rt
            .verify_param_type_nonempty_if_required(
                &group_struct_param_type(StandardSet::R.into()),
                true
            )
            .is_err());
    }
}
