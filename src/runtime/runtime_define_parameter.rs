use crate::prelude::*;

fn fact_for_obj_satisfies_param_type_shallow(
    arg: Obj,
    param_type: &ParamType,
    line_file: LineFile,
) -> Fact {
    match param_type {
        ParamType::Set(_) => IsSetFact::new(arg, line_file).into(),
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(arg, line_file).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(arg, line_file).into(),
        ParamType::Obj(obj) => InFact::new(arg, obj.clone(), line_file).into(),
        ParamType::Struct(st) => InFact::new(arg, Obj::StructObj(st.clone()), line_file).into(),
    }
}

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
            ParamType::Struct(struct_ty) => {
                self.define_parameter_by_binding_struct(name, struct_ty, binding_kind)
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

    pub fn define_parameter_by_binding_struct(
        &mut self,
        name: &str,
        struct_ty: &StructObj,
        binding_kind: ParamObjType,
    ) -> Result<InferResult, RuntimeError> {
        self.register_param_as_struct_instance(name, struct_ty.clone());

        let mut infer_result = InferResult::new();

        let new_fact = InFact::new(
            param_binding_element_obj_for_store(name.to_string(), binding_kind),
            Obj::StructObj(struct_ty.clone()),
            default_line_file(),
        )
        .into();
        infer_result.new_infer_result_inside(
            self.store_fact_without_well_defined_verified_and_infer(new_fact)?,
        );

        let struct_name = struct_ty.name.to_string();
        let Some(def) = self.get_cloned_definition_of_struct(&struct_name) else {
            return Ok(infer_result);
        };

        let base_map = def
            .param_defs
            .param_defs_and_args_to_param_to_arg_map(struct_ty.args.as_slice());
        let lf = default_line_file();
        for (field_name, field_ty) in def.fields.iter() {
            // let arg = FieldAccess::new(name.to_string(), field_name.clone()).into();
            let arg = ForallFieldAccessObj::new(name.to_string(), field_name.clone()).into();
            let param_type = self.inst_param_type(field_ty, &base_map, ParamObjType::DefHeader)?;
            let f = fact_for_obj_satisfies_param_type_shallow(arg, &param_type, lf.clone());

            println!("f: {:?}", f.to_string());

            infer_result.new_infer_result_inside(
                self.store_fact_without_well_defined_verified_and_infer(f)?,
            );
        }

        let iff_facts = self.instantiated_struct_iff_fact(struct_ty, &def, name)?;
        for ocf in iff_facts {
            let result =
                self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(ocf)?;
            infer_result.new_infer_result_inside(result);
        }

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
        self.top_level_env()
            .defined_identifiers
            .insert(key, ParamObjType::StructSelf);
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
