use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub(crate) fn struct_header_param_to_arg_map(
        &mut self,
        struct_obj: &StructObj,
        verify_state: &VerifyState,
    ) -> Result<(DefStructStmt, HashMap<String, Obj>), RuntimeError> {
        let struct_name = struct_obj.name.to_string();
        let def = self
            .get_struct_definition_by_name(&struct_name)
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "struct `{}` is not defined",
                        struct_name
                    )),
                ))
            })?;

        let expected_count = def
            .param_def_with_dom
            .as_ref()
            .map(|(param_def, _)| param_def.number_of_params())
            .unwrap_or(0);
        if struct_obj.params.len() != expected_count {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "struct `{}` expects {} parameter(s), got {}",
                    struct_name,
                    expected_count,
                    struct_obj.params.len()
                )),
            )));
        }

        for arg in struct_obj.params.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let param_to_arg_map = if let Some((param_def, dom_facts)) = &def.param_def_with_dom {
            let verify_args_result = self
                .verify_args_satisfy_param_def_flat_types(
                    param_def,
                    &struct_obj.params,
                    verify_state,
                    ParamObjType::DefHeader,
                )
                .map_err(|runtime_error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify struct `{}` arguments satisfy parameter types",
                                struct_name
                            ),
                            runtime_error,
                        ),
                    ))
                })?;
            if verify_args_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "failed to verify struct `{}` arguments satisfy parameter types",
                        struct_name
                    )),
                )));
            }

            let param_to_arg_map =
                param_def.param_defs_and_args_to_param_to_arg_map(&struct_obj.params);

            for dom_fact in dom_facts.iter() {
                let instantiated_dom_fact = self
                    .inst_or_and_chain_atomic_fact(
                        dom_fact,
                        &param_to_arg_map,
                        ParamObjType::DefHeader,
                        None,
                    )
                    .map_err(|e| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "failed to instantiate struct `{}` domain fact",
                                    struct_name
                                ),
                                e,
                            ),
                        ))
                    })?;
                let verify_result =
                    self.verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)?;
                if verify_result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "failed to verify struct `{}` domain fact:\n{}",
                            struct_name, instantiated_dom_fact
                        )),
                    )));
                }
            }

            param_to_arg_map
        } else {
            HashMap::new()
        };

        Ok((def, param_to_arg_map))
    }

    pub(crate) fn instantiated_struct_field_types(
        &mut self,
        struct_obj: &StructObj,
        verify_state: &VerifyState,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let (def, param_to_arg_map) =
            self.struct_header_param_to_arg_map(struct_obj, verify_state)?;
        let mut fields = Vec::with_capacity(def.fields.len());
        for (_, field_type) in def.fields.iter() {
            fields.push(self.inst_obj(field_type, &param_to_arg_map, ParamObjType::DefHeader)?);
        }
        Ok(fields)
    }

    pub(crate) fn struct_field_index(
        &self,
        struct_obj: &StructObj,
        field_name: &str,
    ) -> Result<usize, RuntimeError> {
        let struct_name = struct_obj.name.to_string();
        let def = self
            .get_struct_definition_by_name(&struct_name)
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "struct `{}` is not defined",
                        struct_name
                    )),
                ))
            })?;
        def.fields
            .iter()
            .position(|(name, _)| name == field_name)
            .map(|idx| idx + 1)
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "struct `{}` has no field `{}`",
                        struct_name, field_name
                    )),
                ))
            })
    }

    pub(crate) fn struct_field_access_projection(
        &self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
    ) -> Result<Obj, RuntimeError> {
        let index = self.struct_field_index(&field_access.struct_obj, &field_access.field_name)?;
        Ok(ObjAtIndex::new(
            (*field_access.obj).clone(),
            Number::new(index.to_string()).into(),
        )
        .into())
    }

    pub(in crate::verify) fn verify_struct_obj_well_defined(
        &mut self,
        struct_obj: &StructObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let (def, param_to_arg_map) =
            self.struct_header_param_to_arg_map(struct_obj, verify_state)?;
        for (_, field_type) in def.fields.iter() {
            let instantiated_field_type =
                self.inst_obj(field_type, &param_to_arg_map, ParamObjType::DefHeader)?;
            self.verify_obj_well_defined_and_store_cache(&instantiated_field_type, verify_state)?;
        }
        self.run_in_local_env(|rt| {
            for (field_name, field_type) in def.fields.iter() {
                let instantiated_field_type =
                    rt.inst_obj(field_type, &param_to_arg_map, ParamObjType::DefHeader)?;
                let param_def =
                    ParamGroupWithSet::new(vec![field_name.clone()], instantiated_field_type);
                rt.define_params_with_set_in_scope(&param_def, ParamObjType::DefStructField)?;
            }

            for fact in def.equivalent_facts.iter() {
                let instantiated_fact =
                    rt.inst_fact(fact, &param_to_arg_map, ParamObjType::DefHeader, None)?;
                rt.verify_fact_well_defined(&instantiated_fact, verify_state)?;
            }
            Ok::<(), RuntimeError>(())
        })?;
        Ok(())
    }

    pub(in crate::verify) fn verify_instantiated_template_obj_well_defined(
        &mut self,
        template_obj: &InstantiatedTemplateObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.materialize_instantiated_template_obj(template_obj, verify_state)
    }

    pub(in crate::verify) fn verify_obj_as_struct_instance_with_field_access_well_defined(
        &mut self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        self.verify_struct_obj_well_defined(&field_access.struct_obj, verify_state)?;
        self.struct_field_index(&field_access.struct_obj, &field_access.field_name)?;
        self.verify_obj_well_defined_and_store_cache(&field_access.obj, verify_state)?;
        let membership_fact: AtomicFact = InFact::new(
            (*field_access.obj).clone(),
            (*field_access.struct_obj).clone().into(),
            default_line_file(),
        )
        .into();
        let result = self.verify_atomic_fact(&membership_fact, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "failed to verify `{}` is well-defined: cannot prove {}",
                    field_access, membership_fact
                )),
            )));
        }
        Ok(())
    }
}
