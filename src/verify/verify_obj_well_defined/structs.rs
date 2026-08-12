use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    /// Mathematical contract: a struct instantiation names a declared struct,
    /// supplies exactly its header arity, and gives well-defined arguments
    /// satisfying every declared parameter type and domain condition.
    pub(crate) fn struct_header_param_to_arg_map(
        &mut self,
        struct_obj: &StructObj,
        verify_state: &UseContextVerifyState,
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

    /// Mathematical contract: field carriers of a struct instance are the
    /// declared field expressions after sound header-parameter substitution.
    pub(crate) fn instantiated_struct_field_types(
        &mut self,
        struct_obj: &StructObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<Vec<Obj>, RuntimeError> {
        let (def, param_to_arg_map) =
            self.struct_header_param_to_arg_map(struct_obj, verify_state)?;
        let mut fields = Vec::with_capacity(def.fields.len());
        for field in def.fields.iter() {
            fields.push(self.inst_obj(
                &field.field_type,
                &param_to_arg_map,
                ParamObjType::DefHeader,
            )?);
        }
        Ok(fields)
    }

    /// Mathematical contract: a one-field structure is a named view of its
    /// sole field carrier.
    /// Multi-field structures retain their Cartesian-product representation.
    pub(crate) fn struct_carrier_from_field_types(&self, mut field_types: Vec<Obj>) -> Obj {
        if field_types.len() == 1 {
            return field_types.remove(0);
        }
        Cart::new(field_types).into()
    }

    /// Mathematical contract: a field projection index exists exactly when
    /// the instantiated struct names a declared field of that name.
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
            .position(|field| field.name() == field_name)
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

    /// Mathematical contract: field access denotes the value itself for a
    /// one-field struct and the corresponding one-based tuple projection for a
    /// multi-field struct.
    pub(crate) fn struct_field_access_projection(
        &self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
    ) -> Result<Obj, RuntimeError> {
        let index = self.struct_field_index(&field_access.struct_obj, &field_access.field_name)?;
        let struct_name = field_access.struct_obj.name.to_string();
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
        if def.fields.len() == 1 {
            return Ok((*field_access.obj).clone());
        }
        Ok(ObjAtIndex::new(
            (*field_access.obj).clone(),
            Number::new(index.to_string()).into(),
        )
        .into())
    }

    /// Mathematical contract: an instantiated struct carrier is meaningful
    /// when its header contract holds, every instantiated field carrier is
    /// meaningful, and each equivalent fact is meaningful under locally bound
    /// fields of those carriers.
    pub(in crate::verify) fn verify_struct_obj_well_defined(
        &mut self,
        struct_obj: &StructObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        let (def, param_to_arg_map) =
            self.struct_header_param_to_arg_map(struct_obj, verify_state)?;
        for field in def.fields.iter() {
            let instantiated_field_type = self.inst_obj(
                &field.field_type,
                &param_to_arg_map,
                ParamObjType::DefHeader,
            )?;
            self.verify_obj_well_defined_and_store_cache(&instantiated_field_type, verify_state)?;
        }
        self.run_in_local_env(|rt| {
            let field_bindings = def
                .fields
                .iter()
                .map(|field| field.binding.clone())
                .collect::<Vec<_>>();
            let field_rename_map = rt.visible_binding_conflict_rename_map(
                &field_bindings,
                ParamObjType::DefStructField,
            )?;
            let active_field_bindings = def
                .fields
                .iter()
                .map(
                    |field| match field_rename_map.get(&field.binding.substitution_key()) {
                        Some(Obj::Atom(AtomObj::DefStructField(param))) => {
                            param.symbol.to_local_binding()
                        }
                        _ => field.binding.clone(),
                    },
                )
                .collect::<Vec<_>>();

            for (field_binding, field) in active_field_bindings.iter().zip(def.fields.iter()) {
                let instantiated_field_type = rt.inst_obj(
                    &field.field_type,
                    &param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let instantiated_field_type = rt.inst_obj(
                    &instantiated_field_type,
                    &field_rename_map,
                    ParamObjType::AlphaRename,
                )?;
                let param_def =
                    ParamGroupWithSet::new(vec![field_binding.clone()], instantiated_field_type);
                rt.define_params_with_set_in_scope(&param_def, ParamObjType::DefStructField)?;
            }

            for fact in def.equivalent_facts.iter() {
                let instantiated_fact =
                    rt.inst_fact(fact, &param_to_arg_map, ParamObjType::DefHeader, None)?;
                let instantiated_fact = rt.inst_fact(
                    &instantiated_fact,
                    &field_rename_map,
                    ParamObjType::AlphaRename,
                    None,
                )?;
                rt.verify_well_defined_and_store_without_infer_with_state(
                    instantiated_fact,
                    verify_state,
                    InferReason::ByDefinition,
                )?;
            }
            Ok::<(), RuntimeError>(())
        })?;
        Ok(())
    }

    /// Mathematical contract: a template application is meaningful when its
    /// template exists and materialization verifies the instantiated template
    /// parameters, body declarations, and resulting object.
    pub(in crate::verify) fn verify_instantiated_template_obj_well_defined(
        &mut self,
        template_obj: &InstantiatedTemplateObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<(), RuntimeError> {
        self.materialize_instantiated_template_obj(template_obj, verify_state)
    }

    /// Mathematical contract: `value.field` is meaningful when the struct and
    /// field are declared, `value` is well-defined, and `value` is provably an
    /// instance of the instantiated struct carrier.
    pub(in crate::verify) fn verify_obj_as_struct_instance_with_field_access_well_defined(
        &mut self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        verify_state: &UseContextVerifyState,
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
