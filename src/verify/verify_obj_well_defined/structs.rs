use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub(in crate::verify) fn verify_struct_obj_well_defined_result(
        &mut self,
        struct_obj: &StructObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let structure_name = struct_obj.name.to_string();
        let def = self
            .get_struct_definition_by_name(&structure_name)
            .ok_or_else(|| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "struct `{structure_name}` is not defined"
                    )),
                ))
            })?;
        let expected_count = def
            .param_def_with_dom
            .as_ref()
            .map(|(definition, _)| definition.number_of_params())
            .unwrap_or(0);
        if struct_obj.params.len() != expected_count {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "struct `{structure_name}` expects {expected_count} parameter(s), got {}",
                    struct_obj.params.len()
                )),
            )));
        }

        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, argument) in struct_obj.params.iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                argument,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }

        let mut header_arguments = Vec::new();
        let mut header_domains = Vec::new();
        let param_to_arg_map = if let Some((parameter_definition, domains)) =
            &def.param_def_with_dom
        {
            let instantiated_types = self.inst_param_def_with_type_one_by_one(
                parameter_definition,
                &struct_obj.params,
                ParamObjType::DefHeader,
            )?;
            let flat_types =
                parameter_definition.flat_instantiated_types_for_args(&instantiated_types);
            for (argument_index, (argument, expected_type)) in struct_obj
                .params
                .iter()
                .zip(flat_types.into_iter())
                .enumerate()
            {
                let result = self.verify_obj_satisfies_param_type(
                    argument.clone(),
                    &expected_type,
                    verify_state,
                )?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "failed to verify struct `{structure_name}` arguments satisfy parameter types"
                        )),
                    )));
                }
                header_arguments.push(SuccessVerifyStructureHeaderArgumentResult {
                    argument_index,
                    argument: argument.clone(),
                    expected_type,
                    verification: super::success_obj_fact_check(result)?,
                });
            }
            let param_to_arg_map =
                parameter_definition.param_defs_and_args_to_param_to_arg_map(&struct_obj.params);
            for domain in domains {
                let proposition = self
                    .inst_quantifier_free_fact(
                        domain,
                        &param_to_arg_map,
                        ParamObjType::DefHeader,
                        None,
                    )
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "failed to instantiate struct `{structure_name}` domain fact"
                                ),
                                error,
                            ),
                        ))
                    })?;
                let result = self.verify_quantifier_free_fact(&proposition, verify_state)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "failed to verify struct `{structure_name}` domain fact:\n{proposition}"
                        )),
                    )));
                }
                header_domains.push(super::success_obj_fact_check(result)?);
            }
            param_to_arg_map
        } else {
            HashMap::new()
        };

        let structure = self.run_in_local_env(|runtime| {
            let field_bindings = def
                .fields
                .iter()
                .map(|field| field.binding.clone())
                .collect::<Vec<_>>();
            let field_rename_map = runtime.visible_binding_conflict_rename_map(
                &field_bindings,
                ParamObjType::DefStructField,
            )?;
            let active_field_bindings = def
                .fields
                .iter()
                .map(
                    |field| match field_rename_map.get(&field.binding.substitution_key()) {
                        Some(Obj::Atom(AtomObj::DefStructField(parameter))) => {
                            parameter.symbol.to_local_binding()
                        }
                        _ => field.binding.clone(),
                    },
                )
                .collect::<Vec<_>>();

            let mut fields = Vec::with_capacity(def.fields.len());
            for (field_index, (field_binding, field)) in active_field_bindings
                .iter()
                .zip(def.fields.iter())
                .enumerate()
            {
                let instantiated_field_type = runtime.inst_obj(
                    &field.field_type,
                    &param_to_arg_map,
                    ParamObjType::DefHeader,
                )?;
                let instantiated_field_type = runtime.inst_obj(
                    &instantiated_field_type,
                    &field_rename_map,
                    ParamObjType::AlphaRename,
                )?;
                let carrier = runtime.verify_child_obj_well_defined_result(
                    &instantiated_field_type,
                    verify_state,
                    WellDefinedObjChildRole::BinderParameterCarrier {
                        parameter_group_index: field_index,
                    },
                )?;
                runtime.store_parameter_binding(field_binding, ParamObjType::DefStructField)?;
                let proposition: Fact = InFact::new(
                    obj_for_bound_param_in_scope(field_binding, ParamObjType::DefStructField),
                    instantiated_field_type,
                    default_line_file(),
                )
                .into();
                let well_definedness =
                    runtime.verify_fact_well_defined_result(&proposition, verify_state)?;
                let Fact::AtomicFact(atomic) = proposition.clone() else {
                    unreachable!("structure-field membership is atomic")
                };
                let mut infers = runtime
                    .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                        atomic,
                        InferReason::ParameterDefinition.store_reason(),
                    )?;
                runtime.attach_known_fact_ids_to_infer_result(&mut infers)?;
                let premise = SuccessVerifyBinderPremiseResult::new(
                    WellDefinedBinderPremiseRole::ParameterMembership {
                        parameter_group_index: field_index,
                        parameter_index: 0,
                    },
                    Some(field_binding.id()),
                    proposition,
                    well_definedness,
                    infers,
                );
                fields.push(SuccessVerifyStructureFieldResult {
                    field_index,
                    field_name: field.name().to_string(),
                    carrier,
                    premise,
                });
            }

            let mut equivalent_facts = Vec::with_capacity(def.equivalent_facts.len());
            for (fact_index, fact) in def.equivalent_facts.iter().enumerate() {
                let proposition =
                    runtime.inst_fact(fact, &param_to_arg_map, ParamObjType::DefHeader, None)?;
                let proposition = runtime.inst_fact(
                    &proposition,
                    &field_rename_map,
                    ParamObjType::AlphaRename,
                    None,
                )?;
                let well_definedness =
                    runtime.verify_fact_well_defined_result(&proposition, verify_state)?;
                let mut infers = runtime
                    .store_fact_without_well_defined_verified_and_without_infer_with_reason(
                        proposition.clone(),
                        InferReason::ByDefinition,
                    )?;
                runtime.attach_known_fact_ids_to_infer_result(&mut infers)?;
                let fact_id = runtime.known_fact_id_for_fact(&proposition)?;
                equivalent_facts.push(SuccessVerifyStructureEquivalentFactResult {
                    fact_index,
                    proposition: proposition.clone(),
                    well_definedness: Box::new(well_definedness),
                    store: SuccessStoreFactResult {
                        fact: proposition,
                        fact_id,
                        infers,
                    },
                });
            }
            Ok::<_, RuntimeError>((fields, equivalent_facts))
        })?;
        steps.binder = Some(Box::new(
            SuccessVerifyBinderObjectWellDefinedResult::Structure(Box::new(
                SuccessVerifyStructureWellDefinedResult {
                    structure_name,
                    header_arguments,
                    header_domains,
                    fields: structure.0,
                    equivalent_facts: structure.1,
                },
            )),
        ));
        Ok(steps)
    }

    pub(in crate::verify) fn verify_obj_as_struct_instance_with_field_access_well_defined_result(
        &mut self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        let structure_carrier: Obj = field_access.struct_obj.as_ref().clone().into();
        steps.push_child(self.verify_child_obj_well_defined_result(
            &structure_carrier,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 0 },
        )?);
        self.struct_field_index(&field_access.struct_obj, &field_access.field_name)?;
        steps.push_child(self.verify_child_obj_well_defined_result(
            &field_access.obj,
            verify_state,
            WellDefinedObjChildRole::ConstructorArgument { argument_index: 1 },
        )?);
        let membership: AtomicFact = InFact::new(
            (*field_access.obj).clone(),
            (*field_access.struct_obj).clone().into(),
            default_line_file(),
        )
        .into();
        let result = self.verify_atomic_fact(&membership, verify_state)?;
        if result.is_unknown() {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "failed to verify `{field_access}` is well-defined: cannot prove {membership}"
                )),
            )));
        }
        steps.push_fact_check(super::success_obj_fact_check(result)?);
        Ok(steps)
    }

    pub(in crate::verify) fn verify_instantiated_template_obj_well_defined_result(
        &mut self,
        template_obj: &InstantiatedTemplateObj,
        verify_state: &UseContextVerifyState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        for (argument_index, argument) in template_obj.args.iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                argument,
                verify_state,
                WellDefinedObjChildRole::ConstructorArgument { argument_index },
            )?);
        }
        steps.template_materialization = Some(Box::new(
            self.materialize_instantiated_template_obj_result(template_obj, verify_state)?,
        ));
        Ok(steps)
    }

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
            self.verify_obj_well_defined_as_verification_dependency(arg, verify_state)?;
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
                    .inst_quantifier_free_fact(
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
                    self.verify_quantifier_free_fact(&instantiated_dom_fact, verify_state)?;
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

    /// Mathematical contract: the carrier of `value.field` is the field's
    /// declared carrier after substituting both struct header arguments and
    /// declaration-owned field projections of `value`.
    pub(crate) fn instantiated_struct_field_type_for_access(
        &mut self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
        verify_state: &UseContextVerifyState,
    ) -> Result<Obj, RuntimeError> {
        let (def, header_map) =
            self.struct_header_param_to_arg_map(&field_access.struct_obj, verify_state)?;
        let field_index =
            self.struct_field_index(&field_access.struct_obj, &field_access.field_name)? - 1;

        let mut field_map = HashMap::new();
        for field in def.fields.iter() {
            let field_value: Obj = ObjAsStructInstanceWithFieldAccess::new(
                (*field_access.struct_obj).clone(),
                (*field_access.obj).clone(),
                field.name().to_string(),
            )
            .into();
            insert_symbol_substitution(&mut field_map, &field.binding, field_value);
        }

        let after_header = self.inst_obj(
            &def.fields[field_index].field_type,
            &header_map,
            ParamObjType::DefHeader,
        )?;
        self.inst_obj(&after_header, &field_map, ParamObjType::DefStructField)
    }

    /// Field membership dispatch reaches this only after the field expression
    /// itself has passed ordinary well-definedness.
    pub(crate) fn instantiated_struct_field_type_after_well_defined(
        &mut self,
        field_access: &ObjAsStructInstanceWithFieldAccess,
    ) -> Result<Obj, RuntimeError> {
        self.instantiated_struct_field_type_for_access(
            field_access,
            &UseContextVerifyState::new(0, true),
        )
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
}
