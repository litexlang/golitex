//! Core recursive object well-definedness helpers.

use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    /// Recover callable contracts carried by the submitted object's own
    /// shape. This lookup does not search equality representatives or unfold
    /// definitions: callers decide explicitly when one transparent `let`
    /// reduction is permitted before submitting the resulting object here.
    pub(in crate::verify) fn derive_callable_space_candidates_from_obj_shape(
        &mut self,
        obj: &Obj,
    ) -> Result<Vec<FnSetSpace>, RuntimeError> {
        if let Some(body) = self.get_direct_object_in_fn_set(obj) {
            return Ok(vec![FnSetSpace::Set(FnSet::from_body(body)?)]);
        }

        let Obj::ObjAsStructInstanceWithFieldAccess(field_access) = obj else {
            return Ok(Vec::new());
        };
        let field_type = self.instantiated_struct_field_type_after_well_defined(field_access)?;
        Ok(self
            .fn_set_space_from_return_set_obj(field_type)
            .ok()
            .into_iter()
            .collect())
    }

    pub(in crate::verify) fn verify_fn_obj_well_defined_result(
        &mut self,
        fn_obj: &FnObj,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let mut head_steps = SuccessVerifyObjWellDefinedStepsResult::new();
        let candidate_spaces = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(value) => {
                let head: Obj = value.as_ref().clone().into();
                head_steps.push_child(
                    self.verify_child_obj_well_defined_result(
                        &head,
                        verify_state,
                        WellDefinedObjChildRole::FunctionHead,
                    )
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "object {fn_obj} is not well-defined: anonymous function head is not well-defined"
                                ),
                                error,
                            ),
                        ))
                    })?,
                );
                vec![FnSetSpace::Anon((**value).clone())]
            }
            FnObjHead::FiniteSeqListObj(list) => {
                let head: Obj = list.clone().into();
                head_steps.push_child(self.verify_child_obj_well_defined_result(
                    &head,
                    verify_state,
                    WellDefinedObjChildRole::FunctionHead,
                )?);
                if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "finite sequence literal function {} expects one argument",
                            fn_obj.head
                        )),
                    )));
                }
                let index = fn_obj.body[0][0].as_ref().clone();
                head_steps.push_child(self.verify_child_obj_well_defined_result(
                    &index,
                    verify_state,
                    WellDefinedObjChildRole::FunctionArgument {
                        layer_index: 0,
                        argument_index: 0,
                    },
                )?);
                let positive: AtomicFact =
                    InFact::new(index.clone(), StandardSet::NPos.into(), default_line_file())
                        .into();
                let result = self.verify_atomic_fact(&positive, verify_state)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "index {index} is not a positive integer"
                        )),
                    )));
                }
                head_steps.push_fact_check(super::success_obj_fact_check(result)?);
                let length: Obj = Number::new(list.objs.len().to_string()).into();
                let bounded: AtomicFact =
                    LessEqualFact::new(index.clone(), length.clone(), default_line_file()).into();
                let result = self.verify_atomic_fact(&bounded, verify_state)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{index} <= {length} is unknown"
                        )),
                    )));
                }
                head_steps.push_fact_check(super::success_obj_fact_check(result)?);
                return Ok(head_steps);
            }
            FnObjHead::MatrixOperator(matrix) => {
                head_steps.push_child(self.verify_child_obj_well_defined_result(
                    matrix,
                    verify_state,
                    WellDefinedObjChildRole::FunctionHead,
                )?);
                let matrix_set = self.real_matrix_type(matrix, verify_state, "entry access")?;
                vec![FnSetSpace::Set(
                    self.matrix_set_to_fn_set(&matrix_set, default_line_file()),
                )]
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
                let head: Obj = field_access.clone().into();
                head_steps.push_child(self.verify_child_obj_well_defined_result(
                    &head,
                    verify_state,
                    WellDefinedObjChildRole::FunctionHead,
                )?);
                let field_type =
                    self.instantiated_struct_field_type_for_access(field_access, verify_state)?;
                vec![self
                    .fn_set_space_from_return_set_obj(field_type.clone())
                    .map_err(|_| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_just_msg(format!(
                                "struct field `{}` is not callable; its defined carrier is {field_type}",
                                field_access.field_name
                            )),
                        ))
                    })?]
            }
            FnObjHead::InstantiatedTemplateObj(template_obj) => {
                let head: Obj = template_obj.clone().into();
                head_steps.push_child(self.verify_child_obj_well_defined_result(
                    &head,
                    verify_state,
                    WellDefinedObjChildRole::FunctionHead,
                )?);
                let bodies = self.get_cloned_object_in_fn_set_candidates(&head);
                if bodies.is_empty() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "function `{}` not defined",
                            fn_obj.head
                        )),
                    )));
                }
                bodies
                    .into_iter()
                    .map(|body| FnSet::from_body(body).map(FnSetSpace::Set))
                    .collect::<Result<Vec<_>, _>>()?
            }
            _ => {
                let function: Obj = (*fn_obj.head).clone().into();
                let bodies = self.get_cloned_object_in_fn_set_candidates(&function);
                let mut candidate_spaces = bodies
                    .into_iter()
                    .map(|body| FnSet::from_body(body).map(FnSetSpace::Set))
                    .collect::<Result<Vec<_>, _>>()?;
                if candidate_spaces.is_empty() {
                    let (resolved, transparent_definitions) =
                        self.resolve_transparent_obj_once(&function)?;
                    if !transparent_definitions.is_empty() {
                        candidate_spaces =
                            self.derive_callable_space_candidates_from_obj_shape(&resolved)?;
                    }
                }
                if candidate_spaces.is_empty() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "function `{}` not defined",
                            fn_obj.head
                        )),
                    )));
                }
                candidate_spaces
            }
        };

        if candidate_spaces.len() == 1 {
            let mut selected = self.verify_fn_obj_well_defined_against_space_result(
                fn_obj,
                candidate_spaces[0].clone(),
                verify_state,
            )?;
            head_steps.append(std::mem::take(&mut selected));
            return Ok(head_steps);
        }

        let mut selected_space = None;
        let mut last_error = None;
        for space in &candidate_spaces {
            let trial = self
                .run_in_local_env_and_take(|runtime| {
                    runtime.verify_fn_obj_well_defined_against_space_result(
                        fn_obj,
                        space.clone(),
                        verify_state,
                    )
                })
                .map(|(steps, _)| steps);
            match trial {
                Ok(_) => {
                    selected_space = Some(space.clone());
                    break;
                }
                Err(error) => last_error = Some(error),
            }
        }
        let selected_space = selected_space.ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new(
                None,
                format!("object {fn_obj} is not well-defined, no function domain matched."),
                default_line_file(),
                last_error,
                vec![],
            )))
        })?;
        let selected = self.verify_fn_obj_well_defined_against_space_result(
            fn_obj,
            selected_space,
            verify_state,
        )?;
        head_steps.append(selected);
        Ok(head_steps)
    }

    fn verify_fn_obj_well_defined_against_space_result(
        &mut self,
        fn_obj: &FnObj,
        mut space: FnSetSpace,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let source_application: Obj = fn_obj.clone().into();
        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        let last_layer_index = fn_obj.body.len().checked_sub(1).ok_or_else(|| {
            RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "function application `{fn_obj}` has no argument layer"
                )),
            ))
        })?;

        if last_layer_index > 0 {
            let prefix: Obj = FnObj::new_with_source_occurrence_id(
                *fn_obj.head.clone(),
                fn_obj.body[..last_layer_index].to_vec(),
                None,
            )
            .into();
            steps.push_child(self.verify_child_obj_well_defined_result(
                &prefix,
                verify_state,
                WellDefinedObjChildRole::FunctionPrefix {
                    through_layer_index: last_layer_index - 1,
                },
            )?);

            for arguments in &fn_obj.body[..last_layer_index] {
                let return_set = self.fn_set_return_set_after_args(&space, arguments)?;
                if let Obj::InstantiatedTemplateObj(template_obj) = &return_set {
                    self.instantiate_template_obj(template_obj, verify_state)?;
                }
                space = self.fn_set_space_from_return_set_obj(return_set)?;
            }
        }

        let arguments = &fn_obj.body[last_layer_index];
        let layer = self
            .verify_fn_obj_well_defined_against_fn_like_space_result(
                &source_application,
                last_layer_index,
                arguments,
                space.params(),
                space.dom(),
                SubstitutionMode::Exact,
                verify_state,
            )
            .map_err(|error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "object {fn_obj} is not well-defined, failed to verify arguments satisfy function domain."
                        ),
                        error,
                    ),
                ))
            })?;
        steps.append(layer);
        let return_set = self.fn_set_return_set_after_args(&space, arguments)?;
        let membership: AtomicFact =
            InFact::new(source_application, return_set, default_line_file()).into();
        let proposition: Fact = membership.clone().into();
        let mut infers = self
            .store_atomic_fact_without_well_defined_verified_and_infer(membership)
            .map_err(|error| {
                RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_cause(
                        format!(
                            "failed to store intermediate fn-obj membership fact while verifying `{fn_obj}`"
                        ),
                        error,
                    ),
                ))
            })?;
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        let fact_id = self.known_fact_id_for_fact(&proposition)?;
        steps.push_store(SuccessStoreFactResult {
            fact: proposition,
            fact_id,
            infers,
        });
        Ok(steps)
    }

    fn verify_fn_obj_well_defined_against_fn_like_space_result(
        &mut self,
        source_application: &Obj,
        layer_index: usize,
        arguments: &[Box<Obj>],
        parameters: &SetBoundParameterList,
        domains: &[QuantifierFreeFact],
        substitution_mode: SubstitutionMode,
        verify_state: &ProofSearchState,
    ) -> Result<SuccessVerifyObjWellDefinedStepsResult, RuntimeError> {
        let parameter_count = parameters.number_of_params();
        if arguments.len() != parameter_count {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "number of args ({}) does not match fn set with dom param finite_set_size({parameter_count})",
                    arguments.len()
                )),
            )));
        }

        let mut steps = SuccessVerifyObjWellDefinedStepsResult::new();
        let arguments_as_objects = arguments
            .iter()
            .map(|argument| argument.as_ref().clone())
            .collect::<Vec<_>>();
        for (argument_index, argument) in arguments_as_objects.iter().enumerate() {
            steps.push_child(self.verify_child_obj_well_defined_result(
                argument,
                verify_state,
                WellDefinedObjChildRole::FunctionArgument {
                    layer_index,
                    argument_index,
                },
            )?);
        }

        let mut substitutions = HashMap::new();
        let mut argument_index = 0;
        for (group_index, parameter_group) in parameters.groups.iter().enumerate() {
            let parameter_type = if !parameters
                .cited_param_indices_for_group(group_index)
                .is_empty()
            {
                ParamType::Obj(self.inst_obj(
                    parameter_group.set_obj(),
                    &substitutions,
                    substitution_mode,
                )?)
            } else {
                ParamType::Obj(parameter_group.set_obj().clone())
            };
            for parameter in &parameter_group.params {
                let argument = arguments_as_objects[argument_index].clone();
                let mut result = self
                    .verify_obj_satisfies_param_type(argument.clone(), &parameter_type, verify_state)
                    .map_err(|error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "failed to verify arg `{argument}` satisfy fn parameter type {parameter_type}"
                                ),
                                error,
                            ),
                        ))
                    })?;
                if result.is_unknown() {
                    let resolved = self.resolve_obj(&argument);
                    if resolved.to_string() != argument.to_string() {
                        result = self.verify_obj_satisfies_param_type(
                            resolved,
                            &parameter_type,
                            verify_state,
                        )?;
                    }
                }
                if result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "arg `{argument}` does not satisfy fn parameter type {parameter_type}"
                        )),
                    )));
                }
                steps.push_target_requirement(super::success_obj_target_requirement(
                    source_application.clone(),
                    WellDefinednessRequirementRole::FunctionArgumentMembership {
                        layer_index,
                        parameter_index: argument_index,
                    },
                    result,
                )?);
                insert_symbol_substitution(&mut substitutions, parameter, argument);
                argument_index += 1;
            }
        }

        let substitutions =
            parameters.param_defs_and_args_to_param_to_arg_map(&arguments_as_objects);
        for (domain_index, domain) in domains.iter().enumerate() {
            let instantiated = self
                .inst_quantifier_free_fact(domain, &substitutions, substitution_mode, None)
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to instantiate function domain fact: {error}"),
                            error,
                        ),
                    ))
                })?;
            let result = self
                .verify_quantifier_free_fact(&instantiated, verify_state)
                .map_err(|error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to verify function domain fact:\n{instantiated}"),
                            error,
                        ),
                    ))
                })?;
            if result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "failed to verify function domain fact:\n{instantiated}"
                    )),
                )));
            }
            steps.push_target_requirement(super::success_obj_target_requirement(
                source_application.clone(),
                WellDefinednessRequirementRole::FunctionDomain {
                    layer_index,
                    domain_index,
                },
                result,
            )?);
        }
        Ok(steps)
    }

    /// Mathematical contract: an unqualified symbol denotes an object only if
    /// that identifier or struct constructor is visible in the current scope.
    pub(in crate::verify) fn verify_identifier_well_defined(
        &self,
        identifier: &Identifier,
    ) -> Result<(), RuntimeError> {
        if self.is_name_used_for_identifier(&identifier.name) {
            Ok(())
        } else if self
            .get_struct_definition_by_name(&identifier.name)
            .is_some()
        {
            Ok(())
        } else {
            Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "identifier `{}` not defined",
                    identifier.to_string()
                )),
            )))
        }
    }

    /// Mathematical contract: a qualified symbol denotes an object only if
    /// its identifier or struct constructor exists in the named current or
    /// imported module.
    pub(in crate::verify) fn verify_identifier_with_mod_well_defined(
        &self,
        x: &IdentifierWithMod,
    ) -> Result<(), RuntimeError> {
        if self.is_current_parse_module(&x.mod_name) {
            for env in self.iter_environments_from_top() {
                if env.definitions.object_symbol(&x.name).is_some()
                    || env.definitions.structure_definitions.contains_key(&x.name)
                {
                    return Ok(());
                }
            }
        } else {
            for env in self.imported_module_environments(&x.mod_name) {
                if env.definitions.object_symbol(&x.name).is_some()
                    || env.definitions.structure_definitions.contains_key(&x.name)
                {
                    return Ok(());
                }
            }
        }

        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new_with_just_msg(format!(
                "identifier `{}` not defined",
                x.to_string()
            )),
        )))
    }
}
