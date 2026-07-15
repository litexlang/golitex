use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
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

    pub(in crate::verify) fn verify_identifier_with_mod_well_defined(
        &self,
        x: &IdentifierWithMod,
    ) -> Result<(), RuntimeError> {
        if self.is_current_parse_module(&x.mod_name) {
            for env in self.iter_environments_from_top() {
                if env.defined_identifiers.contains_key(&x.name)
                    || env.defined_structs.contains_key(&x.name)
                {
                    return Ok(());
                }
            }
        } else {
            for env in self.imported_module_environments(&x.mod_name) {
                if env.defined_identifiers.contains_key(&x.name)
                    || env.defined_structs.contains_key(&x.name)
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

    pub(in crate::verify) fn verify_fn_obj_well_defined(
        &mut self,
        fn_obj: &FnObj,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let candidate_spaces = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(a) => {
                self.verify_anonymous_fn_well_defined(a.as_ref(), verify_state)
                    .map_err(|well_defined_error| {
                        RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                                "object {} is not well-defined: anonymous function head is not well-defined",
                                fn_obj.to_string()
                            ), well_defined_error)))
                    })?;
                vec![FnSetSpace::Anon((**a).clone())]
            }
            FnObjHead::FiniteSeqListObj(list) => {
                for obj in list.objs.iter() {
                    self.verify_obj_well_defined_and_store_cache(obj, verify_state)?;
                }
                if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "finite sequence literal function {} expects one argument",
                            fn_obj.head
                        )),
                    )));
                }
                let index_obj = fn_obj.body[0][0].as_ref().clone();
                self.verify_obj_well_defined_and_store_cache(&index_obj, verify_state)?;
                let index_in_n_pos: AtomicFact = InFact::new(
                    index_obj.clone(),
                    StandardSet::NPos.into(),
                    default_line_file(),
                )
                .into();
                let index_in_n_pos_result =
                    self.verify_atomic_fact(&index_in_n_pos, verify_state)?;
                if index_in_n_pos_result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "index {} is not a positive integer",
                            index_obj
                        )),
                    )));
                }
                let list_len_obj: Obj = Number::new(list.objs.len().to_string()).into();
                let index_not_larger_than_list_len: AtomicFact = LessEqualFact::new(
                    index_obj.clone(),
                    list_len_obj.clone(),
                    default_line_file(),
                )
                .into();
                let index_not_larger_than_list_len_result =
                    self.verify_atomic_fact(&index_not_larger_than_list_len, verify_state)?;
                if index_not_larger_than_list_len_result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "{} <= {} is unknown",
                            index_obj, list_len_obj
                        )),
                    )));
                }
                return Ok(());
            }
            FnObjHead::InstantiatedTemplateObj(template_obj) => {
                let function_name_obj: Obj = template_obj.clone().into();
                self.verify_obj_well_defined_and_store_cache(&function_name_obj, verify_state)?;
                let bodies = self.get_cloned_object_in_fn_set_candidates(&function_name_obj);
                if bodies.is_empty() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "function `{}` not defined",
                            fn_obj.head.to_string()
                        )),
                    )));
                }
                let mut spaces = Vec::with_capacity(bodies.len());
                for body in bodies {
                    spaces.push(FnSetSpace::Set(FnSet::from_body(body)?));
                }
                spaces
            }
            _ => {
                let function_name_obj: Obj = (*fn_obj.head).clone().into();
                let bodies = self.get_cloned_object_in_fn_set_candidates(&function_name_obj);
                if bodies.is_empty() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "function `{}` not defined",
                            fn_obj.head.to_string()
                        )),
                    )));
                }
                let mut spaces = Vec::with_capacity(bodies.len());
                for body in bodies {
                    spaces.push(FnSetSpace::Set(FnSet::from_body(body)?));
                }
                spaces
            }
        };

        if candidate_spaces.len() == 1 {
            return self.verify_fn_obj_well_defined_against_space(
                fn_obj,
                candidate_spaces[0].clone(),
                verify_state,
            );
        }

        let mut last_error: Option<RuntimeError> = None;
        for space in candidate_spaces.iter() {
            let trial = self.run_in_local_env(|rt| {
                rt.verify_fn_obj_well_defined_against_space(fn_obj, space.clone(), verify_state)
            });
            match trial {
                Ok(()) => {
                    return self.verify_fn_obj_well_defined_against_space(
                        fn_obj,
                        space.clone(),
                        verify_state,
                    );
                }
                Err(e) => last_error = Some(e),
            }
        }

        Err(RuntimeError::from(WellDefinedRuntimeError(
            RuntimeErrorStruct::new(
                None,
                format!(
                    "object {} is not well-defined, no function domain matched.",
                    fn_obj
                ),
                default_line_file(),
                last_error,
                vec![],
            ),
        )))
    }

    pub(in crate::verify) fn verify_fn_obj_well_defined_against_space(
        &mut self,
        fn_obj: &FnObj,
        mut space: FnSetSpace,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        for (i, args) in fn_obj.body.iter().enumerate() {
            self.verify_fn_obj_well_defined_against_fn_like_space(
                args,
                space.params(),
                space.dom(),
                space.binding(),
                verify_state,
            )
            .map_err(|well_defined_error| {
                RuntimeError::from(WellDefinedRuntimeError(RuntimeErrorStruct::new_with_msg_and_cause(format!(
                        "object {} is not well-defined, failed to verify arguments satisfy function domain.",
                        fn_obj.to_string()
                    ), well_defined_error)))
            })?;

            let set_where_the_next_fn_obj_is_in = space.ret_set_obj();

            let fn_obj_prefix_body: Vec<Vec<Box<Obj>>> =
                fn_obj.body[..=i].iter().cloned().collect();
            let fn_obj_prefix_as_obj: Obj =
                FnObj::new(*fn_obj.head.clone(), fn_obj_prefix_body).into();
            let intermediate_in_fact = InFact::new(
                fn_obj_prefix_as_obj,
                set_where_the_next_fn_obj_is_in,
                default_line_file(),
            );
            let intermediate_atomic_fact = AtomicFact::InFact(intermediate_in_fact);
            let intermediate_line_file = intermediate_atomic_fact.line_file();
            let intermediate_fact_string = intermediate_atomic_fact.to_string();
            self.top_level_env()
                .store_atomic_fact(intermediate_atomic_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to store intermediate fn-obj membership fact while verifying `{}`",
                                fn_obj.to_string()
                            ),
                            store_fact_error,
                        ),
                    ))
                })?;
            self.top_level_env()
                .store_fact_to_cache_known_fact(intermediate_fact_string, intermediate_line_file)
                .map_err(|store_fact_error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                        "failed to store intermediate fn-obj membership fact while verifying `{}`",
                        fn_obj.to_string()
                    ),
                            store_fact_error,
                        ),
                    ))
                })?;

            if i == fn_obj.body.len() - 1 {
                break;
            }

            space = self.fn_set_space_from_return_set_obj(space.ret_set_obj())?;
        }

        Ok(())
    }

    pub(in crate::verify) fn verify_fn_obj_well_defined_against_fn_like_space(
        &mut self,
        args: &Vec<Box<Obj>>,
        params_def_with_set: &ParamDefWithSet,
        dom_facts: &Vec<OrAndChainAtomicFact>,
        param_binding: ParamObjType,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let param_count = params_def_with_set.number_of_params();
        if args.len() != param_count {
            return Err(RuntimeError::from(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_just_msg(format!(
                    "number of args ({}) does not match fn set with dom param finite_set_size({})",
                    args.len(),
                    param_count
                )),
            )));
        }

        for arg in args.iter() {
            self.verify_obj_well_defined_and_store_cache(arg, verify_state)?;
        }

        let mut args_as_obj: Vec<Obj> = Vec::with_capacity(args.len());
        for arg in args.iter() {
            args_as_obj.push((**arg).clone());
        }

        self.verify_args_satisfy_fn_param_groups(
            params_def_with_set,
            &args_as_obj,
            param_binding,
            verify_state,
        )?;

        let param_to_arg_map =
            params_def_with_set.param_defs_and_args_to_param_to_arg_map(&args_as_obj);
        for dom_fact in dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(dom_fact, &param_to_arg_map, param_binding, None)
                .map_err(|e| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!("failed to instantiate function domain fact: {}", e),
                            e,
                        ),
                    ))
                })?;
            let verify_result = self
                .verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)
                .map_err(|verify_error| {
                    RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_cause(
                            format!(
                                "failed to verify function domain fact:\n{}",
                                instantiated_dom_fact
                            ),
                            verify_error,
                        ),
                    ))
                })?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::from(WellDefinedRuntimeError(
                    RuntimeErrorStruct::new_with_just_msg(format!(
                        "failed to verify function domain fact:\n{}",
                        instantiated_dom_fact
                    )),
                )));
            }
        }

        Ok(())
    }

    pub(in crate::verify) fn verify_args_satisfy_fn_param_groups(
        &mut self,
        params_def_with_set: &ParamDefWithSet,
        args_as_obj: &Vec<Obj>,
        param_binding: ParamObjType,
        verify_state: &VerifyState,
    ) -> Result<(), RuntimeError> {
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        let mut arg_index: usize = 0;
        for (group_index, param_def) in params_def_with_set.groups.iter().enumerate() {
            let param_type =
                if !params_def_with_set.param_set_cited_param_indices[group_index].is_empty() {
                    ParamType::Obj(self.inst_obj(
                        param_def.set_obj(),
                        &param_to_arg_map,
                        param_binding,
                    )?)
                } else {
                    ParamType::Obj(param_def.set_obj().clone())
                };

            for param_name in param_def.params.iter() {
                let arg = args_as_obj[arg_index].clone();
                let mut verify_result = self
                    .verify_obj_satisfies_param_type(arg.clone(), &param_type, verify_state)
                    .map_err(|verify_error| {
                        RuntimeError::from(WellDefinedRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_cause(
                                format!(
                                    "failed to verify arg `{}` satisfy fn parameter type {}",
                                    arg, param_type
                                ),
                                verify_error,
                            ),
                        ))
                    })?;
                if verify_result.is_unknown() {
                    let resolved_arg = self.resolve_obj(&arg);
                    if resolved_arg.to_string() != arg.to_string() {
                        verify_result = self.verify_obj_satisfies_param_type(
                            resolved_arg,
                            &param_type,
                            verify_state,
                        )?;
                    }
                }
                if verify_result.is_unknown() {
                    return Err(RuntimeError::from(WellDefinedRuntimeError(
                        RuntimeErrorStruct::new_with_just_msg(format!(
                            "arg `{}` does not satisfy fn parameter type {}",
                            arg, param_type
                        )),
                    )));
                }
                param_to_arg_map.insert(param_name.clone(), arg);
                arg_index += 1;
            }
        }
        Ok(())
    }
}
