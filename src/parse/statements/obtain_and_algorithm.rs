//! `obtain`, preimage, and algorithm-branch statements.

use crate::prelude::*;

impl Runtime {
    pub fn parse_obtain_obj(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(OBTAIN)?;

        let mut equal_tos = vec![];
        loop {
            if tb.current_token_is_equal_to(FROM) {
                if equal_tos.is_empty() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "`obtain` expects at least one name before `from`".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                break;
            }
            let name = tb.advance()?;
            is_valid_litex_name(&name).map_err(|msg| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                ))
            })?;
            equal_tos.push(name);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            } else if !tb.current_token_is_equal_to(FROM) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "`obtain` expects `,` or `from` after each name".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        }

        tb.skip_token(FROM)?;
        let source_line_file = tb.line_file.clone();
        let obtain_source_error = |msg: String| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, source_line_file.clone()),
            ))
        };
        let mut source_atomic_fact = None;
        let mut source_thm_call = None;
        let true_fact = if tb.current_token_is_equal_to(EXIST) {
            Some(self.parse_exist_fact(tb)?)
        } else if tb.current_token_is_equal_to(THM) {
            tb.skip_token(THM)?;
            let (thm_name, args) = self.parse_theorem_call(tb)?;
            let preview = self.preview_obtain_obj_from_thm(&thm_name, &args, &source_line_file)?;
            source_thm_call = Some((thm_name, args));
            preview
        } else {
            let source_atomic = self.parse_atomic_fact(tb, true)?;
            let AtomicFact::NormalAtomicFact(source_prop) = source_atomic else {
                return Err(obtain_source_error(
                    "`obtain` expects a positive `exist`/`exist!` fact or a positive prop fact after `from`"
                        .to_string(),
                ));
            };
            let predicate_name = source_prop.predicate.to_string();
            let Some(definition) = self.get_active_prop_definition_by_name(&predicate_name) else {
                let message = if self
                    .get_abstract_prop_definition_by_name(&predicate_name)
                    .is_some()
                {
                    format!(
                        "`obtain ... from {}` requires a concrete `prop` definition; `abstract_prop` has no existential body",
                        source_prop
                    )
                } else {
                    format!(
                        "`obtain ... from {}` could not find a concrete prop definition",
                        source_prop
                    )
                };
                return Err(obtain_source_error(message));
            };
            if definition.iff_facts.len() != 1 {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` requires `{}` to have exactly one definition clause, which must be `exist` or `exist!`",
                    source_prop, predicate_name
                )));
            }
            let Fact::ExistFact(definition_exist_fact) = &definition.iff_facts[0] else {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` requires the sole definition clause of `{}` to be `exist` or `exist!`",
                    source_prop, predicate_name
                )));
            };
            if definition_exist_fact.is_not_exist() {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` cannot eliminate a `not exist` definition clause",
                    source_prop
                )));
            }
            let expected_args = definition.params_def_with_type.number_of_params();
            if source_prop.body.len() != expected_args {
                return Err(obtain_source_error(format!(
                    "`obtain ... from {}` expected {} prop argument(s), got {}",
                    source_prop,
                    expected_args,
                    source_prop.body.len()
                )));
            }
            let param_to_arg_map = self
                .params_to_arg_map(&definition.params_def_with_type, &source_prop.body)
                .map_err(|cause| {
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to instantiate existential definition of `{}`",
                            predicate_name
                        ),
                        source_line_file.clone(),
                        Some(cause),
                        vec![],
                    )))
                })?;
            let instantiated_exist_fact = self
                .inst_exist_fact(
                    definition_exist_fact,
                    &param_to_arg_map,
                    ParamObjType::DefHeader,
                    Some(&source_line_file),
                )
                .map_err(|cause| {
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to instantiate existential definition of `{}`",
                            predicate_name
                        ),
                        source_line_file.clone(),
                        Some(cause),
                        vec![],
                    )))
                })?;
            source_atomic_fact = Some(source_prop);
            Some(instantiated_exist_fact)
        };
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after `obtain` source fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        self.register_collected_param_names_for_def_parse(&equal_tos, tb.line_file.clone())?;
        let equal_to_bindings = self.allocate_local_symbol_bindings(&equal_tos)?;

        if let Some(true_fact) = true_fact.as_ref() {
            let exist_param_defs = true_fact.params_def_with_type();
            if exist_param_defs.number_of_params() == equal_to_bindings.len() {
                let equal_to_objs = equal_to_bindings
                    .iter()
                    .map(|binding| {
                        param_binding_element_obj_for_store(binding, ParamObjType::Identifier)
                    })
                    .collect::<Vec<_>>();
                let param_to_arg_map =
                    exist_param_defs.param_defs_and_args_to_param_to_arg_map(&equal_to_objs);
                let mut default_struct_views = Vec::new();
                let mut equal_to_index = 0;

                for param_group in exist_param_defs.groups.iter() {
                    for _ in param_group.params.iter() {
                        if let ParamType::Obj(Obj::StructObj(_)) = &param_group.param_type {
                            let instantiated_type = self.inst_param_type(
                                &param_group.param_type,
                                &param_to_arg_map,
                                ParamObjType::Exist,
                            )?;
                            if let ParamType::Obj(Obj::StructObj(struct_obj)) = instantiated_type {
                                default_struct_views
                                    .push((equal_to_bindings[equal_to_index].clone(), struct_obj));
                            }
                        }
                        equal_to_index += 1;
                    }
                }

                for (binding, struct_obj) in default_struct_views {
                    self.register_default_struct_view(std::slice::from_ref(&binding), &struct_obj);
                }
            }
        }

        self.register_local_existing_identifier_bindings_for_parse(
            &equal_to_bindings,
            tb.line_file.clone(),
        )?;

        let stmt = match (source_thm_call, source_atomic_fact, true_fact) {
            (Some((thm_name, args)), None, _) => {
                ObtainObjFromThm::new(equal_to_bindings, thm_name, args, tb.line_file.clone())
                    .into()
            }
            (None, Some(fact), _) => {
                ObtainObjFromAtomicFact::new(equal_to_bindings, fact, tb.line_file.clone()).into()
            }
            (None, None, Some(fact)) => {
                ObtainObjFromExistFact::new(equal_to_bindings, fact, tb.line_file.clone()).into()
            }
            _ => unreachable!("obtain parser must retain exactly one source form"),
        };
        Ok(stmt)
    }

    /// Preview a locally resolvable theorem only to register dependent struct
    /// views for the names introduced by `obtain`. Execution resolves and
    /// validates the theorem again; no theorem definition or existential fact
    /// is cached in the statement.
    fn preview_obtain_obj_from_thm(
        &self,
        thm_name: &AtomicName,
        args: &[Obj],
        line_file: &LineFile,
    ) -> Result<Option<ExistFactEnum>, RuntimeError> {
        let Some(forall_fact) = self.get_thm_or_axiom_forall_fact_by_name(&thm_name.to_string())
        else {
            // Reserved builtin theorem interfaces are execution-owned. An
            // unresolved user/imported theorem likewise receives its normal
            // authoritative diagnostic during execution.
            return Ok(None);
        };
        if forall_fact.then_facts.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "obtain from thm `{}` requires exactly one direct theorem conclusion, got {}",
                        thm_name,
                        forall_fact.then_facts.len()
                    ),
                    line_file.clone(),
                ),
            )));
        }
        let ExistOrAndChainAtomicFact::ExistFact(exist_fact) = &forall_fact.then_facts[0] else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "obtain from thm `{}` requires its sole direct conclusion to be `exist` or `exist!`",
                        thm_name
                    ),
                    line_file.clone(),
                ),
            )));
        };
        if exist_fact.is_not_exist() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "obtain from thm `{}` cannot eliminate a `not exist` conclusion",
                        thm_name
                    ),
                    line_file.clone(),
                ),
            )));
        }
        let Ok(param_to_arg_map) = self.params_to_arg_map(&forall_fact.params_def_with_type, args)
        else {
            // Preview data is optional. The executor owns theorem arity and
            // argument diagnostics through the ordinary `by thm` path.
            return Ok(None);
        };
        Ok(self
            .inst_exist_fact(
                exist_fact,
                &param_to_arg_map,
                ParamObjType::TheoremInstantiation,
                Some(line_file),
            )
            .ok())
    }

    pub fn parse_have_preimage(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(BY)?;
        tb.skip_token(PREIMAGE)?;

        let mut preimage_names = Vec::new();
        loop {
            if tb.current_token_is_equal_to(FROM) {
                if preimage_names.is_empty() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "have by preimage expects at least one preimage name".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                break;
            }
            let name = tb.advance()?;
            is_valid_litex_name(&name).map_err(|msg| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                ))
            })?;
            preimage_names.push(name);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            } else if tb.current_token_is_equal_to(FROM) {
                break;
            } else {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have by preimage expects `,` or `from` after a preimage name".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        }

        tb.skip_token(FROM)?;
        let source_fact = self.parse_atomic_fact(tb, true)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "unexpected token after have by preimage source fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let range_membership = match source_fact {
            AtomicFact::InFact(in_fact) => in_fact,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "have by preimage expects `from z $in fn_range(f)` or `from z $in replacement(P, A)`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };

        self.register_collected_param_names_for_def_parse(&preimage_names, tb.line_file.clone())?;
        let preimage_bindings = self.allocate_local_symbol_bindings(&preimage_names)?;
        self.register_local_existing_identifier_bindings_for_parse(
            &preimage_bindings,
            tb.line_file.clone(),
        )?;

        Ok(
            HaveByPreimageStmt::new(preimage_bindings, range_membership, tb.line_file.clone())
                .into(),
        )
    }

    /// Parses `have algo for f(a, b):` as an executable implementation of `f`.
    pub fn parse_have_algo_for_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(HAVE)?;
        tb.skip_token(ALGO)?;
        tb.skip_token(FOR)?;
        let name = tb.advance()?;
        self.run_in_local_parsing_time_name_scope(move |this| {
            tb.skip_token(LEFT_BRACE)?;
            let mut params: Vec<String> = vec![];
            while tb.current()? != RIGHT_BRACE {
                params.push(tb.advance()?);
                if tb.current_token_is_equal_to(COMMA) {
                    tb.skip_token(COMMA)?;
                }
            }
            tb.skip_token(RIGHT_BRACE)?;
            this.register_collected_param_names_for_def_parse(&params, tb.line_file.clone())?;
            tb.skip_token(COLON)?;
            let param_bindings =
                this.begin_parsing_scope(ParamObjType::DefAlgo, &params, tb.line_file.clone())?;
            let params_for_end = params.clone();
            let algo_result = (|| -> Result<DefAlgoStmt, RuntimeError> {
                let mut algo_cases: Vec<AlgoCase> = vec![];
                let mut default_return: Option<AlgoReturn> = None;
                match tb.body.split_last_mut() {
                    None => {}
                    Some((last_block, leading_blocks)) => {
                        for block in leading_blocks.iter_mut() {
                            algo_cases.push(this.parse_algo_case(block)?);
                        }
                        if last_block.current_token_empty_if_exceed_end_of_head() == CASE {
                            algo_cases.push(this.parse_algo_case(last_block)?);
                        } else {
                            default_return = Some(this.parse_algo_return(last_block)?);
                        }
                    }
                }
                Ok(DefAlgoStmt::new(
                    name,
                    param_bindings,
                    algo_cases,
                    default_return,
                    tb.line_file.clone(),
                ))
            })();
            this.end_parsing_scope(ParamObjType::DefAlgo, &params_for_end);
            Ok(algo_result?.into())
        })
    }

    /// Parses one `case <condition>: <return>` branch in a function implementation.
    fn parse_algo_case(&mut self, block: &mut TokenBlock) -> Result<AlgoCase, RuntimeError> {
        block.skip_token(CASE)?;
        let condition = self.parse_atomic_fact(block, true)?;
        block.skip_token(COLON)?;

        let return_stmt = self.parse_algo_return(block)?;
        Ok(AlgoCase::new(
            condition,
            return_stmt,
            block.line_file.clone(),
        ))
    }

    /// Parses the return object for an algorithm branch or default return.
    fn parse_algo_return(&mut self, block: &mut TokenBlock) -> Result<AlgoReturn, RuntimeError> {
        let value = self.parse_obj(block)?;
        Ok(AlgoReturn::new(value, block.line_file.clone()))
    }
}
