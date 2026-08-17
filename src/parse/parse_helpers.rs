use crate::prelude::*;
use std::collections::HashMap;

pub(crate) struct FreshSettingParameterBundle {
    pub(crate) param_def: ParamDefWithType,
    pub(crate) dom_facts: Vec<Fact>,
}

impl Runtime {
    /// Parses `[Setting]` or `[Setting(fresh_name, ...)]` and elaborates it into
    /// ordinary parameters and facts in `target_kind`.
    ///
    /// Explicit arguments are declarations, never expressions or references to
    /// an outer binding. Each parameter is allocated afresh, while its type and
    /// the setting conditions are instantiated from the setting's `forall`
    /// binders into the target binding kind.
    pub(crate) fn parse_fresh_setting_parameter_bundle(
        &mut self,
        tb: &mut TokenBlock,
        target_kind: ParamObjType,
    ) -> Result<FreshSettingParameterBundle, RuntimeError> {
        tb.skip_token(LEFT_BRACKET)?;
        if tb.current_token_is_equal_to(RIGHT_BRACKET) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "setting parameter bundle cannot be empty".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let setting_name = self.parse_module_qualified_reference_name(tb)?.to_string();
        let explicit_names = if tb.current_token_is_equal_to(LEFT_BRACE) {
            tb.skip_token(LEFT_BRACE)?;
            let mut names = Vec::new();
            while !tb.current_token_is_equal_to(RIGHT_BRACE) {
                let name = tb.advance()?;
                self.validate_name(&name, tb.line_file.clone())?;
                names.push(name);
                if tb.current_token_is_equal_to(RIGHT_BRACE) {
                    break;
                }
                if !tb.current_token_is_equal_to(COMMA) {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "setting `{}` arguments must be bare binder names separated by `,`",
                                setting_name
                            ),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                tb.skip_token(COMMA)?;
            }
            tb.skip_token(RIGHT_BRACE)?;
            Some(names)
        } else {
            None
        };
        tb.skip_token(RIGHT_BRACKET)?;

        let setting = self
            .get_setting_definition_by_name(&setting_name)
            .ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("unknown setting `{}`", setting_name),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
        let source_bindings = setting.param_def.collect_param_bindings();
        let target_names = explicit_names.unwrap_or_else(|| {
            source_bindings
                .iter()
                .map(|binding| binding.name().to_string())
                .collect()
        });
        if target_names.len() != source_bindings.len() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "setting `{}` expects {} binder name(s), got {}",
                        setting_name,
                        source_bindings.len(),
                        target_names.len()
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }

        let mut source_to_target: HashMap<String, Obj> = HashMap::new();
        let mut groups = Vec::with_capacity(setting.param_def.groups.len());
        let mut target_index = 0;
        for source_group in &setting.param_def.groups {
            let instantiated_type = self.inst_param_type(
                &source_group.param_type,
                &source_to_target,
                ParamObjType::BinderRetag(BinderRetagSource::Forall),
            )?;
            let group_len = source_group.params.len();
            let group_names = target_names[target_index..target_index + group_len].to_vec();
            let target_bindings =
                self.begin_parsing_scope(target_kind, &group_names, tb.line_file.clone())?;
            if let ParamType::Obj(Obj::StructObj(struct_obj)) = &instantiated_type {
                self.register_default_struct_view(&target_bindings, struct_obj);
            }
            if let ParamType::Obj(Obj::Cart(cart)) = &instantiated_type {
                self.register_default_tuple_view(&target_bindings, cart);
            }
            for (source, target) in source_group.params.iter().zip(target_bindings.iter()) {
                insert_symbol_substitution(
                    &mut source_to_target,
                    source,
                    obj_for_bound_param_in_scope(target, target_kind),
                );
            }
            groups.push(ParamGroupWithParamType::new(
                target_bindings,
                instantiated_type,
            ));
            target_index += group_len;
        }

        let mut dom_facts = Vec::with_capacity(setting.dom_facts.len());
        for fact in &setting.dom_facts {
            dom_facts.push(self.inst_fact(
                fact,
                &source_to_target,
                ParamObjType::BinderRetag(BinderRetagSource::Forall),
                Some(tb.line_file.clone()),
            )?);
        }

        Ok(FreshSettingParameterBundle {
            param_def: ParamDefWithType::new(groups),
            dom_facts,
        })
    }

    pub(super) fn new_parsed_fn_obj(
        &self,
        head: FnObjHead,
        body: Vec<Vec<Box<Obj>>>,
    ) -> Result<Obj, RuntimeError> {
        Ok(FnObj::new_with_source_occurrence_id(
            head,
            body,
            Some(self.allocate_source_object_occurrence_id()?),
        )
        .into())
    }

    pub(super) fn new_parsed_add(&self, left: Obj, right: Obj) -> Result<Obj, RuntimeError> {
        Ok(Add::new_with_source_occurrence_id(
            left,
            right,
            Some(self.allocate_source_object_occurrence_id()?),
        )
        .into())
    }

    pub(super) fn new_parsed_sub(&self, left: Obj, right: Obj) -> Result<Obj, RuntimeError> {
        Ok(Sub::new_with_source_occurrence_id(
            left,
            right,
            Some(self.allocate_source_object_occurrence_id()?),
        )
        .into())
    }

    pub(super) fn new_parsed_mul(&self, left: Obj, right: Obj) -> Result<Obj, RuntimeError> {
        Ok(Mul::new_with_source_occurrence_id(
            left,
            right,
            Some(self.allocate_source_object_occurrence_id()?),
        )
        .into())
    }

    pub(super) fn new_parsed_div(&self, left: Obj, right: Obj) -> Result<Obj, RuntimeError> {
        Ok(Div::new_with_source_occurrence_id(
            left,
            right,
            Some(self.allocate_source_object_occurrence_id()?),
        )
        .into())
    }

    pub(super) fn new_parsed_list_set(&self, list: Vec<Obj>) -> Result<ListSet, RuntimeError> {
        Ok(ListSet::new_with_source_occurrence_id(
            list,
            Some(self.allocate_source_object_occurrence_id()?),
        ))
    }
}

pub(crate) fn collect_forall_param_bindings_from_facts(facts: &[Fact]) -> Vec<SymbolBinding> {
    let mut bindings = Vec::new();
    for fact in facts {
        if let Fact::ForallFact(forall_fact) = fact {
            for binding in forall_fact.params_def_with_type.collect_param_bindings() {
                if !bindings
                    .iter()
                    .any(|existing: &SymbolBinding| existing.id() == binding.id())
                {
                    bindings.push(binding);
                }
            }
        }
    }
    bindings
}

impl Runtime {
    pub(crate) fn parse_goal_fact_block(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> Result<Fact, RuntimeError> {
        require_question_goal(block, syntax_name)?;
        block.skip_token(QUESTION_GOAL)?;
        if block.exceed_end_of_head() {
            return Err(parse_goal_error(
                syntax_name,
                "`?` expects a fact",
                block.line_file.clone(),
            ));
        }
        let fact = self.parse_fact(block)?;
        if !block.exceed_end_of_head() {
            return Err(parse_goal_error(
                syntax_name,
                "unfinished tokens in `?` goal",
                block.line_file.clone(),
            ));
        }
        if !block.body.is_empty()
            && !matches!(
                &fact,
                Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_)
            )
        {
            return Err(parse_goal_error(
                syntax_name,
                "`?` body is only allowed for multiline `forall` facts",
                block.line_file.clone(),
            ));
        }
        Ok(fact)
    }

    pub(crate) fn parse_goal_fact_block_with_inline_proof(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> Result<(Fact, usize), RuntimeError> {
        Ok((self.parse_goal_fact_block(block, syntax_name)?, 0))
    }

    pub(crate) fn parse_goal_forall_fact_block_with_inline_proof(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> Result<(ForallFact, usize), RuntimeError> {
        let (fact, inline_proof_start) =
            self.parse_goal_fact_block_with_inline_proof(block, syntax_name)?;
        match fact {
            Fact::ForallFact(forall_fact) => Ok((forall_fact, inline_proof_start)),
            Fact::ForallFactWithIff(_) => Err(parse_goal_error(
                syntax_name,
                "forall with `<=>` is not allowed here",
                block.line_file.clone(),
            )),
            _ => Err(parse_goal_error(
                syntax_name,
                "goal must be a single `forall` fact",
                block.line_file.clone(),
            )),
        }
    }

    pub(crate) fn parse_goal_atomic_fact_block(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> Result<AtomicFact, RuntimeError> {
        require_question_goal(block, syntax_name)?;
        block.skip_token(QUESTION_GOAL)?;
        if block.exceed_end_of_head() {
            return Err(parse_goal_error(
                syntax_name,
                "`?` expects an atomic fact",
                block.line_file.clone(),
            ));
        }
        let fact = self.parse_atomic_fact(block, true)?;
        if !block.exceed_end_of_head() || !block.body.is_empty() {
            return Err(parse_goal_error(
                syntax_name,
                "unfinished tokens in `?` atomic goal",
                block.line_file.clone(),
            ));
        }
        Ok(fact)
    }

    pub(crate) fn parse_goal_forall_fact_block(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> Result<ForallFact, RuntimeError> {
        let fact = self.parse_goal_fact_block(block, syntax_name)?;
        match fact {
            Fact::ForallFact(forall_fact) => Ok(forall_fact),
            Fact::ForallFactWithIff(_) => Err(parse_goal_error(
                syntax_name,
                "forall with `<=>` is not allowed here",
                block.line_file.clone(),
            )),
            _ => Err(parse_goal_error(
                syntax_name,
                "goal must be a single `forall` fact",
                block.line_file.clone(),
            )),
        }
    }

    pub(crate) fn parse_goal_fact_list_blocks(
        &mut self,
        body: &mut [TokenBlock],
        syntax_name: &str,
        line_file: LineFile,
    ) -> Result<(Vec<Fact>, usize), RuntimeError> {
        if body.is_empty() {
            return Err(parse_goal_error(
                syntax_name,
                "expects one or more `? <fact>` goal blocks",
                line_file,
            ));
        }
        require_question_goal(&body[0], syntax_name)?;
        let mut facts = Vec::new();
        let mut consumed = 0;
        for block in body.iter_mut() {
            if !block.current_token_is_equal_to(QUESTION_GOAL) {
                break;
            }
            facts.push(self.parse_goal_fact_block(block, syntax_name)?);
            consumed += 1;
        }
        Ok((facts, consumed))
    }

    pub(crate) fn parse_question_goal_exist_or_and_chain_atomic_fact(
        &mut self,
        block: &mut TokenBlock,
        syntax_name: &str,
    ) -> Result<ExistOrAndChainAtomicFact, RuntimeError> {
        require_question_goal(block, syntax_name)?;
        block.skip_token(QUESTION_GOAL)?;
        if block.exceed_end_of_head() {
            return Err(parse_goal_error(
                syntax_name,
                "`?` expects a fact",
                block.line_file.clone(),
            ));
        }
        let fact = self.parse_exist_or_and_chain_atomic_fact(block)?;
        if !block.exceed_end_of_head() || !block.body.is_empty() {
            return Err(parse_goal_error(
                syntax_name,
                "unfinished tokens in `?` goal",
                block.line_file.clone(),
            ));
        }
        Ok(fact)
    }

    pub(crate) fn parse_header_fact_before_trailing_colon(
        &mut self,
        tb: &mut TokenBlock,
        syntax_name: &str,
        old_arrow_syntax: &str,
        new_syntax: &str,
    ) -> Result<Fact, RuntimeError> {
        if tb.current()? == RIGHT_ARROW {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "{}: use `{}` instead of `{}`",
                        syntax_name, new_syntax, old_arrow_syntax
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        let header = &tb.header;
        if header.len() < tb.parse_index + 2 || header.last().map(|t| t.as_str()) != Some(COLON) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "{}: expected a fact and a trailing `:` on the same line",
                        syntax_name
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        let colon_pos = header.len() - 1;
        let fact_tokens = header[tb.parse_index..colon_pos].to_vec();
        if fact_tokens.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("{}: expected a non-empty fact before `:`", syntax_name),
                    tb.line_file.clone(),
                ),
            )));
        }
        let mut fact_tb = TokenBlock::new(fact_tokens, vec![], tb.line_file.clone());
        let fact = self.parse_fact(&mut fact_tb)?;
        if !fact_tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("{}: unfinished tokens in header fact", syntax_name),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.parse_index = colon_pos + 1;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("{}: unexpected tokens after trailing `:`", syntax_name),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(fact)
    }

    pub(crate) fn parse_optional_trailing_proof_colon(
        &mut self,
        tb: &mut TokenBlock,
        syntax_name: &str,
    ) -> Result<bool, RuntimeError> {
        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("{}: unexpected token after trailing `:`", syntax_name),
                        tb.line_file.clone(),
                    ),
                )));
            }
            return Ok(true);
        }
        if tb.exceed_end_of_head() {
            return Ok(false);
        }
        Err(RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                format!("{}: expected end of head or trailing `:`", syntax_name),
                tb.line_file.clone(),
            ),
        )))
    }
}

fn parse_goal_error(syntax_name: &str, msg: &str, line_file: LineFile) -> RuntimeError {
    RuntimeError::from(ParseRuntimeError(
        RuntimeErrorStruct::new_with_msg_and_line_file(
            format!("{}: {}", syntax_name, msg),
            line_file,
        ),
    ))
}

fn require_question_goal(block: &TokenBlock, syntax_name: &str) -> Result<(), RuntimeError> {
    if block.current_token_is_equal_to(QUESTION_GOAL) {
        return Ok(());
    }
    Err(parse_goal_error(
        syntax_name,
        "expects a `? <fact>` goal block",
        block.line_file.clone(),
    ))
}
