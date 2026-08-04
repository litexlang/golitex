use crate::prelude::*;

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
