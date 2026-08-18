use crate::prelude::*;

impl Runtime {
    pub fn parse_fact(&mut self, tb: &mut TokenBlock) -> Result<Fact, RuntimeError> {
        self.ensure_execution_frame_for_parse();
        if tb.current()? == NOT
            && tb.token_at_add_index(1) == FORALL
            && Self::uses_inline_forall_syntax(tb)
        {
            tb.skip_token(NOT)?;
            let fact = self.parse_inline_forall_fact(tb, false)?;
            match fact {
                Fact::ForallFact(forall_fact) => Ok(NotForallFact::new(forall_fact).into()),
                _ => unreachable!("parse_inline_forall_fact only returns ForallFact"),
            }
        } else if tb.current()? == NOT && tb.token_at_add_index(1) == FORALL {
            tb.skip_token(NOT)?;
            let fact = self.parse_forall_or_forall_with_iff(tb)?;
            match fact {
                Fact::ForallFact(forall_fact) => Ok(NotForallFact::new(forall_fact).into()),
                Fact::ForallFactWithIff(_) => Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "not forall with <=> is not supported".to_string(),
                        tb.line_file.clone(),
                    ),
                ))),
                _ => unreachable!("parse_forall_or_forall_with_iff only returns forall facts"),
            }
        } else if tb.current()? == FORALL && Self::uses_inline_forall_syntax(tb) {
            self.parse_inline_forall_fact(tb, false)
        } else if tb.current()? == FORALL {
            self.parse_forall_or_forall_with_iff(tb)
        } else {
            let or_and_spec_fact = self.parse_exist_or_and_chain_atomic_fact(tb)?;
            Ok(or_and_spec_fact.to_fact())
        }
    }

    /// Parse a fact in a syntactic position that cannot own an indented body, such as an
    /// existential `st { ... }` body or a set-builder predicate.
    pub(crate) fn parse_inline_fact(
        &mut self,
        tb: &mut TokenBlock,
        nested: bool,
    ) -> Result<Fact, RuntimeError> {
        self.ensure_execution_frame_for_parse();
        if !nested && !tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "an inline fact cannot have an indented body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.current()? == NOT && tb.token_at_add_index(1) == FORALL {
            tb.skip_token(NOT)?;
            let fact = self.parse_inline_forall_fact(tb, nested)?;
            let Fact::ForallFact(forall_fact) = fact else {
                unreachable!("parse_inline_forall_fact only returns ForallFact")
            };
            Ok(NotForallFact::new(forall_fact).into())
        } else if tb.current()? == FORALL {
            self.parse_inline_forall_fact(tb, nested)
        } else {
            Ok(self.parse_exist_or_and_chain_atomic_fact(tb)?.to_fact())
        }
    }

    fn uses_inline_forall_syntax(tb: &TokenBlock) -> bool {
        tb.body.is_empty()
            && (tb.header.last().map(String::as_str) == Some(RIGHT_CURLY_BRACE)
                || tb.header.iter().any(|token| token == RIGHT_ARROW))
    }

    pub(crate) fn parse_inline_forall_fact(
        &mut self,
        tb: &mut TokenBlock,
        nested: bool,
    ) -> Result<Fact, RuntimeError> {
        if !nested && !tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "inline `{}` must fit on one line (no indented block)",
                        FORALL
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(FORALL)?;

            if tb.current_token_is_equal_to(LEFT_BRACKET) {
                let setting_prefix =
                    this.parse_fresh_setting_parameter_bundle(tb, ParamObjType::Forall)?;
                if !tb.current_token_is_equal_to(RIGHT_ARROW) {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "inline forall setting reference must be followed by `=>`".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                tb.skip_token(RIGHT_ARROW)?;
                let then_facts = this.parse_inline_forall_then(tb)?;
                if !nested && !tb.exceed_end_of_head() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!("unexpected token after inline `{}`", FORALL),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                return Ok(ForallFact::new(
                    setting_prefix.param_def,
                    setting_prefix.dom_facts,
                    then_facts,
                    tb.line_file.clone(),
                )?
                .into());
            }

            let mut groups: Vec<ParamGroupWithParamType> = vec![];
            loop {
                let cur = tb.current()?;
                if cur == COLON || cur == RIGHT_ARROW || cur == LEFT_CURLY_BRACE {
                    break;
                }
                groups.push(
                    this.parse_param_def_with_param_type_and_skip_comma(tb, ParamObjType::Forall)?,
                );
            }
            if groups.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "expected at least one parameter group after inline `{}`",
                            FORALL
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let param_def = ParamDefWithType::new(groups);
            let forall_param_names = param_def.collect_param_names();
            this.register_collected_param_names_for_def_parse(
                &forall_param_names,
                tb.line_file.clone(),
            )?;
            let has_colon = if tb.current()? == COLON {
                tb.skip_token(COLON)?;
                true
            } else if tb.current()? == RIGHT_ARROW {
                false
            } else {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "after binding variables in inline `{}`, expected `{}` or `{}`",
                            FORALL, COLON, RIGHT_ARROW
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            };

            let (dom_facts, then_facts) = this.parse_inline_forall_after_header(tb, has_colon)?;

            this.end_parsing_scope(ParamObjType::Forall, &forall_param_names);

            if !nested && !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("unexpected token after inline `{}`", FORALL),
                        tb.line_file.clone(),
                    ),
                )));
            }

            Ok(ForallFact::new(param_def, dom_facts, then_facts, tb.line_file.clone())?.into())
        })
    }

    fn parse_inline_forall_after_header(
        &mut self,
        tb: &mut TokenBlock,
        has_colon: bool,
    ) -> Result<(Vec<Fact>, Vec<Fact>), RuntimeError> {
        if tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "expected `{}` and one fact after inline `{}` header",
                        RIGHT_ARROW, FORALL
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        if !has_colon {
            if tb.current()? != RIGHT_ARROW {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "inline `{}` without a domain must use `{}` followed by one fact",
                            FORALL, RIGHT_ARROW
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.skip_token(RIGHT_ARROW)?;
            let then_facts = self.parse_inline_forall_then(tb)?;
            return Ok((vec![], then_facts));
        }

        if tb.current()? == RIGHT_ARROW || tb.current()? == LEFT_CURLY_BRACE {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "inline `{}` with `{}` must have exactly one domain fact before `{}`",
                        FORALL, COLON, RIGHT_ARROW
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }

        let dom_fact = self.parse_inline_forall_dom_segment(tb)?;
        if tb.exceed_end_of_head() || tb.current()? != RIGHT_ARROW {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "inline `{}` with a domain must use exactly one domain fact followed by `{}` and one consequent fact",
                        FORALL, RIGHT_ARROW
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(RIGHT_ARROW)?;
        let then_facts = self.parse_inline_forall_then(tb)?;
        Ok((vec![dom_fact], then_facts))
    }

    fn parse_inline_forall_dom_segment(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Fact, RuntimeError> {
        if tb.current()? == NOT && tb.token_at_add_index(1) == FORALL {
            Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "nested `not forall` is not allowed in an inline forall domain; use a block forall"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )))
        } else if tb.current()? == FORALL {
            Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "nested `forall` is not allowed in an inline forall domain; use a block forall"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )))
        } else {
            let e = self.parse_exist_or_and_chain_atomic_fact(tb)?;
            Ok(e.to_fact())
        }
    }

    fn parse_inline_forall_then(&mut self, tb: &mut TokenBlock) -> Result<Vec<Fact>, RuntimeError> {
        if tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("unexpected end of tokens in inline `{}` `then`", FORALL),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.current()? == LEFT_CURLY_BRACE {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "inline `forall` consequent must not use braces; write `=> <fact>`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(vec![self.parse_inline_fact(tb, true)?])
    }

    // fact_hierarchy 1
    fn parse_forall_or_forall_with_iff(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Fact, RuntimeError> {
        self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(FORALL)?;
            let (mut groups, setting_dom_facts) = if tb.current_token_is_equal_to(LEFT_BRACKET) {
                let setting_prefix =
                    this.parse_fresh_setting_parameter_bundle(tb, ParamObjType::Forall)?;
                if !tb.current_token_is_equal_to(COLON) {
                    tb.skip_token(COMMA).map_err(|_| {
                        RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                "expected `,` or `:` after forall setting reference".to_string(),
                                tb.line_file.clone(),
                            ),
                        ))
                    })?;
                }
                (setting_prefix.param_def.groups, setting_prefix.dom_facts)
            } else {
                (Vec::new(), Vec::new())
            };

            while tb.current()? != COLON {
                groups.push(
                    this.parse_param_def_with_param_type_and_skip_comma(tb, ParamObjType::Forall)?,
                );
            }
            let param_def = ParamDefWithType::new(groups);
            let forall_param_names = param_def.collect_param_names();
            this.register_collected_param_names_for_def_parse(
                &forall_param_names,
                tb.line_file.clone(),
            )?;
            tb.skip_token(COLON)?;

            let last_is_equiv = {
                let last_body = tb.body.last().ok_or_else(|| {
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "Expected body".to_string(),
                            tb.line_file.clone(),
                        ),
                    ))
                })?;
                last_body.current()? == EQUIVALENT_SIGN
            };
            if last_is_equiv {
                this.parse_forall_with_iff(tb, param_def, setting_dom_facts)
            } else {
                this.parse_forall(tb, param_def, setting_dom_facts)
            }
        })
    }

    fn parse_forall_with_iff(
        &mut self,
        tb: &mut TokenBlock,
        param_def: ParamDefWithType,
        mut dom_facts: Vec<Fact>,
    ) -> Result<Fact, RuntimeError> {
        if tb.body.len() < 2 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected at least 2 body blocks".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        let mut iff_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        let body_len = tb.body.len();

        let iff_block = tb.body.get_mut(body_len - 1).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected <=>: block in forall body".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        iff_block.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
        for block in iff_block.body.iter_mut() {
            iff_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        let then_block = tb.body.get_mut(body_len - 2).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected =>: block in forall body".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
        for block in then_block.body.iter_mut() {
            then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        for block in tb.body.iter_mut().take(body_len - 2) {
            dom_facts.push(self.parse_fact(block)?);
        }

        let forall_fact = ForallFact::new_canonical_forall(
            param_def,
            dom_facts,
            then_facts,
            tb.line_file.clone(),
        )?;

        Ok(ForallFactWithIff::new(forall_fact, iff_facts, tb.line_file.clone())?.into())
    }

    fn parse_forall(
        &mut self,
        tb: &mut TokenBlock,
        param_def: ParamDefWithType,
        mut initial_dom_facts: Vec<Fact>,
    ) -> Result<Fact, RuntimeError> {
        let last_body = tb.body.last().ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected body".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        if last_body.current()? == RIGHT_ARROW {
            let n = tb.body.len();
            for block in tb.body.iter_mut().take(n - 1) {
                initial_dom_facts.push(self.parse_fact(block)?);
            }
            let last = tb.body.last_mut().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "Expected body".to_string(),
                        tb.line_file.clone(),
                    ),
                ))
            })?;
            last.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            let mut then_facts: Vec<Fact> = Vec::new();
            for block in last.body.iter_mut() {
                then_facts.push(self.parse_fact(block)?);
            }
            Ok(ForallFact::new(
                param_def,
                initial_dom_facts,
                then_facts,
                tb.line_file.clone(),
            )?
            .into())
        } else {
            let mut then_facts: Vec<Fact> = Vec::new();
            for block in tb.body.iter_mut() {
                then_facts.push(self.parse_fact(block)?);
            }
            Ok(ForallFact::new(
                param_def,
                initial_dom_facts,
                then_facts,
                tb.line_file.clone(),
            )?
            .into())
        }
    }

    // Hierarchy 3: parse `and` chains.
    pub fn parse_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AndChainAtomicFact, RuntimeError> {
        let first = self.parse_chain_atomic(tb, true)?;

        // Chain facts already encode their own comparison sequence.
        match first {
            ChainAtomicFact::ChainFact(c) => return Ok(AndChainAtomicFact::ChainFact(c)),
            ChainAtomicFact::AtomicFact(a) => {
                let mut collected: Vec<AtomicFact> = vec![a];
                while !tb.exceed_end_of_head() && tb.current()? == AND {
                    tb.skip_token(AND)?;
                    let next = self.parse_atomic_fact(tb, true)?;
                    collected.push(next);
                }
                if collected.len() == 1 {
                    return Ok(AndChainAtomicFact::AtomicFact(collected.remove(0)));
                }
                Ok(AndChainAtomicFact::AndFact(AndFact::new(
                    collected,
                    tb.line_file.clone(),
                )))
            }
        }
    }

    pub fn parse_exist_fact(&mut self, tb: &mut TokenBlock) -> Result<ExistFactEnum, RuntimeError> {
        self.run_in_local_parsing_time_name_scope(|this| {
            let is_exist_unique = if tb.current()? == EXIST {
                tb.skip_token(EXIST)?;
                if tb.current()? == "!" {
                    tb.skip_token("!")?;
                    true
                } else {
                    false
                }
            } else {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "expected `{}` or `{}` at start of exist fact",
                            EXIST, EXIST_BANG
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            };
            let mut groups: Vec<ParamGroupWithParamType> = vec![];
            while tb.current()? != ST {
                groups.push(
                    this.parse_param_def_with_param_type_and_skip_comma(tb, ParamObjType::Exist)?,
                );
            }
            let param_def = ParamDefWithType::new(groups);
            let exist_param_names = param_def.collect_param_names();
            this.run_in_local_parsing_time_name_scope(move |inner| {
                inner.register_collected_param_names_for_def_parse(
                    &exist_param_names,
                    tb.line_file.clone(),
                )?;
                let fact_result = (|| {
                    tb.skip_token(ST)?;

                    tb.skip_token(LEFT_CURLY_BRACE)?;

                    let mut facts: Vec<QuantifierFreeFact> = vec![];
                    loop {
                        facts.push(inner.parse_inline_quantifier_free_fact(tb)?);
                        if tb.current()? != RIGHT_CURLY_BRACE {
                            tb.skip_token(COMMA)?;
                        } else {
                            break;
                        }
                    }
                    tb.skip_token(RIGHT_CURLY_BRACE)?;

                    let line_file = tb.line_file.clone();
                    let body = ExistentialSpec::new(param_def, facts, line_file)?;
                    Ok(if is_exist_unique {
                        ExistFactEnum::ExistUniqueFact(body)
                    } else {
                        ExistFactEnum::ExistFact(body)
                    })
                })();
                inner.end_parsing_scope(ParamObjType::Exist, &exist_param_names);
                fact_result
            })
        })
    }

    pub(crate) fn parse_inline_quantifier_free_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<QuantifierFreeFact, RuntimeError> {
        let fact = self.parse_inline_fact(tb, true)?;
        self.parsed_fact_to_quantifier_free_fact(fact, tb)
    }

    fn parsed_fact_to_quantifier_free_fact(
        &self,
        fact: Fact,
        tb: &TokenBlock,
    ) -> Result<QuantifierFreeFact, RuntimeError> {
        match fact {
            Fact::AtomicFact(fact) => Ok(QuantifierFreeFact::AtomicFact(fact)),
            Fact::AndFact(fact) => Ok(QuantifierFreeFact::AndFact(fact)),
            Fact::ChainFact(fact) => Ok(QuantifierFreeFact::ChainFact(fact)),
            Fact::OrFact(fact) => Ok(QuantifierFreeFact::OrFact(fact)),
            Fact::ForallFact(_) => Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "inline `forall` is not allowed in existential or set-builder bodies; define a named `prop` and use `$P(...)`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            ))),
            Fact::ExistFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {
                Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "this fact form is not supported in an existential-style property body"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )))
            }
        }
    }

    pub fn parse_quantifier_free_facts_in_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<QuantifierFreeFact>, RuntimeError> {
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "`have ...:` expects at least one indented fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let mut facts: Vec<QuantifierFreeFact> = vec![];
        for block in tb.body.iter_mut() {
            let fact = self.parse_fact(block)?;
            facts.push(self.parsed_fact_to_quantifier_free_fact(fact, block)?);
        }
        Ok(facts)
    }

    pub fn parse_facts_in_body(&mut self, tb: &mut TokenBlock) -> Result<Vec<Fact>, RuntimeError> {
        let mut facts: Vec<Fact> = vec![];
        for block in tb.body.iter_mut() {
            facts.push(self.parse_fact(block)?);
        }
        Ok(facts)
    }

    pub fn parse_exist_or_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ExistOrAndChainAtomicFact, RuntimeError> {
        match tb.current()? {
            EXIST => {
                let exist_fact = self.parse_exist_fact(tb)?;
                Ok(ExistOrAndChainAtomicFact::ExistFact(exist_fact))
            }
            NOT => {
                if tb.token_at_add_index(1) == EXIST {
                    if tb.token_at_add_index(2) == "!" {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                format!("`{} {}` is not supported", NOT, EXIST_BANG),
                                tb.line_file.clone(),
                            ),
                        )));
                    }
                    tb.skip_token(NOT)?;
                    let exist_fact = self.parse_exist_fact(tb)?;
                    return Ok(ExistOrAndChainAtomicFact::ExistFact(match exist_fact {
                        ExistFactEnum::ExistFact(body) => ExistFactEnum::NotExistFact(body),
                        ExistFactEnum::ExistUniqueFact(_) | ExistFactEnum::NotExistFact(_) => {
                            unreachable!("`not exist` parse should only produce plain exist body")
                        }
                    }));
                }
                let first = self.parse_and_chain_atomic_fact_allow_leading_not(tb)?;
                let mut list: Vec<AndChainAtomicFact> = vec![first];
                while !tb.exceed_end_of_head() && tb.current()? == OR {
                    tb.skip_token(OR)?;
                    list.push(self.parse_and_chain_atomic_fact_allow_leading_not(tb)?);
                }
                if list.len() == 1 {
                    return Ok(match list.remove(0) {
                        AndChainAtomicFact::AtomicFact(a) => {
                            ExistOrAndChainAtomicFact::AtomicFact(a)
                        }
                        AndChainAtomicFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
                        AndChainAtomicFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
                    });
                }
                Ok(ExistOrAndChainAtomicFact::OrFact(OrFact::new(
                    list,
                    tb.line_file.clone(),
                )))
            }
            FORALL => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "Expected exist or and chain atomic fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            _ => Ok(self.parse_quantifier_free_fact(tb)?.into()),
        }
    }

    /// Parse a single atomic fact only: $prop(args) or obj op obj. Does not parse chain (obj op obj op obj).
    pub fn parse_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
        is_true: bool,
    ) -> Result<AtomicFact, RuntimeError> {
        if tb.current()? == NOT {
            tb.skip_token(NOT)?;
            return Ok(self.parse_atomic_fact(tb, !is_true)?);
        }

        let line_file = tb.line_file.clone();
        if tb.current()? == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            let prop = self.parse_predicate(tb)?;
            let args = self.parse_braced_objs(tb)?;
            let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
                |e: RuntimeError| {
                    let msg = match &e {
                        RuntimeError::NewFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                    ))
                },
            )?;
            return Ok(atomic);
        }
        let first_obj = self.parse_obj(tb)?;
        if tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected operator or $prop in atomic fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let tok = tb.current()?.to_string();
        let (prop, atomic_is_true) = if tok == UNICODE_NOT_IN {
            tb.advance()?;
            (AtomicName::WithoutMod(IN.to_string()), !is_true)
        } else if is_comparison_str(&tok) {
            tb.advance()?;
            (AtomicName::WithoutMod(tok.clone()), is_true)
        } else if tok == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            (self.parse_predicate(tb)?, is_true)
        } else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected operator or $prop in atomic fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        };
        let next_obj = self.parse_obj(tb)?;
        let args = vec![first_obj, next_obj];
        let atomic = AtomicFact::to_atomic_fact(prop, atomic_is_true, args, line_file).map_err(
            |e: RuntimeError| {
                let msg = match &e {
                    RuntimeError::NewFactError(s) => s.msg.clone(),
                    _ => "parse atomic fact".to_string(),
                };
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                ))
            },
        )?;
        Ok(atomic)
    }

    /// Normal and/chain atomic fact, or a single leading `not` on an atomic.
    ///
    /// [`Self::parse_and_chain_atomic_fact`] alone is wrong for `not $p()`: it uses
    /// [`Self::parse_chain_atomic`], which treats `$p()` as an infix `$` between objs and parses
    /// `()` as grouping (empty-`()` / EOT issues). Used for `or`-disjuncts and `case not ...`.
    pub fn parse_and_chain_atomic_fact_allow_leading_not(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AndChainAtomicFact, RuntimeError> {
        if tb.current()? == NOT {
            tb.skip_token(NOT)?;
            let a = self.parse_atomic_fact(tb, false)?;
            return Ok(AndChainAtomicFact::AtomicFact(a));
        }
        self.parse_and_chain_atomic_fact(tb)
    }

    pub fn parse_quantifier_free_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<QuantifierFreeFact, RuntimeError> {
        let first = self.parse_and_chain_atomic_fact_allow_leading_not(tb)?;
        let mut list: Vec<AndChainAtomicFact> = vec![first];
        while !tb.exceed_end_of_head() && tb.current()? == OR {
            tb.skip_token(OR)?;
            list.push(self.parse_and_chain_atomic_fact_allow_leading_not(tb)?);
        }
        if list.len() == 1 {
            return Ok(match list.remove(0) {
                AndChainAtomicFact::AtomicFact(a) => QuantifierFreeFact::AtomicFact(a),
                AndChainAtomicFact::AndFact(a) => QuantifierFreeFact::AndFact(a),
                AndChainAtomicFact::ChainFact(c) => QuantifierFreeFact::ChainFact(c),
            });
        }
        Ok(QuantifierFreeFact::OrFact(OrFact::new(
            list,
            tb.line_file.clone(),
        )))
    }

    /// Parse chain (obj op obj op ...) or single atomic ($prop(args) or obj op obj). When is_true is false, only single atomic is allowed (negated).
    pub fn parse_chain_atomic(
        &mut self,
        tb: &mut TokenBlock,
        is_true: bool,
    ) -> Result<ChainAtomicFact, RuntimeError> {
        let line_file = tb.line_file.clone();
        if tb.current()? == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            let prop = self.parse_predicate(tb)?;
            let args = self.parse_braced_objs(tb)?;
            let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
                |e: RuntimeError| {
                    let msg = match &e {
                        RuntimeError::NewFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                    ))
                },
            )?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }
        let first_obj = self.parse_obj(tb)?;
        let mut objs: Vec<Obj> = vec![first_obj];
        let mut prop_names: Vec<AtomicName> = vec![];
        while !tb.exceed_end_of_head() {
            let tok = tb.current()?.to_string();
            if tok == UNICODE_NOT_IN {
                if !prop_names.is_empty() {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "negated membership cannot be part of a fact chain".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                tb.advance()?;
                let next_obj = self.parse_obj(tb)?;
                if !tb.exceed_end_of_head()
                    && (is_comparison_str(tb.current()?)
                        || tb.current_token_is_equal_to(FACT_PREFIX)
                        || tb.current_token_is_equal_to(UNICODE_NOT_IN))
                {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "negated membership cannot be part of a fact chain".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                let atomic = AtomicFact::to_atomic_fact(
                    AtomicName::WithoutMod(IN.to_string()),
                    !is_true,
                    vec![objs.remove(0), next_obj],
                    line_file,
                )
                .map_err(|e: RuntimeError| {
                    let msg = match &e {
                        RuntimeError::NewFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                    ))
                })?;
                return Ok(ChainAtomicFact::AtomicFact(atomic));
            }
            let prop = if is_comparison_str(&tok) {
                tb.advance()?;
                AtomicName::WithoutMod(tok.clone())
            } else if tok == FACT_PREFIX {
                tb.skip_token(FACT_PREFIX)?;
                self.parse_predicate(tb)?
            } else {
                break;
            };
            let next_obj = self.parse_obj(tb)?;
            prop_names.push(prop);
            objs.push(next_obj);
        }
        if prop_names.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected operator or $prop in fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if !is_true && (objs.len() > 2 || prop_names.len() > 1) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Negated fact must be single atomic (one operator)".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if objs.len() == 2 && prop_names.len() == 1 {
            let prop = prop_names.remove(0);
            let args = objs;
            let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
                |e: RuntimeError| {
                    let msg = match &e {
                        RuntimeError::NewFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                    ))
                },
            )?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }
        Ok(ChainAtomicFact::ChainFact(ChainFact::new(
            objs, prop_names, line_file,
        )))
    }
}

#[cfg(test)]
mod inline_forall_parse_tests {
    use crate::parse::Tokenizer;
    use crate::prelude::*;
    use std::rc::Rc;

    fn parse_one_fact_line(line: &str) -> Result<Fact, RuntimeError> {
        let mut rt = Runtime::new();
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer.parse_blocks(line, Rc::from("test.lit"))?;
        assert_eq!(blocks.len(), 1, "{line:?}");
        rt.parse_fact(&mut blocks[0])
    }

    fn parse_error_msg(line: &str) -> String {
        let err = parse_one_fact_line(line).unwrap_err();
        let RuntimeError::ParseError(s) = err else {
            panic!("expected parse error, got {err:?}");
        };
        s.msg
    }

    #[test]
    fn inline_forall_no_colon_before_arrow_when_no_dom() {
        let f = parse_one_fact_line("forall x R => x > 0").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert!(ff.dom_facts.is_empty());
        assert_eq!(ff.then_facts.len(), 1);
    }

    #[test]
    fn inline_forall_dom_arrow_then() {
        let f = parse_one_fact_line("forall x R: x > 0 => x >= 0").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert_eq!(ff.dom_facts.len(), 1);
        assert_eq!(ff.then_facts.len(), 1);
    }

    #[test]
    fn inline_forall_rejects_single_then_without_arrow() {
        let msg = parse_error_msg("forall x R: x > 0");
        assert!(msg.contains("Expected body"), "{}", msg);
    }

    #[test]
    fn inline_forall_rejects_no_colon_braced_then_when_no_dom() {
        let msg = parse_error_msg("forall x R { x > 0, x + 1 > 1 }");
        assert!(msg.contains("expected `:` or `=>`"), "{}", msg);
    }

    #[test]
    fn inline_forall_rejects_empty_dom_arrow() {
        let msg = parse_error_msg("forall x R: => x > 0");
        assert!(msg.contains("exactly one domain fact"), "{}", msg);
    }

    #[test]
    fn inline_forall_rejects_nested_in_dom() {
        let msg = parse_error_msg("forall x R: forall y R => y > 0 => x > 0");
        assert!(msg.contains("nested `forall`"), "{}", msg);
    }

    #[test]
    fn inline_forall_rejects_multiple_domain_facts() {
        let msg = parse_error_msg("forall x R: x > 0, x < 1 => x >= 0");
        assert!(msg.contains("exactly one domain fact"), "{}", msg);
    }

    #[test]
    fn inline_forall_rejects_braced_then() {
        let msg = parse_error_msg("forall x R: x > 0 => {x >= 0}");
        assert!(msg.contains("must not use braces"), "{}", msg);
    }

    #[test]
    fn inline_forall_rejects_multiple_then_facts() {
        let msg = parse_error_msg("forall x R: x > 0 => x >= 0, x + 1 > 0");
        assert!(msg.contains("unexpected token"), "{}", msg);
    }

    #[test]
    fn not_inline_forall_parses_as_not_forall() {
        let f = parse_one_fact_line("not forall x R: x > 0 => x + 1 > 1").unwrap();
        assert!(matches!(f, Fact::NotForall(_)));
    }

    #[test]
    fn unicode_and_ascii_facts_share_one_canonical_representation() {
        let cases = [
            ("forall x R => x != pi", "∀ x ℝ → x ≠ π"),
            ("exist x N st {x $in {}}", "∃ x ℕ st {x ∈ ∅}"),
            ("exist! x N st {x = 0}", "∃! x ℕ st {x = 0}"),
            ("0 <= 1 and 1 >= 0", "0 ≤ 1 ∧ 1 ≥ 0"),
            ("not 0 = 1 or 1 $in Z", "¬ 0 = 1 ∨ 1 ∈ ℤ"),
            ("N $subset Z", "ℕ ⊆ ℤ"),
            ("Z $superset N", "ℤ ⊇ ℕ"),
            ("{0} $proper_subset {0, 1}", "{0} ⊊ {0, 1}"),
            ("{0} $proper_subset {0, 1}", "{0} ⊂ {0, 1}"),
            ("{0, 1} $proper_superset {0}", "{0, 1} ⊋ {0}"),
            ("not x $in union(intersect(A, B), C)", "x ∉ A ∩ B ∪ C"),
            ("cart(A, B, C) = cart(A, B, C)", "A × B × C = cart(A, B, C)"),
            ("1 $in N+", "1 ∈ ℕ+"),
            ("1 $in Z+", "1 ∈ ℤ+"),
            ("1 $in Q+", "1 ∈ ℚ+"),
            ("1 $in R+", "1 ∈ ℝ+"),
            ("-1 $in Z-", "-1 ∈ ℤ-"),
            ("-1 $in Q-", "-1 ∈ ℚ-"),
            ("-1 $in R-", "-1 ∈ ℝ-"),
            ("1 $in Z*", "1 ∈ ℤ*"),
            ("1 $in Q*", "1 ∈ ℚ*"),
            ("1 $in R*", "1 ∈ ℝ*"),
            ("1 $in C*", "1 ∈ ℂ*"),
        ];

        for (ascii, unicode) in cases {
            let ascii_fact = parse_one_fact_line(ascii).unwrap();
            let unicode_fact = parse_one_fact_line(unicode).unwrap();
            assert_eq!(
                ascii_fact.to_string(),
                unicode_fact.to_string(),
                "{unicode}"
            );
        }

        assert!(
            parse_one_fact_line("1 ∈ ℕ*").is_err(),
            "ℕ* must remain unsupported because N* is not a standard set"
        );
    }

    #[test]
    fn unicode_not_in_is_a_negated_membership_operator() {
        assert_eq!(
            parse_one_fact_line("x ∉ A").unwrap().to_string(),
            "not x $in A"
        );
        assert_eq!(
            parse_one_fact_line("not x ∉ A").unwrap().to_string(),
            "x $in A"
        );

        let msg = parse_error_msg("x ∉ A $subset B");
        assert!(msg.contains("cannot be part of a fact chain"), "{msg}");
    }

    #[test]
    fn inline_forall_then_flattens_inline_forall() {
        let fact =
            parse_one_fact_line("forall x R: x > 0 => forall y R: y > 0 => x + y > 0").unwrap();
        let Fact::ForallFact(forall_fact) = fact else {
            panic!("expected a flattened forall fact");
        };
        assert_eq!(forall_fact.params_def_with_type.number_of_params(), 2);
        assert_eq!(forall_fact.dom_facts.len(), 2);
        assert_eq!(forall_fact.then_facts.len(), 1);
    }

    #[test]
    fn existential_body_rejects_inline_forall() {
        let msg = parse_error_msg("exist x R st {forall y R => y = y}");
        assert!(
            msg.contains("inline `forall` is not allowed in existential or set-builder bodies"),
            "{}",
            msg
        );
    }

    #[test]
    fn set_builder_body_rejects_inline_forall() {
        let msg = parse_error_msg("{x R: forall y R => y = y} = {x R: x = x}");
        assert!(
            msg.contains("inline `forall` is not allowed in existential or set-builder bodies"),
            "{}",
            msg
        );
    }

    #[test]
    fn nested_forall_flattening_recomputes_dependent_parameter_indices() {
        let fact =
            parse_one_fact_line("forall S nonempty_set => forall x S => forall y S => x = y")
                .unwrap();
        let Fact::ForallFact(forall_fact) = fact else {
            panic!("expected a recursively flattened forall fact");
        };
        assert_eq!(forall_fact.params_def_with_type.number_of_params(), 3);
        assert_eq!(
            forall_fact
                .params_def_with_type
                .cited_param_indices_for_group(0),
            []
        );
        assert_eq!(
            forall_fact
                .params_def_with_type
                .cited_param_indices_for_group(1),
            [0]
        );
        assert_eq!(
            forall_fact
                .params_def_with_type
                .cited_param_indices_for_group(2),
            [0]
        );
    }

    #[test]
    fn forall_then_rejects_nested_forall_with_sibling_fact() {
        let msg = parse_error_msg(
            "forall x R:\n    x > 0\n    =>:\n        x = x\n        forall y R:\n            y = y",
        );
        assert!(msg.contains("only direct fact"), "{}", msg);
    }
}
