use crate::prelude::*;

impl Runtime {
    pub fn parse_fact(&mut self, tb: &mut TokenBlock) -> Result<Fact, RuntimeError> {
        if tb.current()? == NOT
            && tb.token_at_add_index(1) == FORALL
            && tb.token_at_add_index(2) == "!"
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
        } else if tb.current()? == FORALL && tb.token_at_add_index(1) == "!" {
            self.parse_inline_forall_fact(tb, false)
        } else if tb.current()? == FORALL {
            self.parse_forall_or_forall_with_iff(tb)
        } else {
            let or_and_spec_fact = self.parse_exist_or_and_chain_atomic_fact(tb)?;
            Ok(or_and_spec_fact.to_fact())
        }
    }

    pub(crate) fn parse_inline_forall_fact(
        &mut self,
        tb: &mut TokenBlock,
        nested: bool,
    ) -> Result<Fact, RuntimeError> {
        if !tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "inline `{}` must fit on one line (no indented block); use `{}` for block syntax",
                        FORALL_BANG, FORALL
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(FORALL)?;
            if tb.current()? != "!" {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "expected `!` after `{}` for inline quantifier (`{}`)",
                            FORALL, FORALL_BANG
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.skip_token("!")?;
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
                            "expected at least one parameter group after `{}`",
                            FORALL_BANG
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
            if tb.current()? == COLON {
                tb.skip_token(COLON)?;
            } else if tb.current()? != RIGHT_ARROW && tb.current()? != LEFT_CURLY_BRACE {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "after binding variables in `{}`, expected `{}`, `{}`, or `{}`",
                            FORALL_BANG, COLON, RIGHT_ARROW, LEFT_CURLY_BRACE
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            }

            let (dom_facts, then_facts) = this.parse_inline_forall_after_colon(tb)?;

            this.parsing_free_param_collection
                .end_scope(ParamObjType::Forall, &forall_param_names);

            if !nested && !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("unexpected token after `{}`", FORALL_BANG),
                        tb.line_file.clone(),
                    ),
                )));
            }

            Ok(ForallFact::new(param_def, dom_facts, then_facts, tb.line_file.clone())?.into())
        })
    }

    fn parse_inline_forall_after_colon(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<(Vec<Fact>, Vec<ExistOrAndChainAtomicFact>), RuntimeError> {
        if tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "expected `{}`, `{{`, or body after `{}` header",
                        RIGHT_ARROW, FORALL_BANG
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.current()? == RIGHT_ARROW {
            tb.skip_token(RIGHT_ARROW)?;
            let then_facts = self.parse_inline_forall_then(tb)?;
            return Ok((vec![], then_facts));
        }
        if tb.current()? == LEFT_CURLY_BRACE {
            let then_facts = self.parse_inline_forall_braced_then_list(tb)?;
            return Ok((vec![], then_facts));
        }

        let mut dom_facts: Vec<Fact> = Vec::new();
        loop {
            let seg = self.parse_inline_forall_dom_segment(tb)?;
            if tb.exceed_end_of_head() {
                if dom_facts.is_empty() {
                    let then0 = Self::fact_as_exist_or_then(seg, tb.line_file.clone())?;
                    return Ok((vec![], vec![then0]));
                }
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "expected `{}` after `{}` domain facts",
                            RIGHT_ARROW, FORALL_BANG
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            }
            match tb.current()? {
                COMMA => {
                    dom_facts.push(seg);
                    tb.skip_token(COMMA)?;
                }
                RIGHT_ARROW => {
                    dom_facts.push(seg);
                    tb.skip_token(RIGHT_ARROW)?;
                    let then_facts = self.parse_inline_forall_then(tb)?;
                    return Ok((dom_facts, then_facts));
                }
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                                "expected `,`, `{}`, or end of line after `{}` domain fact",
                                RIGHT_ARROW, FORALL_BANG
                            ),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            }
        }
    }

    fn parse_inline_forall_dom_segment(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Fact, RuntimeError> {
        if tb.current()? == NOT
            && tb.token_at_add_index(1) == FORALL
            && tb.token_at_add_index(2) == "!"
        {
            tb.skip_token(NOT)?;
            let fact = self.parse_inline_forall_fact(tb, true)?;
            match fact {
                Fact::ForallFact(ff) => Ok(NotForallFact::new(ff).into()),
                _ => unreachable!("parse_inline_forall_fact only returns ForallFact"),
            }
        } else if tb.current()? == FORALL && tb.token_at_add_index(1) == "!" {
            self.parse_inline_forall_fact(tb, true)
        } else if tb.current()? == NOT && tb.token_at_add_index(1) == FORALL {
            Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "`not {}` in `{}` domain is not supported (requires a block); use `not {}` or a separate line",
                        FORALL, FORALL_BANG, FORALL_BANG
                    ),
                    tb.line_file.clone(),
                ),
            )))
        } else if tb.current()? == FORALL {
            Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "block `{}` is not allowed inside `{}` domain; use `{}` or move to a multi-line `{}` block",
                        FORALL, FORALL_BANG, FORALL_BANG, FORALL
                    ),
                    tb.line_file.clone(),
                ),
            )))
        } else {
            let e = self.parse_exist_or_and_chain_atomic_fact(tb)?;
            Ok(e.to_fact())
        }
    }

    fn parse_inline_forall_then(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<ExistOrAndChainAtomicFact>, RuntimeError> {
        Self::reject_inline_forall_in_then(tb)?;
        if tb.current()? == LEFT_CURLY_BRACE {
            return self.parse_inline_forall_braced_then_list(tb);
        }
        Ok(vec![self.parse_exist_or_and_chain_atomic_fact(tb)?])
    }

    fn parse_inline_forall_braced_then_list(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<ExistOrAndChainAtomicFact>, RuntimeError> {
        tb.skip_token(LEFT_CURLY_BRACE)?;
        let mut facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        loop {
            Self::reject_inline_forall_in_then(tb)?;
            facts.push(self.parse_exist_or_and_chain_atomic_fact(tb)?);
            if tb.current()? != RIGHT_CURLY_BRACE {
                tb.skip_token(COMMA)?;
            } else {
                break;
            }
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;
        Ok(facts)
    }

    fn reject_inline_forall_in_then(tb: &TokenBlock) -> Result<(), RuntimeError> {
        if tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("unexpected end of tokens in `{}` `then`", FORALL_BANG),
                    tb.line_file.clone(),
                ),
            )));
        }
        if (tb.current()? == FORALL && tb.token_at_add_index(1) == "!")
            || (tb.current()? == NOT
                && tb.token_at_add_index(1) == FORALL
                && tb.token_at_add_index(2) == "!")
        {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "`{}` is not allowed in the `then` part of another `{}`",
                        FORALL_BANG, FORALL_BANG
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(())
    }

    fn fact_as_exist_or_then(
        f: Fact,
        line_file: LineFile,
    ) -> Result<ExistOrAndChainAtomicFact, RuntimeError> {
        match f {
            Fact::AtomicFact(a) => Ok(ExistOrAndChainAtomicFact::AtomicFact(a)),
            Fact::ExistFact(e) => Ok(ExistOrAndChainAtomicFact::ExistFact(e)),
            Fact::OrFact(o) => Ok(ExistOrAndChainAtomicFact::OrFact(o)),
            Fact::AndFact(a) => Ok(ExistOrAndChainAtomicFact::AndFact(a)),
            Fact::ChainFact(c) => Ok(ExistOrAndChainAtomicFact::ChainFact(c)),
            Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {
                Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "`{}` without `{}` must end with one chain/atomic-style fact",
                            FORALL_BANG, RIGHT_ARROW
                        ),
                        line_file,
                    ),
                )))
            }
        }
    }

    // fact_hierarchy 1
    fn parse_forall_or_forall_with_iff(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Fact, RuntimeError> {
        self.run_in_local_parsing_time_name_scope(|this| {
            tb.skip_token(FORALL)?;
            let mut groups: Vec<ParamGroupWithParamType> = vec![];
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
            let fact_result = if last_is_equiv {
                this.parse_forall_with_iff(tb, param_def)
            } else {
                this.parse_forall(tb, param_def)
            };
            this.parsing_free_param_collection
                .end_scope(ParamObjType::Forall, &forall_param_names);
            fact_result
        })
    }

    fn parse_forall_with_iff(
        &mut self,
        tb: &mut TokenBlock,
        param_def: ParamDefWithType,
    ) -> Result<Fact, RuntimeError> {
        if tb.body.len() < 2 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected at least 2 body blocks".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let mut dom_facts: Vec<Fact> = Vec::new();
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

        let forall_fact = ForallFact::new(param_def, dom_facts, then_facts, tb.line_file.clone())?;

        Ok(ForallFactWithIff::new(forall_fact, iff_facts, tb.line_file.clone())?.into())
    }

    fn parse_forall(
        &mut self,
        tb: &mut TokenBlock,
        param_def: ParamDefWithType,
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
            let mut dom_facts: Vec<Fact> = vec![];
            let n = tb.body.len();
            for block in tb.body.iter_mut().take(n - 1) {
                dom_facts.push(self.parse_fact(block)?);
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
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in last.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
            }
            Ok(ForallFact::new(param_def, dom_facts, then_facts, tb.line_file.clone())?.into())
        } else {
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in tb.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
            }
            Ok(ForallFact::new(param_def, vec![], then_facts, tb.line_file.clone())?.into())
        }
    }

    // hierarchy 3: and 并列
    pub fn parse_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AndChainAtomicFact, RuntimeError> {
        let first = self.parse_chain_atomic(tb, true)?;

        // 如果是chain，那直接返回
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

                    let mut facts: Vec<ExistBodyFact> = vec![];
                    loop {
                        facts.push(inner.parse_exist_body_fact(tb)?);
                        if tb.current()? != RIGHT_CURLY_BRACE {
                            tb.skip_token(COMMA)?;
                        } else {
                            break;
                        }
                    }
                    tb.skip_token(RIGHT_CURLY_BRACE)?;

                    let line_file = tb.line_file.clone();
                    let body = ExistFactBody::new(param_def, facts, line_file)?;
                    Ok(if is_exist_unique {
                        ExistFactEnum::ExistUniqueFact(body)
                    } else {
                        ExistFactEnum::ExistFact(body)
                    })
                })();
                inner
                    .parsing_free_param_collection
                    .end_scope(ParamObjType::Exist, &exist_param_names);
                fact_result
            })
        })
    }

    fn parse_exist_body_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ExistBodyFact, RuntimeError> {
        if tb.current()? == FORALL && tb.token_at_add_index(1) == "!" {
            let fact = self.parse_inline_forall_fact(tb, true)?;
            match fact {
                Fact::ForallFact(forall_fact) => Ok(ExistBodyFact::InlineForall(forall_fact)),
                _ => unreachable!("parse_inline_forall_fact only returns ForallFact"),
            }
        } else {
            Ok(self.parse_or_and_chain_atomic_fact(tb)?.into())
        }
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
            _ => Ok(self.parse_or_and_chain_atomic_fact(tb)?.into()),
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
        let prop = if is_comparison_str(&tok) {
            tb.advance()?;
            AtomicName::WithoutMod(tok.clone())
        } else if tok == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            self.parse_predicate(tb)?
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

    pub fn parse_or_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<OrAndChainAtomicFact, RuntimeError> {
        let first = self.parse_and_chain_atomic_fact_allow_leading_not(tb)?;
        let mut list: Vec<AndChainAtomicFact> = vec![first];
        while !tb.exceed_end_of_head() && tb.current()? == OR {
            tb.skip_token(OR)?;
            list.push(self.parse_and_chain_atomic_fact_allow_leading_not(tb)?);
        }
        if list.len() == 1 {
            return Ok(match list.remove(0) {
                AndChainAtomicFact::AtomicFact(a) => OrAndChainAtomicFact::AtomicFact(a),
                AndChainAtomicFact::AndFact(a) => OrAndChainAtomicFact::AndFact(a),
                AndChainAtomicFact::ChainFact(c) => OrAndChainAtomicFact::ChainFact(c),
            });
        }
        Ok(OrAndChainAtomicFact::OrFact(OrFact::new(
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
    use crate::parse::TokenBlock;
    use crate::prelude::*;
    use std::rc::Rc;

    fn parse_one_fact_line(line: &str) -> Result<Fact, RuntimeError> {
        let mut rt = Runtime::new();
        let mut blocks = TokenBlock::parse_blocks(line, Rc::from("test.lit"))?;
        assert_eq!(blocks.len(), 1, "{line:?}");
        rt.parse_fact(&mut blocks[0])
    }

    #[test]
    fn inline_forall_single_then_without_arrow() {
        let f = parse_one_fact_line("forall! x R: x > 0").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert!(ff.dom_facts.is_empty());
        assert_eq!(ff.then_facts.len(), 1);
    }

    #[test]
    fn inline_forall_no_colon_before_arrow_when_no_dom() {
        let f = parse_one_fact_line("forall! x R => { x > 0 }").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert!(ff.dom_facts.is_empty());
        assert_eq!(ff.then_facts.len(), 1);
    }

    #[test]
    fn inline_forall_no_colon_braced_then_when_no_dom() {
        let f = parse_one_fact_line("forall! x R { x > 0, x + 1 > 1 }").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert!(ff.dom_facts.is_empty());
        assert_eq!(ff.then_facts.len(), 2);
    }

    #[test]
    fn inline_forall_dom_arrow_then() {
        let f = parse_one_fact_line("forall! x R: x > 0 => { x >= 0 }").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert_eq!(ff.dom_facts.len(), 1);
        assert_eq!(ff.then_facts.len(), 1);
    }

    #[test]
    fn inline_forall_empty_dom_arrow() {
        let f = parse_one_fact_line("forall! x R: => { x > 0 }").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert!(ff.dom_facts.is_empty());
        assert_eq!(ff.then_facts.len(), 1);
    }

    #[test]
    fn inline_forall_nested_in_dom() {
        let f = parse_one_fact_line("forall! x R: forall! y R: y > 0 => { x > y } => { x > 0 }")
            .unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert_eq!(ff.dom_facts.len(), 1);
        assert!(matches!(&ff.dom_facts[0], Fact::ForallFact(_)));
        assert_eq!(ff.then_facts.len(), 1);
    }

    #[test]
    fn inline_forall_braced_then() {
        let f = parse_one_fact_line("forall! x R: x > 0 => { x >= 0, x + 1 > 0 }").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert_eq!(ff.dom_facts.len(), 1);
        assert_eq!(ff.then_facts.len(), 2);
    }

    #[test]
    fn inline_forall_no_dom_braced_then() {
        let f = parse_one_fact_line("forall! x R: { x > 0, x + 1 > 1 }").unwrap();
        let Fact::ForallFact(ff) = f else {
            panic!("expected ForallFact");
        };
        assert!(ff.dom_facts.is_empty());
        assert_eq!(ff.then_facts.len(), 2);
    }

    #[test]
    fn not_inline_forall_parses_as_not_forall() {
        let f = parse_one_fact_line("not forall! x R: x > 0 => { x + 1 > 1 }").unwrap();
        assert!(matches!(f, Fact::NotForall(_)));
    }

    #[test]
    fn inline_forall_then_may_not_contain_inline_forall() {
        let err = parse_one_fact_line("forall! x R: x > 0 => { forall! y R: y > 0 => { y > x } }")
            .unwrap_err();
        let RuntimeError::ParseError(s) = err else {
            panic!("expected parse error, got {err:?}");
        };
        assert!(s.msg.contains("then"), "{}", s.msg);
    }
}
