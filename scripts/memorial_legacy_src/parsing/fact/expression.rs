//! Fact-expression parsing, including quantified and composite facts.

use crate::prelude::*;

impl Runtime {
    pub fn parse_fact(&mut self, tb: &mut TokenBlock) -> Result<Fact, RuntimeError> {
        if tb.current()? == NOT
            && tb.token_at_add_index(1) == FORALL
            && Self::uses_inline_forall_syntax(tb)
        {
            tb.skip_token(NOT)?;
            let fact = self.parse_inline_forall_fact(tb, false)?;
            match fact {
                Fact::ForallFact(forall_fact) => Ok(self.new_not_forall_fact(forall_fact).into()),
                _ => unreachable!("parse_inline_forall_fact only returns ForallFact"),
            }
        } else if tb.current()? == NOT && tb.token_at_add_index(1) == FORALL {
            tb.skip_token(NOT)?;
            let fact = self.parse_forall_or_forall_with_iff(tb)?;
            match fact {
                Fact::ForallFact(forall_fact) => Ok(self.new_not_forall_fact(forall_fact).into()),
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
    pub fn parse_inline_fact(
        &mut self,
        tb: &mut TokenBlock,
        nested: bool,
    ) -> Result<Fact, RuntimeError> {
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
            Ok(self.new_not_forall_fact(forall_fact).into())
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

    pub fn parse_inline_forall_fact(
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
                    this.parse_fresh_setting_parameter_bundle(tb, BindingScope::LocalBinder)?;
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
                return Ok(this
                    .new_forall_fact(
                        setting_prefix.param_def,
                        setting_prefix.dom_facts,
                        then_facts,
                        tb.line_file.clone(),
                    )?
                    .into());
            }

            let mut groups: Vec<TypedParameterGroup> = vec![];
            loop {
                let cur = tb.current()?;
                if cur == COLON || cur == RIGHT_ARROW || cur == LEFT_CURLY_BRACE {
                    break;
                }
                groups.push(this.parse_param_def_with_param_type_and_skip_comma(
                    tb,
                    BindingScope::LocalBinder,
                )?);
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
            let param_def = TypedParameterList::new(groups);
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

            this.end_parsing_scope(&forall_param_names);

            if !nested && !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("unexpected token after inline `{}`", FORALL),
                        tb.line_file.clone(),
                    ),
                )));
            }

            Ok(this
                .new_forall_fact(param_def, dom_facts, then_facts, tb.line_file.clone())?
                .into())
        })
    }

    fn parse_inline_forall_after_header(
        &mut self,
        tb: &mut TokenBlock,
        has_colon: bool,
    ) -> Result<(Vec<Fact>, Vec<ExistOrAndChainAtomicFact>), RuntimeError> {
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

    fn parse_inline_forall_then(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Vec<ExistOrAndChainAtomicFact>, RuntimeError> {
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
        Ok(vec![self.parse_forall_conclusion_fact(tb)?])
    }

    fn parse_forall_conclusion_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ExistOrAndChainAtomicFact, RuntimeError> {
        if tb.current()? == FORALL {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "a forall conclusion cannot contain another forall; move the inner parameters into the outer forall header"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.current()? == NOT && tb.token_at_add_index(1) == FORALL {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "a forall conclusion cannot contain `not forall`; name that quantified proposition before using it here"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        self.parse_exist_or_and_chain_atomic_fact(tb)
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
                    this.parse_fresh_setting_parameter_bundle(tb, BindingScope::LocalBinder)?;
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
                groups.push(this.parse_param_def_with_param_type_and_skip_comma(
                    tb,
                    BindingScope::LocalBinder,
                )?);
            }
            let param_def = TypedParameterList::new(groups);
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
        param_def: TypedParameterList,
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

        let forall_fact =
            self.new_forall_fact(param_def, dom_facts, then_facts, tb.line_file.clone())?;

        Ok(self
            .new_forall_fact_with_iff(forall_fact, iff_facts, tb.line_file.clone())?
            .into())
    }

    fn parse_forall(
        &mut self,
        tb: &mut TokenBlock,
        param_def: TypedParameterList,
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
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in last.body.iter_mut() {
                then_facts.push(self.parse_forall_conclusion_fact(block)?);
            }
            Ok(self
                .new_forall_fact(
                    param_def,
                    initial_dom_facts,
                    then_facts,
                    tb.line_file.clone(),
                )?
                .into())
        } else {
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in tb.body.iter_mut() {
                then_facts.push(self.parse_forall_conclusion_fact(block)?);
            }
            Ok(self
                .new_forall_fact(
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
                Ok(AndChainAtomicFact::AndFact(
                    self.new_and_fact(collected, tb.line_file.clone()),
                ))
            }
        }
    }

    pub fn parse_exist_fact(&mut self, tb: &mut TokenBlock) -> Result<ExistFact, RuntimeError> {
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
            let mut groups: Vec<TypedParameterGroup> = vec![];
            while tb.current()? != ST {
                groups.push(this.parse_param_def_with_param_type_and_skip_comma(
                    tb,
                    BindingScope::LocalBinder,
                )?);
            }
            let param_def = TypedParameterList::new(groups);
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
                    let body = inner.new_plain_exist_fact(param_def, facts, line_file)?;
                    Ok(if is_exist_unique {
                        ExistFact::ExistUniqueFact(body)
                    } else {
                        ExistFact::PlainExistFact(body)
                    })
                })();
                inner.end_parsing_scope(&exist_param_names);
                fact_result
            })
        })
    }

    pub fn parse_inline_quantifier_free_fact(
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
                        ExistFact::PlainExistFact(body) => ExistFact::NotExistFact(body),
                        ExistFact::ExistUniqueFact(_) | ExistFact::NotExistFact(_) => {
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
                Ok(ExistOrAndChainAtomicFact::OrFact(
                    self.new_or_fact(list, tb.line_file.clone()),
                ))
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
        positive_polarity: bool,
    ) -> Result<AtomicFact, RuntimeError> {
        if tb.current()? == NOT {
            tb.skip_token(NOT)?;
            return Ok(self.parse_atomic_fact(tb, !positive_polarity)?);
        }

        let line_file = tb.line_file.clone();
        if tb.current()? == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            let prop = self.parse_predicate(tb)?;
            let args = self.parse_braced_objs(tb)?;
            let atomic = AtomicFact::to_atomic_fact(self, prop, positive_polarity, args, line_file)
                .map_err(|e: RuntimeError| {
                    let msg = match &e {
                        RuntimeError::NewFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                    ))
                })?;
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
        let (prop, atomic_has_positive_polarity) = if tok == UNICODE_NOT_IN {
            tb.advance()?;
            (AtomicName::WithoutMod(IN.to_string()), !positive_polarity)
        } else if is_comparison_str(&tok) {
            tb.advance()?;
            (AtomicName::WithoutMod(tok.clone()), positive_polarity)
        } else if tok == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            (self.parse_predicate(tb)?, positive_polarity)
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
        let atomic =
            AtomicFact::to_atomic_fact(self, prop, atomic_has_positive_polarity, args, line_file)
                .map_err(|e: RuntimeError| {
                let msg = match &e {
                    RuntimeError::NewFactError(s) => s.msg.clone(),
                    _ => "parse atomic fact".to_string(),
                };
                RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
                ))
            })?;
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
        Ok(QuantifierFreeFact::OrFact(
            self.new_or_fact(list, tb.line_file.clone()),
        ))
    }

    /// Parse chain (obj op obj op ...) or single atomic ($prop(args) or obj op obj). When positive_polarity is false, only single atomic is allowed (negated).
    pub fn parse_chain_atomic(
        &mut self,
        tb: &mut TokenBlock,
        positive_polarity: bool,
    ) -> Result<ChainAtomicFact, RuntimeError> {
        let line_file = tb.line_file.clone();
        if tb.current()? == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            let prop = self.parse_predicate(tb)?;
            let args = self.parse_braced_objs(tb)?;
            let atomic = AtomicFact::to_atomic_fact(self, prop, positive_polarity, args, line_file)
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
                    self,
                    AtomicName::WithoutMod(IN.to_string()),
                    !positive_polarity,
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
        if !positive_polarity && (objs.len() > 2 || prop_names.len() > 1) {
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
            let atomic = AtomicFact::to_atomic_fact(self, prop, positive_polarity, args, line_file)
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
        Ok(ChainAtomicFact::ChainFact(
            self.new_chain_fact(objs, prop_names, line_file),
        ))
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/parsing/fact/expression/inline_forall.rs"]
mod inline_forall_tests;
