use crate::prelude::*;

impl Runtime {
    pub fn parse_fact(&mut self, tb: &mut TokenBlock) -> Result<Fact, RuntimeError> {
        match tb.current()? {
            NOT if tb.token_at_add_index(1) == FORALL => {
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
            }
            FORALL => self.parse_forall_or_forall_with_iff(tb),
            _ => {
                let or_and_spec_fact = self.parse_exist_or_and_chain_atomic_fact(tb)?;
                Ok(or_and_spec_fact.to_fact())
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
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("Expected body".to_string(), tb.line_file.clone())))
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
                RuntimeErrorStruct::new_with_msg_and_line_file("Expected at least 2 body blocks".to_string(), tb.line_file.clone()),
            )));
        }

        let mut dom_facts: Vec<Fact> = Vec::new();
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        let mut iff_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        let body_len = tb.body.len();

        let iff_block = tb.body.get_mut(body_len - 1).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("Expected <=>: block in forall body".to_string(), tb.line_file.clone())))
        })?;
        iff_block.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
        for block in iff_block.body.iter_mut() {
            iff_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        let then_block = tb.body.get_mut(body_len - 2).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("Expected =>: block in forall body".to_string(), tb.line_file.clone())))
        })?;
        then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
        for block in then_block.body.iter_mut() {
            then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        for block in tb.body.iter_mut().take(body_len - 2) {
            dom_facts.push(self.parse_fact(block)?);
        }

        let forall_fact = ForallFact::new(param_def, dom_facts, then_facts, tb.line_file.clone());

        Ok(ForallFactWithIff::new(forall_fact, iff_facts, tb.line_file.clone()).into())
    }

    fn parse_forall(
        &mut self,
        tb: &mut TokenBlock,
        param_def: ParamDefWithType,
    ) -> Result<Fact, RuntimeError> {
        let last_body = tb.body.last().ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("Expected body".to_string(), tb.line_file.clone())))
        })?;
        if last_body.current()? == RIGHT_ARROW {
            let mut dom_facts: Vec<Fact> = vec![];
            let n = tb.body.len();
            for block in tb.body.iter_mut().take(n - 1) {
                dom_facts.push(self.parse_fact(block)?);
            }
            let last = tb.body.last_mut().ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("Expected body".to_string(), tb.line_file.clone())))
            })?;
            last.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in last.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
            }
            Ok(ForallFact::new(param_def, dom_facts, then_facts, tb.line_file.clone()).into())
        } else {
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in tb.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
            }
            Ok(ForallFact::new(param_def, vec![], then_facts, tb.line_file.clone()).into())
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

                    let mut facts: Vec<OrAndChainAtomicFact> = vec![];
                    loop {
                        facts.push(inner.parse_or_and_chain_atomic_fact(tb)?);
                        if tb.current()? != RIGHT_CURLY_BRACE {
                            tb.skip_token(COMMA)?;
                        } else {
                            break;
                        }
                    }
                    tb.skip_token(RIGHT_CURLY_BRACE)?;

                    let line_file = tb.line_file.clone();
                    let body = ExistFactBody::new(param_def, facts, line_file);
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
                        AndChainAtomicFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
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
                    RuntimeErrorStruct::new_with_msg_and_line_file("Expected exist or and chain atomic fact".to_string(), tb.line_file.clone()),
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
                        RuntimeError::NewAtomicFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone())))
                },
            )?;
            return Ok(atomic);
        }
        let first_obj = self.parse_obj(tb)?;
        if tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file("Expected operator or $prop in atomic fact".to_string(), tb.line_file.clone()),
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
                RuntimeErrorStruct::new_with_msg_and_line_file("Expected operator or $prop in atomic fact".to_string(), tb.line_file.clone()),
            )));
        };
        let next_obj = self.parse_obj(tb)?;
        let args = vec![first_obj, next_obj];
        let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
            |e: RuntimeError| {
                let msg = match &e {
                    RuntimeError::NewAtomicFactError(s) => s.msg.clone(),
                    _ => "parse atomic fact".to_string(),
                };
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone())))
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
        let first = self.parse_and_chain_atomic_fact(tb)?;
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
                        RuntimeError::NewAtomicFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone())))
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
                RuntimeErrorStruct::new_with_msg_and_line_file("Expected operator or $prop in fact".to_string(), tb.line_file.clone()),
            )));
        }
        if !is_true && (objs.len() > 2 || prop_names.len() > 1) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file("Negated fact must be single atomic (one operator)".to_string(), tb.line_file.clone()),
            )));
        }
        if objs.len() == 2 && prop_names.len() == 1 {
            let prop = prop_names.remove(0);
            let args = objs;
            let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
                |e: RuntimeError| {
                    let msg = match &e {
                        RuntimeError::NewAtomicFactError(s) => s.msg.clone(),
                        _ => "parse atomic fact".to_string(),
                    };
                    RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone())))
                },
            )?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }
        Ok(ChainAtomicFact::ChainFact(ChainFact::new(
            objs, prop_names, line_file,
        )))
    }
}
