use crate::prelude::*;

impl Runtime {
    pub fn parse_fact(&mut self, tb: &mut TokenBlock) -> Result<Fact, ParsingError> {
        match tb.current()? {
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
    ) -> Result<Fact, ParsingError> {
        self.push_parsing_time_name_scope();
        let fact = self.parse_forall_or_forall_with_iff_body(tb);
        self.pop_parsing_time_name_scope();
        fact
    }

    fn parse_forall_or_forall_with_iff_body(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Fact, ParsingError> {
        tb.skip_token(FORALL)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != COLON {
            param_def.push(self.parse_param_def_with_param_type(tb)?);
        }
        let forall_param_names = ParamDefWithParamType::collect_param_names(&param_def);
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &forall_param_names,
            tb.line_file,
        )
        .map_err(|e| {
            ParsingError::new(
                e.to_string(),
                tb.line_file,
                Some(RuntimeError::ParseBlockError(e)),
            )
        })?;
        tb.skip_token(COLON)?;

        let last_body = tb
            .body
            .last()
            .ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file, None))?;
        if last_body.current()? == EQUIVALENT_SIGN {
            self.parse_forall_with_iff(tb, param_def)
        } else {
            self.parse_forall(tb, param_def)
        }
    }

    fn parse_forall_with_iff(
        &mut self,
        tb: &mut TokenBlock,
        param_def: Vec<ParamDefWithParamType>,
    ) -> Result<Fact, ParsingError> {
        if tb.body.len() < 2 {
            return Err(ParsingError::new(
                "Expected at least 2 body blocks".to_string(),
                tb.line_file,
                None,
            ));
        }

        let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        let mut iff_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        let body_len = tb.body.len();

        let iff_block = tb.body.get_mut(body_len - 1).ok_or_else(|| {
            ParsingError::new(
                "Expected <=>: block in forall body".to_string(),
                tb.line_file,
                None,
            )
        })?;
        iff_block.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
        for block in iff_block.body.iter_mut() {
            iff_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        let then_block = tb.body.get_mut(body_len - 2).ok_or_else(|| {
            ParsingError::new(
                "Expected =>: block in forall body".to_string(),
                tb.line_file,
                None,
            )
        })?;
        then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
        for block in then_block.body.iter_mut() {
            then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        for block in tb.body.iter_mut().take(body_len - 2) {
            dom_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        let forall_fact = ForallFact::new(param_def, dom_facts, then_facts, tb.line_file);

        Ok(Fact::ForallFactWithIff(ForallFactWithIff::new(
            forall_fact,
            iff_facts,
            tb.line_file,
        )))
    }

    fn parse_forall(
        &mut self,
        tb: &mut TokenBlock,
        param_def: Vec<ParamDefWithParamType>,
    ) -> Result<Fact, ParsingError> {
        let last_body = tb
            .body
            .last()
            .ok_or_else(|| ParsingError::new("Expected body".to_string(), tb.line_file, None))?;
        if last_body.current()? == RIGHT_ARROW {
            let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = vec![];
            let n = tb.body.len();
            for block in tb.body.iter_mut().take(n - 1) {
                dom_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
            }
            let last = tb.body.last_mut().ok_or_else(|| {
                ParsingError::new("Expected body".to_string(), tb.line_file, None)
            })?;
            last.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in last.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
            }
            Ok(Fact::ForallFact(ForallFact::new(
                param_def,
                dom_facts,
                then_facts,
                tb.line_file,
            )))
        } else {
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in tb.body.iter_mut() {
                then_facts.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
            }
            Ok(Fact::ForallFact(ForallFact::new(
                param_def,
                vec![],
                then_facts,
                tb.line_file,
            )))
        }
    }

    // hierarchy 3: and 并列
    pub fn parse_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<AndChainAtomicFact, ParsingError> {
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
                    tb.line_file,
                )))
            }
        }
    }

    pub fn parse_exist_fact(&mut self, tb: &mut TokenBlock) -> Result<ExistFact, ParsingError> {
        self.push_parsing_time_name_scope();
        let fact = self.parse_exist_fact_body(tb);
        self.pop_parsing_time_name_scope();
        fact
    }

    fn parse_exist_fact_body(&mut self, tb: &mut TokenBlock) -> Result<ExistFact, ParsingError> {
        tb.skip_token(EXIST)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != ST {
            param_def.push(self.parse_param_def_with_param_type(tb)?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        let exist_param_names = ParamDefWithParamType::collect_param_names(&param_def);
        self.push_parsing_time_name_scope();
        self.validate_names_and_insert_into_top_parsing_time_name_scope(
            &exist_param_names,
            tb.line_file,
        )
        .map_err(|e| {
            ParsingError::new(
                e.to_string(),
                tb.line_file,
                Some(RuntimeError::ParseBlockError(e)),
            )
        })?;
        tb.skip_token(ST)?;

        tb.skip_token(LEFT_CURLY_BRACE)?;

        let mut facts: Vec<OrAndChainAtomicFact> = vec![];
        loop {
            facts.push(self.parse_or_and_chain_atomic_fact(tb)?);
            if tb.current()? != RIGHT_CURLY_BRACE {
                tb.skip_token(COMMA)?;
            } else {
                break;
            }
        }
        tb.skip_token(RIGHT_CURLY_BRACE)?;

        self.pop_parsing_time_name_scope();
        let line = tb.line_file;
        Ok(ExistFact::new(param_def, facts, line))
    }

    pub fn parse_facts_in_body(&mut self, tb: &mut TokenBlock) -> Result<Vec<Fact>, ParsingError> {
        let mut facts: Vec<Fact> = vec![];
        for block in tb.body.iter_mut() {
            facts.push(self.parse_fact(block)?);
        }
        Ok(facts)
    }

    pub fn parse_exist_or_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ExistOrAndChainAtomicFact, ParsingError> {
        match tb.current()? {
            EXIST => {
                let exist_fact = self.parse_exist_fact(tb)?;
                Ok(ExistOrAndChainAtomicFact::ExistFact(exist_fact))
            }
            NOT => {
                tb.skip_token(NOT)?;
                Ok(self
                    .parse_atomic_fact(tb, false)
                    .map(|a| ExistOrAndChainAtomicFact::AtomicFact(a))?)
            }
            _ => Ok(self
                .parse_or_and_chain_atomic_fact(tb)?
                .to_exist_or_and_chain_atomic_fact()),
        }
    }

    /// Parse a single atomic fact only: $prop(args) or obj op obj. Does not parse chain (obj op obj op obj).
    pub fn parse_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
        is_true: bool,
    ) -> Result<AtomicFact, ParsingError> {
        if tb.current()? == NOT {
            tb.skip_token(NOT)?;
            return Ok(self.parse_atomic_fact(tb, !is_true)?);
        }

        let line_file = tb.line_file;
        if tb.current()? == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            let prop = self.parse_identifier_or_identifier_with_mod(tb)?;
            let args = self.parse_braced_objs(tb)?;
            let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
                |e: RuntimeErrorStruct| ParsingError::new(e.msg.clone(), tb.line_file, None),
            )?;
            return Ok(atomic);
        }
        let first_obj = self.parse_obj(tb)?;
        if tb.exceed_end_of_head() {
            return Err(ParsingError::new(
                "Expected operator or $prop in atomic fact".to_string(),
                tb.line_file,
                None,
            ));
        }
        let tok = tb.current()?.to_string();
        let prop = if is_comparison_str(&tok) {
            tb.advance()?;
            IdentifierOrIdentifierWithMod::Identifier(Identifier::new(tok.clone()))
        } else if tok == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            self.parse_identifier_or_identifier_with_mod(tb)?
        } else {
            return Err(ParsingError::new(
                "Expected operator or $prop in atomic fact".to_string(),
                tb.line_file,
                None,
            ));
        };
        let next_obj = self.parse_obj(tb)?;
        let args = vec![first_obj, next_obj];
        let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
            |e: RuntimeErrorStruct| ParsingError::new(e.msg.clone(), tb.line_file, None),
        )?;
        Ok(atomic)
    }

    pub fn parse_or_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<OrAndChainAtomicFact, ParsingError> {
        let first = self.parse_and_chain_atomic_fact(tb)?;
        let mut list: Vec<AndChainAtomicFact> = vec![first];
        while !tb.exceed_end_of_head() && tb.current()? == OR {
            tb.skip_token(OR)?;
            list.push(self.parse_and_chain_atomic_fact(tb)?);
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
            tb.line_file,
        )))
    }

    /// Parse chain (obj op obj op ...) or single atomic ($prop(args) or obj op obj). When is_true is false, only single atomic is allowed (negated).
    pub fn parse_chain_atomic(
        &mut self,
        tb: &mut TokenBlock,
        is_true: bool,
    ) -> Result<ChainAtomicFact, ParsingError> {
        let line_file = tb.line_file;
        if tb.current()? == FACT_PREFIX {
            tb.skip_token(FACT_PREFIX)?;
            let prop = self.parse_identifier_or_identifier_with_mod(tb)?;
            let args = self.parse_braced_objs(tb)?;
            let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
                |e: RuntimeErrorStruct| ParsingError::new(e.msg.clone(), tb.line_file, None),
            )?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }
        let first_obj = self.parse_obj(tb)?;
        let mut objs: Vec<crate::obj::Obj> = vec![first_obj];
        let mut prop_names: Vec<IdentifierOrIdentifierWithMod> = vec![];
        while !tb.exceed_end_of_head() {
            let tok = tb.current()?.to_string();
            let prop = if is_comparison_str(&tok) {
                tb.advance()?;
                IdentifierOrIdentifierWithMod::Identifier(Identifier::new(tok.clone()))
            } else if tok == FACT_PREFIX {
                tb.skip_token(FACT_PREFIX)?;
                self.parse_identifier_or_identifier_with_mod(tb)?
            } else {
                break;
            };
            let next_obj = self.parse_obj(tb)?;
            prop_names.push(prop);
            objs.push(next_obj);
        }
        if prop_names.is_empty() {
            return Err(ParsingError::new(
                "Expected operator or $prop in fact".to_string(),
                tb.line_file,
                None,
            ));
        }
        if !is_true && (objs.len() > 2 || prop_names.len() > 1) {
            return Err(ParsingError::new(
                "Negated fact must be single atomic (one operator)".to_string(),
                tb.line_file,
                None,
            ));
        }
        if objs.len() == 2 && prop_names.len() == 1 {
            let prop = prop_names.remove(0);
            let args = objs;
            let atomic = AtomicFact::to_atomic_fact(prop, is_true, args, line_file).map_err(
                |e: RuntimeErrorStruct| ParsingError::new(e.msg.clone(), tb.line_file, None),
            )?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }
        Ok(ChainAtomicFact::ChainFact(ChainFact::new(
            objs, prop_names, line_file,
        )))
    }
}
