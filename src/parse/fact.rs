use super::fact_prop::is_infix_prop_name;
use super::keywords::{
    is_comparison_op, AND, EQUIVALENT_SIGN, EXIST, EXIST_BANG, FACT_PREFIX, FORALL, IN,
    MOD_FLAT_SIGN, MOD_SIGN, NOT, OR, RIGHT_ARROW,
};
use super::object::{parse_obj, parse_obj_list_paren};
use crate::ast::fact::{
    AndChainAtomicFact, AndFact, AtomicFact, ChainAtomicFact, ChainFact, ExistShapedFact,
    ExistOrAndChainAtomicFact, Fact, ForallFact, ForallFactWithIff, NotForallFact, OrFact,
    PlainExistFact, QuantifierFreeFact,
};
use crate::ast::names::AtomicName;
use crate::ast::stmt::Stmt;
use crate::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    pub(super) fn parse_fact_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        let fact = self.parse_fact(&mut tb)?;
        match &fact {
            Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {}
            _ if !tb.exceed_end_of_head() => {
                return Err(RuntimeParseError::new(
                    format!("trailing tokens after fact: `{}`", tb.peek().unwrap_or("")),
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            _ => {}
        }
        Ok(Stmt::Fact(fact))
    }

    pub(super) fn parse_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Fact> {
        match tb.peek() {
            Some(FORALL) => self.parse_forall_fact(tb),
            Some(EXIST) | Some(EXIST_BANG) => Ok(crate::ast::fact::exist_shaped_fact_to_fact(&self.parse_exist_fact(tb)?)),
            Some(NOT) => self.parse_not_fact(tb),
            _ => Ok(self.parse_quantifier_free_fact_top(tb)?.into_fact()),
        }
    }

    fn parse_not_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Fact> {
        tb.expect(NOT)?;
        match tb.peek() {
            Some(FORALL) => Ok(Fact::NotForall(self.parse_not_forall_fact(tb)?)),
            Some(EXIST) | Some(EXIST_BANG) => {
                if tb.peek() == Some(EXIST_BANG)
                    || (tb.peek() == Some(EXIST) && tb.peek_at(1) == Some(super::keywords::BANG))
                {
                    return Err(RuntimeParseError::new(
                        "`not exist!` is not supported",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let ExistShapedFact::Exist(body) = self.parse_exist_fact(tb)? else {
                    return Err(RuntimeParseError::new(
                        "`not exist` expects a plain exist fact",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                };
                Ok(Fact::NotExistFact(body))
            }
            _ => {
                // `not` already consumed; parse a single atomic with negative polarity.
                let atomic = self.parse_chain_or_atomic(tb, false)?;
                match atomic {
                    ChainAtomicFact::AtomicFact(a) => Ok(Fact::AtomicFact(a)),
                    ChainAtomicFact::ChainFact(_) => Err(RuntimeParseError::new(
                        "negated fact must be a single atomic (one operator)",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into()),
                }
            }
        }
    }

    // `not forall` body is QuantifierFree only (same as exist body shapes).
    // Reject `<=>:` and nested exist/forall at parse.
    fn parse_not_forall_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<NotForallFact> {
        self.push_parse_scope();
        let result = (|| {
            tb.expect(FORALL)?;
            let params = self.parse_typed_param_list_until_colon(tb)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeParseError::new(
                    "trailing tokens after `not forall` header",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            if tb.body.is_empty() {
                return Err(RuntimeParseError::new(
                    "`not forall` expects an indented body",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            let last_header = tb
                .body
                .last()
                .and_then(|b| b.header.first())
                .map(String::as_str);
            if last_header == Some(EQUIVALENT_SIGN) {
                return Err(RuntimeParseError::new(
                    "`not forall` does not support `<=>:`",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            let mut dom_facts = Vec::new();
            let mut then_facts = Vec::new();
            if last_header == Some(RIGHT_ARROW) {
                let n = tb.body.len();
                for block in tb.body.iter().take(n - 1) {
                    let mut child = block.clone();
                    dom_facts.push(self.parse_quantifier_free_fact_top(&mut child)?);
                }
                let mut then_block = tb.body[n - 1].clone();
                then_block.expect(RIGHT_ARROW)?;
                then_block.expect(super::keywords::COLON)?;
                if !then_block.exceed_end_of_head() {
                    return Err(RuntimeParseError::new(
                        "trailing tokens after `=>:`",
                        then_block.line,
                        then_block.source_path.clone(),
                    )
                    .into());
                }
                for block in &then_block.body {
                    let mut child = block.clone();
                    then_facts.push(self.parse_quantifier_free_fact_top(&mut child)?);
                }
            } else {
                for block in &tb.body {
                    let mut child = block.clone();
                    then_facts.push(self.parse_quantifier_free_fact_top(&mut child)?);
                }
            }

            if then_facts.is_empty() {
                return Err(RuntimeParseError::new(
                    "`not forall` expects at least one conclusion fact",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            Ok(NotForallFact {
                fact_id: self.global_ids.allocate_fact_id(),
                typed_parameters: params,
                dom_facts,
                then_facts,
                line_file: Some(tb.line_file(self.code_source.clone())),
            })
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_forall_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Fact> {
        self.push_parse_scope();
        let result = (|| {
            tb.expect(FORALL)?;
            let params = self.parse_typed_param_list_until_colon_or_arrow(tb)?;

            match tb.peek() {
                Some(RIGHT_ARROW) => {
                    // `forall x Dom => P`
                    return self.finish_inline_forall(tb, params, false);
                }
                Some(super::keywords::COLON) => {
                    tb.expect(super::keywords::COLON)?;
                    if !tb.exceed_end_of_head() {
                        // `forall x Dom: D => P`
                        return self.finish_inline_forall(tb, params, true);
                    }
                }
                _ => {
                    return Err(RuntimeParseError::new(
                        "forall: expected `:` or `=>` after parameters",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
            }

            if tb.body.is_empty() {
                return Err(RuntimeParseError::new(
                    "forall expects an indented body",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            let last_header = tb
                .body
                .last()
                .and_then(|b| b.header.first())
                .map(String::as_str);
            let last_is_arrow = last_header == Some(RIGHT_ARROW);
            let last_is_iff = last_header == Some(EQUIVALENT_SIGN);

            let mut dom_facts = Vec::new();
            let mut then_facts = Vec::new();

            if last_is_iff {
                let n = tb.body.len();
                if n < 2 {
                    return Err(RuntimeParseError::new(
                        "forall with `<=>:` expects a `=>:` block before it",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let then_header = tb.body[n - 2].header.first().map(String::as_str);
                if then_header != Some(RIGHT_ARROW) {
                    return Err(RuntimeParseError::new(
                        "forall with `<=>:` expects the previous block to be `=>:`",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                for block in tb.body.iter().take(n - 2) {
                    let mut child = block.clone();
                    dom_facts.push(self.parse_fact(&mut child)?);
                }
                let mut then_block = tb.body[n - 2].clone();
                then_block.expect(RIGHT_ARROW)?;
                then_block.expect(super::keywords::COLON)?;
                for block in &then_block.body {
                    let mut child = block.clone();
                    then_facts.push(self.parse_exist_or_and_chain_atomic_fact(&mut child)?);
                }
                let mut iff_block = tb.body[n - 1].clone();
                iff_block.expect(EQUIVALENT_SIGN)?;
                iff_block.expect(super::keywords::COLON)?;
                let mut iff_facts = Vec::new();
                for block in &iff_block.body {
                    let mut child = block.clone();
                    iff_facts.push(self.parse_exist_or_and_chain_atomic_fact(&mut child)?);
                }
                if then_facts.is_empty() {
                    return Err(RuntimeParseError::new(
                        "forall expects at least one conclusion fact",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let forall_fact = ForallFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    typed_parameters: params,
                    dom_facts,
                    then_facts,
                    line_file: Some(tb.line_file(self.code_source.clone())),
                };
                return Ok(Fact::ForallFactWithIff(ForallFactWithIff {
                    fact_id: self.global_ids.allocate_fact_id(),
                    forall_fact,
                    iff_facts,
                    line_file: Some(tb.line_file(self.code_source.clone())),
                }));
            }

            if last_is_arrow {
                let n = tb.body.len();
                for block in tb.body.iter().take(n - 1) {
                    let mut child = block.clone();
                    dom_facts.push(self.parse_fact(&mut child)?);
                }
                let mut then_block = tb.body[n - 1].clone();
                then_block.expect(RIGHT_ARROW)?;
                then_block.expect(super::keywords::COLON)?;
                if !then_block.exceed_end_of_head() {
                    return Err(RuntimeParseError::new(
                        "trailing tokens after `=>:`",
                        then_block.line,
                        then_block.source_path.clone(),
                    )
                    .into());
                }
                for block in &then_block.body {
                    let mut child = block.clone();
                    then_facts.push(self.parse_exist_or_and_chain_atomic_fact(&mut child)?);
                }
            } else {
                for block in &tb.body {
                    let mut child = block.clone();
                    then_facts.push(self.parse_exist_or_and_chain_atomic_fact(&mut child)?);
                }
            }

            if then_facts.is_empty() {
                return Err(RuntimeParseError::new(
                    "forall expects at least one conclusion fact",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            Ok(Fact::ForallFact(ForallFact {
                fact_id: self.global_ids.allocate_fact_id(),
                typed_parameters: params,
                dom_facts,
                then_facts,
                line_file: Some(tb.line_file(self.code_source.clone())),
            }))
        })();
        self.pop_parse_scope();
        result
    }

    // Finish inline forall after binders (and optional `:` already consumed).
    // `has_dom_segment`: true for `forall x Dom: D => P`, false for `forall x Dom => P`.
    fn finish_inline_forall(
        &mut self,
        tb: &mut TokenBlock,
        params: crate::ast::param::TypedParameterList,
        has_dom_segment: bool,
    ) -> RuntimeResult<Fact> {
        if !tb.body.is_empty() {
            return Err(RuntimeParseError::new(
                "inline forall must be on one line (no indented body)",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }

        let mut dom_facts = Vec::new();
        if has_dom_segment {
            if tb.exceed_end_of_head() || tb.peek() == Some(RIGHT_ARROW) {
                return Err(RuntimeParseError::new(
                    "inline forall with `:` expects one domain fact before `=>`",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            dom_facts.push(self.parse_fact(tb)?);
        }

        tb.expect(RIGHT_ARROW)?;
        if tb.exceed_end_of_head() {
            return Err(RuntimeParseError::new(
                "inline forall: `=>` expects a conclusion fact",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        let then_fact = self.parse_exist_or_and_chain_atomic_fact(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeParseError::new(
                format!(
                    "trailing tokens after inline forall: `{}`",
                    tb.peek().unwrap_or("")
                ),
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }

        Ok(Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: params,
            dom_facts,
            then_facts: vec![then_fact],
            line_file: Some(tb.line_file(self.code_source.clone())),
        }))
    }

    pub(super) fn parse_exist_fact(&mut self, tb: &mut TokenBlock) -> RuntimeResult<ExistShapedFact> {
        self.push_parse_scope();
        let result = (|| {
            let unique = match tb.peek() {
                Some(EXIST_BANG) => {
                    tb.advance()?;
                    true
                }
                Some(EXIST) => {
                    tb.advance()?;
                    if tb.peek() == Some(super::keywords::BANG) {
                        tb.advance()?;
                        true
                    } else {
                        false
                    }
                }
                _ => {
                    return Err(RuntimeParseError::new(
                        "expected `exist` or `exist!`",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
            };

            let params = self.parse_typed_param_list_until_st(tb)?;
            tb.expect(super::keywords::ST)?;
            tb.expect(super::keywords::LEFT_CURLY)?;

            let mut facts = Vec::new();
            loop {
                facts.push(self.parse_quantifier_free_fact_inline(tb)?);
                if tb.peek() == Some(super::keywords::RIGHT_CURLY) {
                    break;
                }
                tb.expect(super::keywords::COMMA)?;
            }
            tb.expect(super::keywords::RIGHT_CURLY)?;
            if !tb.body.is_empty() {
                return Err(RuntimeParseError::new(
                    "inline `exist … st {…}` cannot have an indented body",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            if facts.is_empty() {
                return Err(RuntimeParseError::new(
                    "exist body cannot be empty",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }

            let body = PlainExistFact {
                fact_id: self.global_ids.allocate_fact_id(),
                typed_parameters: params,
                facts,
                line_file: Some(tb.line_file(self.code_source.clone())),
            };
            Ok(if unique {
                ExistShapedFact::ExistUnique(body)
            } else {
                ExistShapedFact::Exist(body)
            })
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_exist_or_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<ExistOrAndChainAtomicFact> {
        match tb.peek() {
            Some(EXIST) | Some(EXIST_BANG) => {
                match self.parse_exist_fact(tb)? {
                    ExistShapedFact::Exist(p) => Ok(ExistOrAndChainAtomicFact::ExistFact(p)),
                    ExistShapedFact::ExistUnique(p) => {
                        Ok(ExistOrAndChainAtomicFact::ExistUniqueFact(p))
                    }
                    ExistShapedFact::NotExist(_) => Err(RuntimeParseError::new(
                        "internal: parse_exist_fact returned not-exist",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into()),
                }
            }
            Some(NOT) if tb.peek_at(1) == Some(EXIST) => {
                tb.expect(NOT)?;
                if tb.peek() == Some(EXIST_BANG)
                    || (tb.peek() == Some(EXIST) && tb.peek_at(1) == Some(super::keywords::BANG))
                {
                    return Err(RuntimeParseError::new(
                        "`not exist!` is not supported",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let ExistShapedFact::Exist(body) = self.parse_exist_fact(tb)? else {
                    return Err(RuntimeParseError::new(
                        "`not exist` expects a plain exist fact",
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                };
                Ok(ExistOrAndChainAtomicFact::NotExistFact(body))
            }
            Some(FORALL) => Err(RuntimeParseError::new(
                "nested `forall` is not allowed here",
                tb.line,
                tb.source_path.clone(),
            )
            .into()),
            _ => Ok(self.parse_quantifier_free_fact_top(tb)?.into_exist_or_and()),
        }
    }

    pub(super) fn parse_quantifier_free_fact_top(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<QuantifierFreeFact> {
        let fact = self.parse_quantifier_free_fact_inline(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeParseError::new(
                format!("trailing tokens in fact: `{}`", tb.peek().unwrap_or("")),
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        if !tb.body.is_empty() {
            return Err(RuntimeParseError::new(
                "this fact form cannot have an indented body",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }
        Ok(fact)
    }

    pub(super) fn parse_quantifier_free_fact_inline(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<QuantifierFreeFact> {
        // Allow leading `not` so exist bodies can hold De Morgan counterexamples
        // like `exist x R st {not x > 0}`.
        let first = self.parse_and_chain_atomic_fact_allow_not(tb)?;
        let mut list = vec![first];
        while tb.peek() == Some(OR) {
            tb.advance()?;
            list.push(self.parse_and_chain_atomic_fact_allow_not(tb)?);
        }
        if list.len() == 1 {
            return Ok(match list.remove(0) {
                AndChainAtomicFact::AtomicFact(a) => QuantifierFreeFact::AtomicFact(a),
                AndChainAtomicFact::AndFact(a) => QuantifierFreeFact::AndFact(a),
                AndChainAtomicFact::ChainFact(c) => QuantifierFreeFact::ChainFact(c),
            });
        }
        Ok(QuantifierFreeFact::OrFact(OrFact {
            fact_id: self.global_ids.allocate_fact_id(),
            facts: list,
            line_file: Some(tb.line_file(self.code_source.clone())),
        }))
    }

    pub(super) fn parse_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
        positive: bool,
    ) -> RuntimeResult<AtomicFact> {
        match self.parse_chain_or_atomic(tb, positive)? {
            ChainAtomicFact::AtomicFact(a) => Ok(a),
            ChainAtomicFact::ChainFact(_) => Err(RuntimeParseError::new(
                "expected a single atomic fact (one operator)",
                tb.line,
                tb.source_path.clone(),
            )
            .into()),
        }
    }

    pub(super) fn parse_and_chain_atomic_fact(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<AndChainAtomicFact> {
        let first = self.parse_chain_or_atomic(tb, true)?;
        match first {
            ChainAtomicFact::ChainFact(c) => Ok(AndChainAtomicFact::ChainFact(c)),
            ChainAtomicFact::AtomicFact(a) => {
                let mut collected = vec![a];
                while tb.peek() == Some(AND) {
                    tb.advance()?;
                    match self.parse_chain_or_atomic(tb, true)? {
                        ChainAtomicFact::AtomicFact(next) => collected.push(next),
                        ChainAtomicFact::ChainFact(_) => {
                            return Err(RuntimeParseError::new(
                                "`and` cannot combine chain facts",
                                tb.line,
                                tb.source_path.clone(),
                            )
                            .into());
                        }
                    }
                }
                if collected.len() == 1 {
                    Ok(AndChainAtomicFact::AtomicFact(collected.remove(0)))
                } else {
                    Ok(AndChainAtomicFact::AndFact(AndFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        facts: collected,
                        line_file: Some(tb.line_file(self.code_source.clone())),
                    }))
                }
            }
        }
    }

    // Case arms may start with `not`.
    pub(super) fn parse_and_chain_atomic_fact_allow_not(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<AndChainAtomicFact> {
        if tb.peek() == Some(NOT) {
            tb.advance()?;
            Ok(AndChainAtomicFact::AtomicFact(
                self.parse_atomic_fact(tb, false)?,
            ))
        } else {
            self.parse_and_chain_atomic_fact(tb)
        }
    }

    // obj op obj [op obj…] / `$prop(...)` / infix `$in` `$subset` …
    fn parse_chain_or_atomic(
        &mut self,
        tb: &mut TokenBlock,
        positive: bool,
    ) -> RuntimeResult<ChainAtomicFact> {
        let line_file = tb.line_file(self.code_source.clone());

        if tb.peek() == Some(FACT_PREFIX) {
            tb.advance()?;
            let prop = self.parse_prop_name(tb)?;
            if matches!(&prop, AtomicName::Plain { name } if name == IN) {
                return Err(RuntimeParseError::new(
                    "leading `$in` is invalid; write `x $in S`",
                    tb.line,
                    tb.source_path.clone(),
                )
                .into());
            }
            let args = parse_obj_list_paren(self, tb)?;
            let atomic = self.atomic_from_prop(prop, args, positive, line_file)?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }

        let first = parse_obj(self, tb)?;
        let mut objs = vec![first];
        let mut prop_names: Vec<AtomicName> = Vec::new();

        while !tb.exceed_end_of_head() {
            let Some(tok) = tb.peek().map(str::to_string) else {
                break;
            };
            if tok == FACT_PREFIX {
                tb.advance()?;
                let prop = self.parse_prop_name(tb)?;
                let prop_str = match &prop {
                    AtomicName::Plain { name } => name.as_str(),
                    AtomicName::WithExportFileId { .. }
                    | AtomicName::WithModAndExportFileId { .. } => {
                        return Err(RuntimeParseError::new(
                            "mod-qualified infix `$Mod::prop` is not supported; use `$Mod::prop(...)`",
                            tb.line,
                            tb.source_path.clone(),
                        )
                        .into());
                    }
                };
                if !is_infix_prop_name(prop_str) {
                    return Err(RuntimeParseError::new(
                        format!("`{prop_str}` is not a valid infix prop; use `${prop_str}(...)`"),
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                if !prop_names.is_empty()
                    && (prop_str == IN
                        || prop_str == super::fact_prop::SUBSET
                        || prop_str == super::fact_prop::SUPERSET)
                {
                    return Err(RuntimeParseError::new(
                        format!("`${prop_str}` cannot appear in a comparison chain"),
                        tb.line,
                        tb.source_path.clone(),
                    )
                    .into());
                }
                let right = parse_obj(self, tb)?;
                if prop_names.is_empty()
                    && (prop_str == IN
                        || prop_str == super::fact_prop::SUBSET
                        || prop_str == super::fact_prop::SUPERSET)
                {
                    if !tb.exceed_end_of_head()
                        && (tb.peek().map(is_comparison_op).unwrap_or(false)
                            || tb.peek() == Some(FACT_PREFIX))
                    {
                        return Err(RuntimeParseError::new(
                            format!("`${prop_str}` cannot appear in a comparison chain"),
                            tb.line,
                            tb.source_path.clone(),
                        )
                        .into());
                    }
                    let left = objs.remove(0);
                    let atomic =
                        self.atomic_from_prop(prop, vec![left, right], positive, line_file)?;
                    return Ok(ChainAtomicFact::AtomicFact(atomic));
                }
                prop_names.push(prop);
                objs.push(right);
                continue;
            }
            if is_comparison_op(&tok) {
                tb.advance()?;
                prop_names.push(AtomicName::Plain { name: tok });
                objs.push(parse_obj(self, tb)?);
                continue;
            }
            break;
        }

        if prop_names.is_empty() {
            return Err(RuntimeParseError::new(
                "expected comparison operator or `$prop`",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }

        if objs.len() == 2 && prop_names.len() == 1 {
            let right = objs.pop().unwrap();
            let left = objs.pop().unwrap();
            let prop = prop_names.pop().unwrap();
            let atomic = self.atomic_from_prop(prop, vec![left, right], positive, line_file)?;
            return Ok(ChainAtomicFact::AtomicFact(atomic));
        }

        if !positive {
            return Err(RuntimeParseError::new(
                "negated fact must be a single atomic (one operator)",
                tb.line,
                tb.source_path.clone(),
            )
            .into());
        }

        Ok(ChainAtomicFact::ChainFact(ChainFact {
            fact_id: self.global_ids.allocate_fact_id(),
            objs,
            prop_names,
            line_file: Some(line_file),
        }))
    }

    pub(in crate::parse) fn parse_prop_name(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<AtomicName> {
        let first = tb.advance()?;
        if tb.peek() == Some(MOD_FLAT_SIGN) {
            tb.advance()?;
            let next = tb.advance()?;
            return self.elaborate_flat_import(&first, next);
        }
        if tb.peek() != Some(MOD_SIGN) {
            // File-root defined props qualify; builtins / unknowns stay Plain.
            return Ok(self.atomic_name_for_plain_prop_ref(first));
        }
        let mut parts = vec![first];
        while tb.peek() == Some(MOD_SIGN) {
            tb.advance()?;
            let next = tb.advance()?;
            parts.push(next);
        }
        match parts.len() {
            2 | 3 => self.elaborate_name_parts(&parts),
            _ => Err(RuntimeParseError::new(
                "qualified prop name must be `a::b`, `a:::b`, or `a::b::c`",
                tb.line,
                tb.source_path.clone(),
            )
            .into()),
        }
    }
}

trait QuantifierFreeFactExt {
    fn into_fact(self) -> Fact;
    fn into_exist_or_and(self) -> ExistOrAndChainAtomicFact;
}

impl QuantifierFreeFactExt for QuantifierFreeFact {
    fn into_fact(self) -> Fact {
        match self {
            QuantifierFreeFact::AtomicFact(a) => Fact::AtomicFact(a),
            QuantifierFreeFact::AndFact(a) => Fact::AndFact(a),
            QuantifierFreeFact::ChainFact(c) => Fact::ChainFact(c),
            QuantifierFreeFact::OrFact(o) => Fact::OrFact(o),
        }
    }

    fn into_exist_or_and(self) -> ExistOrAndChainAtomicFact {
        match self {
            QuantifierFreeFact::AtomicFact(a) => ExistOrAndChainAtomicFact::AtomicFact(a),
            QuantifierFreeFact::AndFact(a) => ExistOrAndChainAtomicFact::AndFact(a),
            QuantifierFreeFact::ChainFact(c) => ExistOrAndChainAtomicFact::ChainFact(c),
            QuantifierFreeFact::OrFact(o) => ExistOrAndChainAtomicFact::OrFact(o),
        }
    }
}
