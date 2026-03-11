use crate::fact::{
    ExistFact, AndFactOrChainFactOrAtomicFact, FactInsideExistFact, ExistOrAndChainAtomicFact,
    NotExistFact, TrueExistFact,
};
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;
use crate::fact::OrFactOrAndFactOrSpecFact;
use crate::fact::ForallFact;
use crate::fact::ForallFactWithIff;
use super::Parser;
use super::TokenBlock;
use crate::error::{ParsingError};
use crate::fact::Fact;
use crate::common::keywords::{COLON, COMMA, EQUIVALENT_SIGN, EXIST, FORALL, OR, RIGHT_ARROW, ST};
use crate::fact::OrFact;

impl Parser {
    pub fn fact(&self, tb: &mut TokenBlock) -> Result<Fact, ParsingError> {
        match tb.current()? {
            FORALL => self.forall_or_forall_with_iff(tb),
            _ => {
                let or_and_spec_fact = self.or_and_spec_fact(tb)?;
                Ok(or_and_spec_fact.to_fact())
            }
        }
    }

    // fact_hierarchy 1
    fn forall_or_forall_with_iff(&self, tb: &mut TokenBlock) -> Result<Fact, ParsingError> {
        tb.skip_token(FORALL)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != COLON {
            param_def.push(self.param_def_with_param_type(tb)?);
        } 
        tb.skip_token(COLON)?;

        let last_body = tb.body.last().ok_or_else(|| {
            ParsingError::new("Expected body", tb.line_file_index)
        })?;
        if last_body.current()? == EQUIVALENT_SIGN {
            self.forall_with_iff(tb, param_def)
        } else {
            self.forall(tb, param_def)
        }
    }

    fn forall_with_iff(&self, tb: &mut TokenBlock, param_def: Vec<ParamDefWithParamType>) -> Result<Fact, ParsingError> {
        if tb.body.len() < 2 {
            return Err(ParsingError::new("Expected at least 2 body blocks", tb.line_file_index));
        }
        
        let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        let mut iff_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();

        let last = tb.body.last_mut().unwrap();
        last.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
        for block in last.body.iter_mut() {
            iff_facts.push(self.parse_fact_in_forall(block)?);
        }

        let n = tb.body.len();
        let has_right_arrow = tb.body.get(n - 2).unwrap().current()? == RIGHT_ARROW;
        if has_right_arrow {
            let then_block = tb.body.get_mut(n - 2).unwrap();
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for block in then_block.body.iter_mut() {
                then_facts.push(self.parse_fact_in_forall(block)?);
            }
            
            for block in tb.body.iter_mut().take(n - 2) {
                dom_facts.push(self.parse_fact_in_forall(block)?);
            }
        } else {
            let then_block = tb.body.get_mut(0).unwrap();
            for block in then_block.body.iter_mut() {
                then_facts.push(self.parse_fact_in_forall(block)?);
            }
        }

        let forall_fact = ForallFact::new(param_def, dom_facts, then_facts, Some(tb.line_file_index));
        
        Ok(Fact::ForallFactWithIff(ForallFactWithIff::new(forall_fact, iff_facts, Some(tb.line_file_index))))
    }

    fn forall(&self, tb: &mut TokenBlock, param_def: Vec<ParamDefWithParamType>) -> Result<Fact, ParsingError> {
        let last_body = tb.body.last().ok_or_else(|| {
            ParsingError::new("Expected body", tb.line_file_index)
        })?;
        if last_body.current()? == RIGHT_ARROW {
            let mut dom_facts: Vec<ExistOrAndChainAtomicFact> = vec![];
            let n = tb.body.len();
            for block in tb.body.iter_mut().take(n - 1) {
                dom_facts.push(self.parse_fact_in_forall(block)?);
            }
            let last = tb.body.last_mut().unwrap();
            last.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in last.body.iter_mut() {
                then_facts.push(self.parse_fact_in_forall(block)?);
            }
            Ok(Fact::ForallFact(ForallFact::new(param_def, dom_facts, then_facts, Some(tb.line_file_index))))
        } else {
            let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
            for block in tb.body.iter_mut() {
                then_facts.push(self.parse_fact_in_forall(block)?);
            }
            Ok(Fact::ForallFact(ForallFact::new(param_def, vec![], then_facts, Some(tb.line_file_index))))
        }
    }


    // hierarchy 2: or 并列
    pub fn or_and_spec_fact(&self, tb: &mut TokenBlock) -> Result<OrFactOrAndFactOrSpecFact, ParsingError> {
        let mut facts = vec![self.and_spec_fact(tb)?];
        while !tb.exceed_end_of_head() && tb.current()? == OR {
            tb.skip()?;
            facts.push(self.and_spec_fact(tb)?);
        }
        if facts.len() == 1 {
            let one = facts.into_iter().next().unwrap();
            Ok(match one {
                AndFactOrChainFactOrAtomicFact::AndFact(a) => OrFactOrAndFactOrSpecFact::AndFact(a),
                AndFactOrChainFactOrAtomicFact::AtomicFact(a) => OrFactOrAndFactOrSpecFact::AtomicFact(a),
                _ => return Err(ParsingError::new("Expected atomic fact", tb.line_file_index)),
            })
        } else {
            Ok(OrFactOrAndFactOrSpecFact::OrFact(OrFact::new(facts, Some(tb.line_file_index))))
        }
    }

    // hierarchy 3: and 并列
    pub fn and_spec_fact(&self, tb: &mut TokenBlock) -> Result<AndFactOrChainFactOrAtomicFact, ParsingError> {
        _ = tb;
        panic!("and_spec_fact is not implemented");
    }

    pub fn exist_fact(&self, tb: &mut TokenBlock, is_true: bool) -> Result<ExistFact, ParsingError> {
        tb.skip_token(EXIST)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != ST {
            param_def.push(self.param_def_with_param_type(tb)?);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(ST)?;

        let facts = self.parse_facts_inside_exist_fact(tb)?;

        let line = Some(tb.line_file_index);
        if is_true {
            Ok(ExistFact::TrueExistFact(TrueExistFact::new(param_def, facts, line)))
        } else {
            Ok(ExistFact::NotExistFact(NotExistFact::new(param_def, facts, line)))
        }
    }

    /// 解析一个 and_spec_fact 并转为 MatchableFactWithAtomicFactInside（用于 set builder / fn set with dom 等）。
    pub fn parse_matchable_fact_with_atomic_fact_inside(&self, tb: &mut TokenBlock) -> Result<AndFactOrChainFactOrAtomicFact, ParsingError> {
        _ = tb;
        panic!("parse_matchable_fact_with_atomic_fact_inside is not implemented");
    }

    pub fn parse_facts_in_body(&self, tb: &mut TokenBlock) -> Result<Vec<Fact>, ParsingError> 
    {
        let mut facts: Vec<Fact> = vec![];
        for block in tb.body.iter_mut() {
            facts.push(self.fact(block)?);
        }
        Ok(facts)
    }

    pub fn parse_facts_inside_exist_fact(&self, tb: &mut TokenBlock) -> Result<Vec<FactInsideExistFact>, ParsingError> {
        _ = tb;
        panic!("parse_facts_inside_exist_fact is not implemented");
    }

    pub fn parse_fact_in_forall(&self, tb: &mut TokenBlock) -> Result<ExistOrAndChainAtomicFact, ParsingError> {
        _ = tb;
        panic!("parse_fact_in_forall is not implemented");
    }
}
