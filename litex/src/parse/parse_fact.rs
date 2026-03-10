use crate::fact::AndFactOrSpecFact;
use crate::obj::IdentifierOrIdentifierWithMod;
use crate::fact::AtomicFact;
use crate::fact::{
    AndAtomicFact, ChainAtomicFact, ExistFact, MatchableFactWithAtomicFactInside, FactInsideExistFact,
    NotExistFact, OrAtomicFact, TrueExistFact,
};
use crate::stmt::parameter_type_and_property::ParamDefWithParamType;
use crate::fact::OrFactOrAndFactOrSpecFact;
use crate::fact::ForallFact;
use crate::fact::ForallFactWithIff;
use super::Parser;
use super::TokenBlock;
use crate::error::{NewAtomicFactError, ParsingError};
use crate::fact::Fact;
use crate::fact::{AndFact, AndSpecFacts, ChainFact};
use crate::obj::Identifier;
use crate::common::keywords::{AND, COLON, COMMA, EQUIVALENT_SIGN, EXIST, FACT_PREFIX, FORALL, LEFT_CURLY_BRACE, NOT, OR, RIGHT_ARROW, RIGHT_CURLY_BRACE, ST};
use crate::fact::OrFact;
use crate::fact::SpecFact;
use crate::common::keywords::is_comparison_str;

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
        
        let mut dom_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
        let mut then_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
        let mut iff_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();

        let last = tb.body.last_mut().unwrap();
        last.skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
        for block in last.body.iter_mut() {
            iff_facts.push(self.or_and_spec_fact(block)?);
        }

        let n = tb.body.len();
        let has_right_arrow = tb.body.get(n - 2).unwrap().current()? == RIGHT_ARROW;
        if has_right_arrow {
            let then_block = tb.body.get_mut(n - 2).unwrap();
            then_block.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for block in then_block.body.iter_mut() {
                then_facts.push(self.or_and_spec_fact(block)?);
            }
            
            for block in tb.body.iter_mut().take(n - 2) {
                dom_facts.push(self.or_and_spec_fact(block)?);
            }
        } else {
            let then_block = tb.body.get_mut(0).unwrap();
            for block in then_block.body.iter_mut() {
                then_facts.push(self.or_and_spec_fact(block)?);
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
            let mut dom_facts: Vec<OrFactOrAndFactOrSpecFact> = vec![];
            let n = tb.body.len();
            for block in tb.body.iter_mut().take(n - 1) {
                dom_facts.push(self.or_and_spec_fact(block)?);
            }
            let last = tb.body.last_mut().unwrap();
            last.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            let mut then_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
            for block in last.body.iter_mut() {
                then_facts.push(self.or_and_spec_fact(block)?);
            }
            Ok(Fact::ForallFact(ForallFact::new(param_def, dom_facts, then_facts, Some(tb.line_file_index))))
        } else {
            let mut then_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
            for block in tb.body.iter_mut() {
                then_facts.push(self.or_and_spec_fact(block)?);
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
                AndFactOrSpecFact::AndFact(a) => OrFactOrAndFactOrSpecFact::AndFact(a),
                AndFactOrSpecFact::SpecFact(s) => OrFactOrAndFactOrSpecFact::SpecFact(s),
            })
        } else {
            Ok(OrFactOrAndFactOrSpecFact::OrFact(OrFact::new(facts, Some(tb.line_file_index))))
        }
    }

    // hierarchy 3: and 并列
    pub fn and_spec_fact(&self, tb: &mut TokenBlock) -> Result<AndFactOrSpecFact, ParsingError> {
        _ = tb;
        panic!("and_spec_fact is not implemented");
    }

    /// 返回 AndFactOrSpecFact：要么单个 SpecFact（含 NOT/EXIST/原子），要么链式 AndFact::ChainFact。
    // hierarchy 4
    fn spec_fact_chain_fact(&self, tb: &mut TokenBlock, is_true: bool) -> Result<AndFactOrSpecFact, ParsingError> {
        if tb.current()? == NOT {
            tb.skip()?;
            self.spec_fact_chain_fact(tb, !is_true)
        } else if tb.current()? == EXIST {
            Ok(AndFactOrSpecFact::SpecFact(SpecFact::ExistFact(self.exist_fact(tb, is_true)?)))
        } else {
            self.atomic_or_chain_fact(tb, is_true)
        }
    }

    fn atomic_or_chain_fact(&self, tb: &mut TokenBlock, is_true: bool) -> Result<AndFactOrSpecFact, ParsingError> {
        if tb.current()? == FACT_PREFIX {
            tb.skip()?;
            let prop_name = self.atom(tb)?.to_identifier_or_identifier_with_mod();
            let args = self.braced_objs(tb)?;
            let line = Some(tb.line_file_index);
            let atomic = AtomicFact::to_atomic_fact(prop_name, is_true, args, line)
                .map_err(|e: NewAtomicFactError| ParsingError::new(&e.msg, tb.line_file_index))?;
            Ok(AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(atomic)))
        } else {
            let left_most_obj = self.obj(tb)?;
            let mut objs = vec![left_most_obj];
            let mut prop_names: Vec<IdentifierOrIdentifierWithMod> = vec![];

            while !tb.exceed_end_of_head() && (is_comparison_str(tb.current()?) || tb.current()? == FACT_PREFIX) {
                let tok = tb.current()?.to_string();
                if is_comparison_str(&tok) {
                    tb.skip()?;
                    prop_names.push(IdentifierOrIdentifierWithMod::Identifier(Identifier::new(&tok)));
                    objs.push(self.obj(tb)?);
                } else if tok == FACT_PREFIX {
                    tb.skip_token(FACT_PREFIX)?;
                    prop_names.push(self.identifier_or_identifier_with_mod(tb)?);
                    objs.push(self.obj(tb)?);
                } else {
                    break;
                }
            }

            if prop_names.is_empty() {
                return Err(ParsingError::new("Expected operator or $prop after object in chain", tb.line_file_index));
            }
            if prop_names.len() == 1 {
                let prop_name = prop_names.into_iter().next().unwrap();
                let line = Some(tb.line_file_index);
                let atomic = AtomicFact::to_atomic_fact(prop_name, is_true, objs, line)
                    .map_err(|e: NewAtomicFactError| ParsingError::new(&e.msg, tb.line_file_index))?;
                return Ok(AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(atomic)));
            }
            if !is_true {
                return Err(ParsingError::new("chain fact cannot be negated", tb.line_file_index));
            }
            Ok(AndFactOrSpecFact::AndFact(AndFact::ChainFact(ChainFact::new(objs, prop_names, Some(tb.line_file_index)))))
        }
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

    /// 将解析得到的 OrFactOrAndFactOrSpecFact 转为 FactInsideExistFact，并校验 exist 体内只允许 atomic / and-of-atomics / chain / or-of-these。
    fn try_convert_or_and_spec_fact_to_fact_inside_exist(
        &self,
        o: OrFactOrAndFactOrSpecFact,
        line_file_index: (usize, usize),
    ) -> Result<FactInsideExistFact, ParsingError> {
        panic!("try_convert_or_and_spec_fact_to_fact_inside_exist is not implemented");
    }

    fn try_convert_and_spec_fact_to_fact_inside_exist_fact(
        &self,
        a: AndFactOrSpecFact,
        line_file_index: (usize, usize),
    ) -> Result<MatchableFactWithAtomicFactInside, ParsingError> {
        panic!("try_convert_and_spec_fact_to_fact_inside_exist_fact is not implemented");
    }

    /// 解析一个 and_spec_fact 并转为 MatchableFactWithAtomicFactInside（用于 set builder / fn set with dom 等）。
    pub fn parse_matchable_fact_with_atomic_fact_inside(&self, tb: &mut TokenBlock) -> Result<MatchableFactWithAtomicFactInside, ParsingError> {
        let and_spec = self.and_spec_fact(tb)?;
        self.try_convert_and_spec_fact_to_fact_inside_exist_fact(and_spec, tb.line_file_index)
    }

    pub fn parse_facts_in_body(&self, tb: &mut TokenBlock) -> Result<Vec<Fact>, ParsingError> 
    {
        let mut facts: Vec<Fact> = vec![];
        for block in tb.body.iter_mut() {
            facts.push(self.fact(block)?);
        }
        Ok(facts)
    }

    /// 先按普通 or_and_spec_fact 解析得到多个 OrFactOrAndFactOrSpecFact，再校验并转为 FactInsideExistFact（exist 体内只允许 atomic / and-of-atomics / chain / or）。
    pub fn parse_facts_inside_exist_fact(&self, tb: &mut TokenBlock) -> Result<Vec<FactInsideExistFact>, ParsingError> {
        let raw = if tb.current()? == LEFT_CURLY_BRACE {
            tb.skip_token(LEFT_CURLY_BRACE)?;
            let mut list = vec![self.or_and_spec_fact(tb)?];
            while tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
                list.push(self.or_and_spec_fact(tb)?);
            }
            tb.skip_token(RIGHT_CURLY_BRACE)?;
            list
        } else {
            return Err(ParsingError::new("Expected { after exist", tb.line_file_index));
        };
        let line_file = tb.line_file_index;
        raw.into_iter()
            .map(|o| self.try_convert_or_and_spec_fact_to_fact_inside_exist(o, line_file))
            .collect()
    }
}
