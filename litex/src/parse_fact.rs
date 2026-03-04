use crate::parameter_type_and_property::ParamDefWithParamType;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::forall_fact::ForallFact;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::fact::Fact;
use crate::keywords::{COLON, EQUIVALENT_SIGN, FORALL, RIGHT_ARROW, DOM};
use crate::specific_fact::SpecFact;

impl Parser {
    pub fn fact(&self, token_block: &mut TokenBlock) -> Result<Fact, ParsingError> {
        match token_block.current()? {
            FORALL => self.forall_or_forall_with_iff(token_block),
            _ => {
                let or_and_spec_fact = self.or_and_spec_fact(token_block)?;
                match or_and_spec_fact {
                    OrFactOrAndFactOrSpecFact::OrFact(or_fact) => Ok(Fact::OrFact(or_fact)),
                    OrFactOrAndFactOrSpecFact::AndFact(and_fact) => Ok(Fact::AndFact(and_fact)),
                    OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => {
                        match spec_fact {
                            SpecFact::AtomicFact(atomic_fact) => Ok(Fact::AtomicFact(atomic_fact)),
                            SpecFact::ExistFact(exist_fact) => Ok(Fact::ExistFact(exist_fact)),
                        }
                    }
                }
            }
        }
    }

    fn forall_or_forall_with_iff(&self, token_block: &mut TokenBlock) -> Result<Fact, ParsingError> {
        if token_block.head_last_token_is(COLON)? {
            self.multiline_forall_or_forall_with_iff(token_block)
        } else {
            self.single_line_forall_or_forall_with_iff(token_block)
        }
    }

    fn multiline_forall_or_forall_with_iff(&self, token_block: &mut TokenBlock) -> Result<Fact, ParsingError> {
        token_block.skip_token(FORALL)?;
        let mut param_def: Vec<ParamDefWithParamType> = vec![];
        while token_block.current()? != COLON {
            param_def.push(self.param_def_with_param_type(token_block)?);
        } 
        token_block.skip_token(COLON)?;

        let last_body = token_block.body.last().ok_or_else(|| {
            ParsingError::new("Expected body", token_block.line_file_index)
        })?;
        if last_body.current()? == EQUIVALENT_SIGN {
            self.multiline_forall_with_iff(token_block, param_def)
        } else {
            self.multiline_forall(token_block, param_def)
        }
    }

    fn multiline_forall_with_iff(&self, token_block: &mut TokenBlock, param_def: Vec<ParamDefWithParamType>) -> Result<Fact, ParsingError> {
        if token_block.body.len() != 2 || token_block.body.len() != 3 {
            return Err(ParsingError::new("Expected body", token_block.line_file_index));
        }

        let mut then_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
        let mut dom_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
        let mut iff_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();

        token_block.body.last_mut().unwrap().skip_token_and_colon_and_exceed_end_of_head(EQUIVALENT_SIGN)?;
        
        for i in 0..token_block.body.last_mut().unwrap().body.len() {
            iff_facts.push(self.or_and_spec_fact(token_block.body.get_mut(i).unwrap())?);
        }

        if token_block.body.len() == 3 {
            // 第一个 body 块是 dom 块
            token_block.body.get_mut(0).expect("Expected dom block").skip_token_and_colon_and_exceed_end_of_head(DOM)?;
            
            for i in 0..token_block.body.get_mut(0).unwrap().body.len() {
                dom_facts.push(self.or_and_spec_fact(token_block.body.get_mut(i).unwrap())?);
            }

            token_block.body.get_mut(1).unwrap().skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for i in 0..token_block.body.get_mut(1).unwrap().body.len() {
                then_facts.push(self.or_and_spec_fact(token_block.body.get_mut(i).unwrap())?);
            }
        } else {
            token_block.body.get_mut(0).unwrap().skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            for i in 0..token_block.body.len() - 1 {
                then_facts.push(self.or_and_spec_fact(token_block.body.get_mut(i).unwrap())?);
            }
        }

        let forall_fact = ForallFact::new(param_def, dom_facts, then_facts, Some(token_block.line_file_index));
        
        Ok(Fact::ForallFactWithIff(ForallFactWithIff::new(forall_fact, iff_facts, Some(token_block.line_file_index))))
    }

    fn multiline_forall(&self, token_block: &mut TokenBlock, param_def: Vec<ParamDefWithParamType>) -> Result<Fact, ParsingError> {
        let last_body = token_block.body.last().ok_or_else(|| {
            ParsingError::new("Expected body", token_block.line_file_index)
        })?;
        if last_body.current()? == RIGHT_ARROW {
            let mut dom_facts: Vec<OrFactOrAndFactOrSpecFact> = vec![];
            for i in 0..token_block.body.len() - 1 {
                dom_facts.push(self.or_and_spec_fact(token_block.body.get_mut(i).unwrap())?);
            }
            token_block.body.last_mut().unwrap().skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            let mut then_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
            for i in 0..token_block.body.last_mut().unwrap().body.len() {
                then_facts.push(self.or_and_spec_fact(token_block.body.get_mut(i).unwrap())?);
            }
            Ok(Fact::ForallFact(ForallFact::new(param_def, dom_facts, then_facts, Some(token_block.line_file_index))))
        } else {
            let mut then_facts: Vec<OrFactOrAndFactOrSpecFact> = Vec::new();
            for i in 0..token_block.body.len() {
                then_facts.push(self.or_and_spec_fact(token_block.body.get_mut(i).unwrap())?);
            }
            Ok(Fact::ForallFact(ForallFact::new(param_def, vec![], then_facts, Some(token_block.line_file_index))))
        }
    }

    fn single_line_forall_or_forall_with_iff(&self, token_block: &mut TokenBlock) -> Result<Fact, ParsingError> {
        token_block.skip_token(FORALL)?;
        panic!("")
    }

    fn or_and_spec_fact(&self, token_block: &mut TokenBlock) -> Result<OrFactOrAndFactOrSpecFact, ParsingError> {
        _ = token_block;
        panic!("")
    }

    pub fn parse_facts_in_body(&self, token_block: &mut TokenBlock) -> Result<Vec<Fact>, ParsingError> 
    {
        let mut facts: Vec<Fact> = vec![];
        for i in 0..token_block.body.len() {
            let fact = self.fact(token_block.body.get_mut(i).unwrap())?;
            facts.push(fact);
        }
        Ok(facts)
    }
}
