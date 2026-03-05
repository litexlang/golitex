use crate::parameter_type_and_property::ParamDefWithParamType;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::forall_fact::ForallFact;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::fact::Fact;
use crate::keywords::{COLON, EQUIVALENT_SIGN, FORALL, RIGHT_ARROW};
use crate::specific_fact::SpecFact;

impl Parser {
    pub fn fact(&self, tb: &mut TokenBlock) -> Result<Fact, ParsingError> {
        match tb.current()? {
            FORALL => self.forall_or_forall_with_iff(tb),
            _ => {
                let or_and_spec_fact = self.or_and_spec_fact(tb)?;
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

    fn forall_or_forall_with_iff(&self, tb: &mut TokenBlock) -> Result<Fact, ParsingError> {
        if tb.head_last_token_is(COLON)? {
            self.multiline_forall_or_forall_with_iff(tb)
        } else {
            self.single_line_forall_or_forall_with_iff(tb)
        }
    }

    fn multiline_forall_or_forall_with_iff(&self, tb: &mut TokenBlock) -> Result<Fact, ParsingError> {
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
            self.multiline_forall_with_iff(tb, param_def)
        } else {
            self.multiline_forall(tb, param_def)
        }
    }

    fn multiline_forall_with_iff(&self, tb: &mut TokenBlock, param_def: Vec<ParamDefWithParamType>) -> Result<Fact, ParsingError> {
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

    fn multiline_forall(&self, tb: &mut TokenBlock, param_def: Vec<ParamDefWithParamType>) -> Result<Fact, ParsingError> {
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

    fn single_line_forall_or_forall_with_iff(&self, tb: &mut TokenBlock) -> Result<Fact, ParsingError> {
        tb.skip_token(FORALL)?;
        panic!("")
    }

    fn or_and_spec_fact(&self, tb: &mut TokenBlock) -> Result<OrFactOrAndFactOrSpecFact, ParsingError> {
        _ = tb;
        panic!("")
    }

    pub fn parse_facts_in_body(&self, tb: &mut TokenBlock) -> Result<Vec<Fact>, ParsingError> 
    {
        let mut facts: Vec<Fact> = vec![];
        for block in tb.body.iter_mut() {
            facts.push(self.fact(block)?);
        }
        Ok(facts)
    }
}
