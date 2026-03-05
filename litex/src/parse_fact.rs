use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::atom::Atom;
use crate::atomic_fact::{AtomicFact, NormalAtomicFact, NotNormalAtomicFact};
use crate::exist_fact::{ExistFact, TrueExistFact, NotExistFact};
use crate::parameter_type_and_property::ParamDefWithParamTypeOrProperty;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::forall_fact::ForallFact;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::fact::Fact;
use crate::and_fact::{AndFact, AndSpecFacts, ChainFact};
use crate::atom::AtomWithoutModName;
use crate::keywords::{AND, COLON, COMMA, EQUIVALENT_SIGN, EXIST, FACT_PREFIX, FORALL, LEFT_CURLY_BRACE, NOT, OR, RIGHT_ARROW, RIGHT_CURLY_BRACE, ST};
use crate::or_fact::OrFact;
use crate::specific_fact::SpecFact;
use crate::keywords::is_comparison_str;

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
        let mut param_def: Vec<ParamDefWithParamTypeOrProperty> = vec![];
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

    fn forall_with_iff(&self, tb: &mut TokenBlock, param_def: Vec<ParamDefWithParamTypeOrProperty>) -> Result<Fact, ParsingError> {
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

    fn forall(&self, tb: &mut TokenBlock, param_def: Vec<ParamDefWithParamTypeOrProperty>) -> Result<Fact, ParsingError> {
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
        let mut facts = vec![self.spec_fact_chain_fact(tb, true)?];
        while !tb.exceed_end_of_head() && tb.current()? == AND {
            tb.skip()?;
            facts.push(self.spec_fact_chain_fact(tb, true)?);
        }
        if facts.len() == 1 {
            Ok(facts.into_iter().next().unwrap())
        } else {
            let spec_facts: Vec<SpecFact> = facts
                .into_iter()
                .map(|f| match f {
                    AndFactOrSpecFact::SpecFact(s) => Ok(s),
                    AndFactOrSpecFact::AndFact(_) => Err(ParsingError::new("and-list cannot mix chain and spec fact", tb.line_file_index)),
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(AndFactOrSpecFact::AndFact(AndFact::AndSpecFacts(AndSpecFacts::new(spec_facts, Some(tb.line_file_index)))))
        }
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
            let prop_name = self.atom(tb)?;
            let args = self.braced_objs(tb)?;
            let line = Some(tb.line_file_index);
            let atomic = if is_true {
                AtomicFact::NormalAtomicFact(NormalAtomicFact::new(prop_name, args, line))
            } else {
                AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(prop_name, args, line))
            };
            Ok(AndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(atomic)))
        } else {
            let left_most_obj = self.obj(tb)?;
            let mut objs = vec![left_most_obj];
            let mut prop_names: Vec<Atom> = vec![];

            while !tb.exceed_end_of_head() && (is_comparison_str(tb.current()?) || tb.current()? != FACT_PREFIX) {
                let tok = tb.current()?.to_string();
                if is_comparison_str(&tok) {
                    tb.skip()?;
                    prop_names.push(Atom::AtomWithoutModName(AtomWithoutModName::new(&tok)));
                    objs.push(self.obj(tb)?);
                } else if tok == FACT_PREFIX {
                    tb.skip_token(FACT_PREFIX)?;
                    prop_names.push(self.atom(tb)?);
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
                let atomic = if is_true {
                    AtomicFact::NormalAtomicFact(NormalAtomicFact::new(prop_name, objs, line))
                } else {
                    AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact::new(prop_name, objs, line))
                };
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
        let mut param_def: Vec<ParamDefWithParamTypeOrProperty> = vec![];
        while tb.current()? != ST {
            param_def.push(self.param_def_with_param_type(tb)?);
            if tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(ST)?;

        let facts = if tb.current()? == LEFT_CURLY_BRACE {
            tb.skip_token(LEFT_CURLY_BRACE)?;
            let mut facts = vec![self.or_and_spec_fact(tb)?];
            while tb.current()? == COMMA {
                tb.skip_token(COMMA)?;
                facts.push(self.or_and_spec_fact(tb)?);
            }
            tb.skip_token(RIGHT_CURLY_BRACE)?;
            facts
        } else {
            vec![self.or_and_spec_fact(tb)?]
        };

        let line = Some(tb.line_file_index);
        if is_true {
            Ok(ExistFact::TrueExistFact(TrueExistFact::new(param_def, facts, line)))
        } else {
            Ok(ExistFact::NotExistFact(NotExistFact::new(param_def, facts, line)))
        }
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
