use crate::errors::ParsingError;
use crate::fact::Fact;
use crate::know_stmt::KnowStmt;
use crate::keywords::{COLON, COMMA, FORALL, KNOW};
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::parser::Parser;
use crate::specific_fact::SpecFact;
use crate::stmt::Stmt;
use crate::token_block::TokenBlock;

fn or_and_spec_to_fact(o: OrFactOrAndFactOrSpecFact) -> Fact {
    match o {
        OrFactOrAndFactOrSpecFact::OrFact(or_fact) => Fact::OrFact(or_fact),
        OrFactOrAndFactOrSpecFact::AndFact(and_fact) => Fact::AndFact(and_fact),
        OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => match spec_fact {
            SpecFact::AtomicFact(atomic_fact) => Fact::AtomicFact(atomic_fact),
            SpecFact::ExistFact(exist_fact) => Fact::ExistFact(exist_fact),
        },
    }
}

impl Parser {
    pub fn know_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(KNOW)?;
        if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let facts = self.parse_facts_in_body(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(facts, Some(tb.line_file_index))))
        } else if tb.current()? == FORALL {
            let fact = self.fact(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(vec![fact], Some(tb.line_file_index))))
        } else {
            let mut facts: Vec<Fact> = vec![];
            loop {
                let o = self.or_and_spec_fact(tb)?;
                facts.push(or_and_spec_to_fact(o));
                if tb.current()? != COMMA {
                    break;
                }
                tb.skip_token(COMMA)?;
            }
            Ok(Stmt::KnowStmt(KnowStmt::new(facts, Some(tb.line_file_index))))
        }
    }
}
