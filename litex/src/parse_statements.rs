use crate::keywords::{LEFT_BRACE, PROP, RIGHT_BRACE};
use crate::token_block::TokenBlock;
use crate::stmt::Stmt;
use crate::definition_stmt::{DefStmt, DefPropStmt};
use crate::errors::ParsingError;
use crate::parser::Parser;
use crate::parameter_type_and_property::{ParamDefWithParamType};


impl Parser {
    pub fn stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        match tb.current()? {
            PROP => self.def_prop_stmt(tb),
            _ => {
                let fact = self.fact(tb)?;
                Ok(Stmt::Fact(fact))
            }
        }
    }

    pub fn def_prop_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(PROP)?;
        let name = tb.advance()?;
        tb.skip_token(LEFT_BRACE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        while tb.current()? != RIGHT_BRACE {
            let param_def = self.param_def_with_property(tb)?;
            param_defs.push(param_def);
        }
        tb.skip_token(RIGHT_BRACE)?;
        let facts = self.parse_facts_in_body(tb)?;
        match facts.len() {
            0 => Ok(Stmt::DefStmt(DefStmt::DefPropStmt(DefPropStmt::new(name, param_defs, None, Some(tb.line_file_index))))),
            _ => Ok(Stmt::DefStmt(DefStmt::DefPropStmt(DefPropStmt::new(name, param_defs, Some(facts), Some(tb.line_file_index))))),
        }
    }
}