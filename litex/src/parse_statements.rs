use crate::keywords::{LEFT_BRACE, PROP, RIGHT_BRACE};
use crate::token_block::TokenBlock;
use crate::stmt::Stmt;
use crate::definition_stmt::{DefStmt, DefPropStmt};
use crate::errors::ParsingError;
use crate::fact::Fact;
use crate::parser::Parser;
use crate::parameter_type_and_property::{ParamDefWithParamType};


impl Parser {
    pub fn parse_stmt(&self, token_block: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        match token_block.current()? {
            PROP => self.parse_def_prop_stmt(token_block),
            _ => Err(ParsingError::new("Expected statement", token_block.line_file_index)),
        }
    }

    pub fn parse_def_prop_stmt(&self, token_block: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        token_block.skip_token(PROP)?;
        let name = token_block.advance()?;
        token_block.skip_token(LEFT_BRACE)?;
        let mut param_defs: Vec<ParamDefWithParamType> = vec![];
        while token_block.current()? != RIGHT_BRACE {
            let param_def = self.param_def_with_property(token_block)?;
            param_defs.push(param_def);
        }
        token_block.skip_token(RIGHT_BRACE)?;
        let facts = self.parse_facts_in_body(token_block)?;
        match facts.len() {
            0 => Ok(Stmt::DefStmt(DefStmt::DefPropStmt(DefPropStmt::new(name, param_defs, None, Some(token_block.line_file_index))))),
            _ => Ok(Stmt::DefStmt(DefStmt::DefPropStmt(DefPropStmt::new(name, param_defs, Some(facts), Some(token_block.line_file_index))))),
        }
    }
}

impl Parser {
    pub fn parse_facts_in_body(&self, token_block: &mut TokenBlock) -> Result<Vec<Fact>, ParsingError> {
        panic!("Not implemented");
    }
}
