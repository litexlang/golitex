use crate::keywords::{LEFT_BRACE, PROP, RIGHT_BRACE, SET, NONEMPTY_SET, FINITE_SET};
use crate::token_block::TokenBlock;
use crate::stmt::Stmt;
use crate::errors::ParsingError;
use crate::parameter_type_and_property::{ParamDefWithParamTypeAndProperty, ParameterType, Set, NonemptySet, FiniteSet};
use crate::fact::Fact;
use crate::definition_stmt::DefStmt;
use crate::definition_stmt::DefPropStmt;
use crate::obj::Obj;

impl Parser {
    pub fn parse_stmt(&self, token_block: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        match token_block.current_token() {
            None => Err(ParsingError::new("Expected statement", token_block.line_file_index)),
            Some(token) => {
                match token {
                    PROP => self.parse_def_prop_stmt(token_block),
                    _ => Err(ParsingError::new("Expected statement", token_block.line_file_index)),
                }
            }
        }
    }

    pub fn parse_def_prop_stmt(&self, token_block: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        token_block.skip_token(PROP)?;
        let name = token_block.advance()?;
        let param_def = self.parse_braced_param_def_with_param_type_and_property(token_block)?;
        let facts = self.parse_facts_in_body(token_block)?;

        let line_file_index = Some(token_block.line_file_index);
        let def_prop_stmt = match facts.len() {
            0 => DefPropStmt::new(name, param_def, None, line_file_index),
            _ => DefPropStmt::new(name, param_def, Some(facts), line_file_index),
        };
        Ok(Stmt::DefStmt(DefStmt::DefPropStmt(def_prop_stmt)))
    }
}

impl Parser {
    pub fn parse_braced_param_def_with_param_type_and_property(&self, token_block: &mut TokenBlock) -> Result<Vec<ParamDefWithParamTypeAndProperty>, ParsingError> {
        token_block.skip_token(LEFT_BRACE)?;
        let param_def_with_param_type_and_property = self.parse_param_def_with_param_type_and_property(token_block)?;
        token_block.skip_token(RIGHT_BRACE)?;
        Ok(param_def_with_param_type_and_property)
    }
    
    pub fn parse_param_def_with_param_type_and_property(&self, token_block: &mut TokenBlock) -> Result<Vec<ParamDefWithParamTypeAndProperty>, ParsingError> {
        let mut def: Vec<ParamDefWithParamTypeAndProperty> = Vec::new();
        panic!("Not implemented");
    }

    pub fn parse_param_def_with_property(&self, token_block: &mut TokenBlock) -> Result<ParamDefWithParamTypeAndProperty, ParsingError> {
        panic!("Not implemented");
    }

    pub fn parse_param_type_set(&self, token_block: &mut TokenBlock) -> Result<ParameterType, ParsingError> {
        token_block.skip_token(SET)?;
        Ok(ParameterType::Set(Set::new()))
    }

    pub fn parse_param_type_nonempty_set(&self, token_block: &mut TokenBlock) -> Result<ParameterType, ParsingError> {
        token_block.skip_token(NONEMPTY_SET)?;
        Ok(ParameterType::NonemptySet(NonemptySet::new()))
    }

    pub fn parse_param_type_finite_set(&self, token_block: &mut TokenBlock) -> Result<ParameterType, ParsingError> {
        token_block.skip_token(FINITE_SET)?;
        Ok(ParameterType::FiniteSet(FiniteSet::new()))
    }

    pub fn parse_param_type_obj(&self, token_block: &mut TokenBlock) -> Result<ParameterType, ParsingError> {
        let obj = self.parse_obj(token_block)?;
        Ok(ParameterType::Obj(obj))
    }
}

impl Parser {
    pub fn parse_facts_in_body(&self, token_block: &mut TokenBlock) -> Result<Vec<Fact>, ParsingError> {
        panic!("Not implemented");
    }
}
