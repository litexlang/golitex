use crate::keywords::PROP;
use crate::module_manager::ModuleManager;
use crate::token_block::TokenBlock;
use crate::stmt::Stmt;
use crate::errors::StmtError;
use crate::errors::ParsingError;

pub struct Parser<'a> {
    pub ModuleManager: &'a ModuleManager<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(module_manager: &'a ModuleManager<'a>) -> Self {
        Parser { ModuleManager: module_manager }
    }
}

impl<'a> Parser<'a> {
    pub fn stmt(&self, token_block: &TokenBlock) -> Result<Stmt, StmtError> {
        match token_block.current_token() {
            None => Err(StmtError::ParsingError(ParsingError::new("Expected statement"))),
            Some(token) => {
                match token {
                    PROP => panic!("Expected statement"),
                    _ => panic!("Expected statement"),
                }
            }
        }
    }
}