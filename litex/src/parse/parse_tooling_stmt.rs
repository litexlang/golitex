use crate::keywords::{DOUBLE_QUOTE, IMPORT, AS, CLEAR, DO_NOTHING, RUN_FILE};
use crate::stmt::tooling_stmt::{ClearStmt, DoNothingStmt, RunFileStmt};
use super::Parser;
use super::TokenBlock;
use crate::errors::ParsingError;
use crate::stmt::Stmt;
use crate::stmt::tooling_stmt::{ToolingStmt, ImportStmt, ImportRelativePathStmt, ImportGlobalModuleStmt};

impl Parser {
    pub fn import_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(IMPORT)?;
        if tb.current()? == DOUBLE_QUOTE {
            tb.skip_token(DOUBLE_QUOTE)?;
            let mut path_parts: Vec<String> = vec![];
            while tb.current()? != DOUBLE_QUOTE {
                path_parts.push(tb.advance()?);
            }
            tb.skip_token(DOUBLE_QUOTE)?;
            let path = path_parts.join("");
            let as_mod_name = if tb.current().map(|t| t == AS).unwrap_or(false) {
                tb.skip_token(AS)?;
                Some(tb.advance()?)
            } else {
                None
            };
            Ok(Stmt::ToolingStmt(ToolingStmt::Import(ImportStmt::ImportRelativePath(
                ImportRelativePathStmt {
                    path,
                    as_mod_name,
                    line_file_index: Some(tb.line_file_index),
                },
            ))))
        } else {
            let mod_name = tb.advance()?;
            let as_mod_name = if tb.current().map(|t| t == AS).unwrap_or(false) {
                tb.skip_token(AS)?;
                Some(tb.advance()?)
            } else {
                None
            };
            Ok(Stmt::ToolingStmt(ToolingStmt::Import(ImportStmt::ImportGlobalModule(
                ImportGlobalModuleStmt {
                    mod_name,
                    as_mod_name,
                    line_file_index: Some(tb.line_file_index),
                },
            ))))
        }
    }

    pub fn clear_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CLEAR)?;
        Ok(Stmt::ToolingStmt(ToolingStmt::Clear(ClearStmt {
            line_file_index: Some(tb.line_file_index),
        })))
    }

    pub fn do_nothing_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(DO_NOTHING)?;
        Ok(Stmt::ToolingStmt(ToolingStmt::DoNothing(DoNothingStmt {
            line_file_index: Some(tb.line_file_index),
        })))
    }

    pub fn run_file_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(RUN_FILE)?;
        tb.skip_token(DOUBLE_QUOTE)?;
        let mut path_parts: Vec<String> = vec![];
        while tb.current()? != DOUBLE_QUOTE {
            path_parts.push(tb.advance()?);
        }
        tb.skip_token(DOUBLE_QUOTE)?;
        let file_path = path_parts.join("");
        Ok(Stmt::ToolingStmt(ToolingStmt::RunFile(RunFileStmt {
            file_path,
            line_file_index: Some(tb.line_file_index),
        })))
    }
}