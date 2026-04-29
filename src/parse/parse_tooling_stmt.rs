use crate::prelude::*;

impl Runtime {
    pub fn parse_import_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(IMPORT)?;
        if tb.current_token_is_equal_to(DOUBLE_QUOTE) {
            tb.skip_token(DOUBLE_QUOTE)?;
            let mut path_parts: Vec<String> = vec![];
            while tb.current()? != DOUBLE_QUOTE {
                path_parts.push(tb.advance()?);
            }
            tb.skip_token(DOUBLE_QUOTE)?;
            let path = path_parts.join("");
            let as_mod_name = if tb.current_token_is_equal_to(AS) {
                tb.skip_token(AS)?;
                Some(tb.advance()?)
            } else {
                None
            };
            Ok(ImportStmt::ImportRelativePath(ImportRelativePathStmt::new(
                path,
                as_mod_name,
                tb.line_file.clone(),
            ))
            .into())
        } else {
            let mod_name = tb.advance()?;
            let as_mod_name = if tb.current_token_is_equal_to(AS) {
                tb.skip_token(AS)?;
                Some(tb.advance()?)
            } else {
                None
            };
            Ok(ImportStmt::ImportGlobalModule(ImportGlobalModuleStmt::new(
                mod_name,
                as_mod_name,
                tb.line_file.clone(),
            ))
            .into())
        }
    }

    pub fn parse_do_nothing_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        if tb.current()? == DOT_DOT_DOT {
            tb.skip_token(DOT_DOT_DOT)?;
        } else {
            tb.skip_token(DO_NOTHING)?;
        }
        Ok(DoNothingStmt::new(tb.line_file.clone()).into())
    }

    pub fn parse_clear_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLEAR)?;
        Ok(ClearStmt::new(tb.line_file.clone()).into())
    }

    pub fn parse_run_file_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(RUN_FILE)?;
        tb.skip_token(DOUBLE_QUOTE)?;
        let mut path_parts: Vec<String> = vec![];
        while tb.current()? != DOUBLE_QUOTE {
            path_parts.push(tb.advance()?);
        }
        tb.skip_token(DOUBLE_QUOTE)?;
        let file_path = path_parts.join("");
        Ok(RunFileStmt::new(file_path, tb.line_file.clone()).into())
    }
}
