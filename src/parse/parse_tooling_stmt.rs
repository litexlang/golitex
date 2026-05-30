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
            if tb.current_token_is_equal_to(AS) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!(
                            "standard-library imports use the std folder name; write `import {}` without `as`",
                            mod_name
                        ),
                        tb.line_file.clone(),
                    ),
                )));
            }
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "import: unexpected token after standard-library module name".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            Ok(ImportStmt::ImportGlobalModule(ImportGlobalModuleStmt::new(
                mod_name,
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

    pub fn parse_stop_import_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STOP)?;
        tb.skip_token(IMPORT)?;
        let module_name = tb.advance()?;
        is_valid_litex_name(&module_name).map_err(|msg| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, tb.line_file.clone()),
            ))
        })?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "stop import: unexpected token after module name".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(StopImportStmt::new(module_name, tb.line_file.clone()).into())
    }

    pub fn parse_run_file_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(RUN_FILE)?;
        if tb.current_token_is_equal_to(DOUBLE_QUOTE) {
            tb.skip_token(DOUBLE_QUOTE)?;
            let mut path_parts: Vec<String> = vec![];
            while tb.current()? != DOUBLE_QUOTE {
                path_parts.push(tb.advance()?);
            }
            tb.skip_token(DOUBLE_QUOTE)?;
            let file_path = path_parts.join("");
            return Ok(RunFileStmt::new(file_path, tb.line_file.clone()).into());
        }

        Err(RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                "run_file expects a quoted relative or absolute file path; use import <std_module> for std modules".to_string(),
                tb.line_file.clone(),
            ),
        )))
    }
}
