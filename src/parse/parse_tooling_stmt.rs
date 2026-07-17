use crate::prelude::*;

impl Runtime {
    pub fn parse_trust_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TRUST)?;
        if tb.current_token_is_equal_to(IMPORT) {
            return Err(removed_source_import_error(tb));
        }
        if tb.current_token_is_equal_to(LOCAL) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "trust local import has been removed; use `trust Name = \"path\"` in litex.config [import] for a package"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.current_token_is_equal_to(HAVE) {
            return self.parse_trust_have_stmt(tb);
        }
        self.parse_trust_fact_stmt(tb)
    }

    pub fn parse_import_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        if !self.isolated {
            return Err(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                "source import is only available in an isolated REPL or an isolated .lit file; module files must declare dependencies in litex.config"
                    .to_string(),
                tb.line_file.clone(),
            ))
            .into());
        }

        tb.skip_token(IMPORT)?;
        if tb.current_token_is_equal_to(STD) {
            tb.skip_token(STD)?;
            let name = tb.advance()?;
            if !tb.exceed_end_of_head() {
                return Err(import_parse_error(
                    tb,
                    "import std: expected one standard package name",
                ));
            }
            return Ok(CommandStmt::ImportStmt(ImportStmt::Std(ImportStdStmt::new(
                name,
                tb.line_file.clone(),
            )))
            .into());
        }

        tb.skip_token(DOUBLE_QUOTE)?;
        let mut path_parts = vec![];
        while !tb.exceed_end_of_head() && !tb.current_token_is_equal_to(DOUBLE_QUOTE) {
            path_parts.push(tb.advance()?);
        }
        if path_parts.is_empty() {
            return Err(import_parse_error(
                tb,
                "import: module path cannot be empty",
            ));
        }
        tb.skip_token(DOUBLE_QUOTE)?;
        tb.skip_token(AS)?;
        let alias = tb.advance()?;
        is_valid_litex_name(alias.as_str()).map_err(|message| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(message, tb.line_file.clone()),
            ))
        })?;
        if !tb.exceed_end_of_head() {
            return Err(import_parse_error(
                tb,
                "import: expected a quoted path followed by as and an alias",
            ));
        }
        Ok(
            CommandStmt::ImportStmt(ImportStmt::Module(ImportModuleStmt::new(
                path_parts.join(""),
                alias,
                tb.line_file.clone(),
            )))
            .into(),
        )
    }

    pub fn parse_do_nothing_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(DO_NOTHING)?;
        Ok(DoNothingStmt::new(tb.line_file.clone()).into())
    }

    pub fn parse_clear_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLEAR)?;
        Ok(ClearStmt::new(tb.line_file.clone()).into())
    }
}

fn removed_source_import_error(tb: &TokenBlock) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        "trust import is invalid: import is trusted by default. Use terminal `import` in an isolated REPL, or declare a module dependency in litex.config [import] or [import std]; use `litex -strict` to verify loaded code"
            .to_string(),
        tb.line_file.clone(),
    ))
    .into()
}

fn import_parse_error(tb: &TokenBlock, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        tb.line_file.clone(),
    ))
    .into()
}
