use crate::prelude::*;

impl Runtime {
    pub fn parse_trust_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TRUST)?;
        if tb.current_token_is_equal_to(IMPORT) {
            let stmt = self.parse_import_stmt(tb)?;
            let Stmt::Command(CommandStmt::ImportStmt(import)) = stmt else {
                unreachable!("import parser should produce an import statement")
            };
            return Ok(TrustImportStmt::new(import).into());
        }
        if tb.current_token_is_equal_to(LOCAL) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "trust local import has been removed; use `trust name = \"path\"` in litex.config [export]"
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
        tb.skip_token(IMPORT)?;
        let mod_name = tb.advance()?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "import: unexpected token after declared root-module name".to_string(),
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

    pub fn parse_do_nothing_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(DO_NOTHING)?;
        Ok(DoNothingStmt::new(tb.line_file.clone()).into())
    }

    pub fn parse_clear_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLEAR)?;
        Ok(ClearStmt::new(tb.line_file.clone()).into())
    }
}
