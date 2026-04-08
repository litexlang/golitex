use crate::prelude::*;

impl Runtime {
    pub fn parse_by_struct_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRUCT)?;
        tb.skip_token(COLON)?;
        let struct_obj = self.parse_obj(tb)?;
        Ok(Stmt::ByStructStmt(ByStructStmt::new(
            struct_obj,
            tb.line_file.clone(),
        )))
    }
}
