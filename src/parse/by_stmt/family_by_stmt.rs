use crate::prelude::*;

impl Runtime {
    pub fn parse_by_family_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FAMILY)?;
        tb.skip_token(AS)?;
        tb.skip_token(SET)?;
        tb.skip_token(COLON)?;
        let family_obj = self.parse_obj(tb)?;
        Ok(ByFamilyAsSetStmt::new(family_obj, tb.line_file.clone()).into())
    }
}
