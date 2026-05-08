use crate::prelude::*;

impl Runtime {
    pub fn parse_by_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FN_LOWER_CASE)?;
        if tb.current_token_is_equal_to(SET) {
            tb.skip_token(SET)?;
            tb.skip_token(AS)?;
            tb.skip_token(SET)?;
            tb.skip_token(COLON)?;
            return self.parse_by_fn_set_stmt(tb);
        }
        tb.skip_token(AS)?;
        tb.skip_token(SET)?;
        tb.skip_token(COLON)?;
        let function = self.parse_obj(tb)?;
        Ok(ByFnAsSetStmt::new(function, tb.line_file.clone()).into())
    }

    pub fn parse_by_fn_set_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let func = self.parse_obj(tb)?;
        tb.skip_token(FACT_PREFIX)?;
        tb.skip_token(IN)?;
        tb.skip_token(FN_LOWER_CASE)?;
        let fn_set = self.parse_fn_set(tb)?;
        Ok(ByFnSetAsSetStmt::new(func, fn_set, tb.line_file.clone()).into())
    }

    // `by tuple as set: <obj>` expands the tuple as its set-theoretic encoding.
    pub fn parse_by_tuple_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TUPLE)?;
        tb.skip_token(AS)?;
        tb.skip_token(SET)?;
        tb.skip_token(COLON)?;
        let obj = self.parse_obj(tb)?;
        Ok(ByTupleAsSetStmt::new(obj, tb.line_file.clone()).into())
    }
}
