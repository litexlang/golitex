use crate::prelude::*;

impl Runtime {
    pub fn parse_by_fn_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FN_LOWER_CASE)?;
        if tb.current_token_is_equal_to(SET) {
            tb.skip_token(SET)?;
            tb.skip_token(COLON)?;
            return self.parse_by_fn_set_stmt(tb);
        }
        tb.skip_token(COLON)?;
        let function = self.parse_obj(tb)?;
        Ok(Stmt::ByFnStmt(ByFnStmt::new(
            function,
            tb.line_file.clone(),
        )))
    }

    /// `by fn set: <func> $in fn{ ... } <ret>` — membership in a function-set via built-in rules (exec TBD).
    pub fn parse_by_fn_set_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let func = self.parse_obj(tb)?;
        tb.skip_token(FACT_PREFIX)?;
        tb.skip_token(IN)?;
        tb.skip_token(FN_LOWER_CASE)?;
        let fn_set = self.parse_fn_set(tb)?;
        Ok(Stmt::ByFnSetStmt(ByFnSetStmt::new(
            func,
            fn_set,
            tb.line_file.clone(),
        )))
    }

    /// `by tuple: <obj>` — tuple / ordered-pair definitional expansion.
    pub fn parse_by_tuple_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TUPLE)?;
        tb.skip_token(COLON)?;
        let obj = self.parse_obj(tb)?;
        Ok(Stmt::ByTuple(ByTupleStmt::new(obj, tb.line_file.clone())))
    }
}
