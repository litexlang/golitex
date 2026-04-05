use crate::prelude::*;

impl Runtime {
    pub fn parse_by_fn_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FN_FOR_FN_WITH_PARAMS)?;
        tb.skip_token(COLON)?;
        let function = self.parse_obj(tb)?;
        Ok(Stmt::ByFnStmt(ByFnStmt::new(
            function,
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
