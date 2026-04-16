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
        Ok(ByFnStmt::new(function, tb.line_file.clone()).into())
    }

    pub fn parse_by_fn_set_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let func = self.parse_obj(tb)?;
        tb.skip_token(FACT_PREFIX)?;
        tb.skip_token(IN)?;
        tb.skip_token(FN_LOWER_CASE)?;
        let fn_set = self.parse_fn_set(tb)?;
        Ok(ByFnSetStmt::new(func, fn_set, tb.line_file.clone()).into())
    }

    /// `by tuple: <obj>` — tuple / ordered-pair definitional expansion.
    pub fn parse_by_tuple_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TUPLE)?;
        tb.skip_token(COLON)?;
        let obj = self.parse_obj(tb)?;
        Ok(ByTupleStmt::new(obj, tb.line_file.clone()).into())
    }

    /// `by finite_seq: finite_seq(S, n)` — expand to the corresponding `fn` set.
    pub fn parse_by_finite_seq_set_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FINITE_SEQ)?;
        tb.skip_token(COLON)?;
        let obj = self.parse_obj(tb)?;
        let line_file = tb.line_file.clone();
        match obj {
            Obj::FiniteSeqSet(fs) => Ok(ByFiniteSeqSetStmt::new(fs, line_file).into()),
            _ => Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "by finite_seq: expected a finite_seq(...) object, got `{}`",
                    obj
                ),
                line_file,
                None,
                vec![],
            )))),
        }
    }

    /// `by matrix: matrix(S, r, c)` — expand to the corresponding `fn` set.
    pub fn parse_by_matrix_set_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(MATRIX)?;
        tb.skip_token(COLON)?;
        let obj = self.parse_obj(tb)?;
        let line_file = tb.line_file.clone();
        match obj {
            Obj::MatrixSet(ms) => Ok(ByMatrixSetStmt::new(ms, line_file).into()),
            _ => Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "by matrix: expected a matrix(...) object, got `{}`",
                    obj
                ),
                line_file,
                None,
                vec![],
            )))),
        }
    }
}
