use crate::prelude::*;

impl Runtime {
    pub fn parse_by_closed_range_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLOSED_RANGE)?;
        tb.skip_token(COLON)?;
        let element = self.parse_obj(tb)?;
        tb.skip_token(FACT_PREFIX)?;
        tb.skip_token(IN)?;
        let obj = self.parse_obj(tb)?;
        let Obj::ClosedRange(closed_range) = obj else {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "by closed_range: expected `closed_range(...)` after `$in`, got `{}`",
                    obj
                ),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        };
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by closed_range: expected end of line after range".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        Ok(ByClosedRangeStmt::new(element, closed_range, tb.line_file.clone()).into())
    }
}
