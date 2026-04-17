use crate::prelude::*;

impl Runtime {
    /// After `by enumerate`; consumes `closed_range(lo, hi): element`.
    pub fn parse_by_enumerate_closed_range_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLOSED_RANGE)?;
        let args = self.parse_braced_objs(tb)?;
        if args.len() != 2 {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by enumerate closed_range: expected closed_range(lo, hi) with two endpoints"
                    .to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        let mut args = args.into_iter();
        let left = args.next().unwrap();
        let right = args.next().unwrap();
        let closed_range = ClosedRange::new(left, right);
        tb.skip_token(COLON)?;
        let element = self.parse_obj(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by enumerate closed_range: expected end of line after element".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        Ok(ByEnumerateClosedRangeStmt::new(element, closed_range, tb.line_file.clone()).into())
    }
}
