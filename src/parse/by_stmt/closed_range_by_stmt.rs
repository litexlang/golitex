use crate::prelude::*;

impl Runtime {
    /// After `by enumerate`; consumes `closed_range(lo, hi): element`.
    pub fn parse_by_enumerate_closed_range_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        let obj = self.parse_obj(tb)?;
        let closed_range = match obj {
            Obj::ClosedRange(cr) => cr,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("by enumerate closed_range: expected closed_range(lo, hi) or lo ... hi before `:`"
                        .to_string(), tb.line_file.clone()))));
            }
        };

        tb.skip_token(COLON)?;
        let element = self.parse_obj(tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by enumerate closed_range: expected end of line after element".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByEnumerateClosedRangeStmt::new(element, closed_range, tb.line_file.clone()).into())
    }
}
