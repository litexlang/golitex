use crate::prelude::*;

impl Runtime {
    pub fn parse_by_closed_range_as_cases_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLOSED_RANGE)?;
        tb.skip_token(AS)?;
        tb.skip_token(CASES)?;
        tb.skip_token(COLON)?;

        let element = self.parse_obj(tb)?;
        tb.skip_token(FACT_PREFIX)?;
        tb.skip_token(IN)?;
        let range_obj = self.parse_obj(tb)?;
        let closed_range = match range_obj {
            Obj::ClosedRange(cr) => cr,
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file("by closed_range as cases: expected closed_range(lo, hi) or lo ... hi after `$in`"
                        .to_string(), tb.line_file.clone()))));
            }
        };

        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by closed_range as cases: expected end of line after membership fact"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByClosedRangeAsCasesStmt::new(element, closed_range, tb.line_file.clone()).into())
    }
}
