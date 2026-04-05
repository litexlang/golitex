//! Parsing for `by …` statements (one file per keyword).
use crate::prelude::*;

mod cases_by_stmt;
mod contra_by_stmt;
mod enumerate_by_stmt;
mod extension_by_stmt;
mod fn_tuple_by_stmt;
mod for_by_stmt;
mod induc_by_stmt;

impl Runtime {
    pub fn parse_by_prefixed_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(BY)?;
        let second_keyword = tb.current()?;
        match second_keyword {
            CASES => self.parse_by_cases_stmt(tb),
            CONTRA => self.parse_by_contra_stmt(tb),
            ENUMERATE => self.parse_by_enumerate_stmt(tb),
            INDUC => self.parse_by_induc_stmt(tb),
            FOR => self.parse_by_for_stmt(tb),
            EXTENSION => self.parse_by_extension_stmt(tb),
            FN_FOR_FN_WITH_PARAMS => self.parse_by_fn_stmt(tb),
            TUPLE => self.parse_by_tuple_stmt(tb),
            _ => Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                format!(
                    "by: expected cases, contra, enumerate, induc, for, extension, fn, or tuple after `by`, got `{}`",
                    second_keyword
                ),
                tb.line_file.clone(),
                None,
            )),
        }
    }
}
