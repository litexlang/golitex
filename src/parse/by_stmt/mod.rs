//! Parsing for `by …` statements (one file per keyword).
use crate::prelude::*;

mod cases_by_stmt;
mod closed_range_by_stmt;
mod commutative_prop_by_stmt;
mod contra_by_stmt;
mod enumerate_by_stmt;
mod extension_by_stmt;
mod family_by_stmt;
mod fn_tuple_by_stmt;
mod for_by_stmt;
mod induc_by_stmt;
mod struct_by_stmt;
mod transitive_prop_by_stmt;

impl Runtime {
    pub fn parse_by_prefixed_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(BY)?;
        let second_keyword = tb.current()?;
        match second_keyword {
            CASES => self.parse_by_cases_stmt(tb),
            CONTRA => self.parse_by_contra_stmt(tb),
            ENUMERATE => self.parse_by_enumerate_stmt(tb),
            INDUC => self.parse_by_induc_stmt(tb),
            FOR => self.parse_by_for_stmt(tb),
            EXTENSION => self.parse_by_extension_stmt(tb),
            TRANSITIVE_PROP => self.parse_by_transitive_prop_stmt(tb),
            COMMUTATIVE_PROP => self.parse_by_commutative_prop_stmt(tb),
            CLOSED_RANGE => self.parse_by_closed_range_as_cases_stmt(tb),
            FN_LOWER_CASE => self.parse_by_fn_stmt(tb),
            FAMILY => self.parse_by_family_stmt(tb),
            TUPLE => self.parse_by_tuple_stmt(tb),
            STRUCT => self.parse_by_struct_stmt(tb),
            _ => Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(format!(
                    "by: expected cases, contra, enumerate finite_set, closed_range as cases, induc, for, extension, transitive_prop, commutative_prop, fn as set, fn set as set, family as set, tuple as set, or struct after `by`, got `{}`",
                    second_keyword
                ), tb.line_file.clone())))),
        }
    }
}
