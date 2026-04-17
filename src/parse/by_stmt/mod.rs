//! Parsing for `by …` statements (one file per keyword).
use crate::prelude::*;

mod cases_by_stmt;
mod closed_range_by_stmt;
mod contra_by_stmt;
mod enumerate_by_stmt;
mod extension_by_stmt;
mod family_by_stmt;
mod fn_tuple_by_stmt;
mod for_by_stmt;
mod induc_by_stmt;
mod struct_by_stmt;

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
            FN_LOWER_CASE => self.parse_by_fn_stmt(tb),
            FAMILY => self.parse_by_family_stmt(tb),
            STRUCT => self.parse_by_struct_stmt(tb),
            TUPLE => self.parse_by_tuple_stmt(tb),
            FINITE_SEQ => self.parse_by_finite_seq_set_stmt(tb),
            SEQ => self.parse_by_seq_set_stmt(tb),
            MATRIX => self.parse_by_matrix_set_stmt(tb),
            _ => Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "by: expected cases, contra, enumerate (or enumerate closed_range), induc, for, extension, fn, fn set, family, finite_seq, seq, matrix, struct, or tuple after `by`, got `{}`",
                    second_keyword
                ),
                tb.line_file.clone(),
                None,
                vec![],
            )))),
        }
    }
}
