//! Parsing for `by …` statements (one file per keyword).
use crate::prelude::*;

mod antisymmetric_prop_by_stmt;
mod axiom_of_choice_by_stmt;
mod cases_by_stmt;
mod closed_range_by_stmt;
mod contra_by_stmt;
mod enumerate_by_stmt;
mod extension_by_stmt;
mod for_by_stmt;
mod induc_by_stmt;
mod reflexive_prop_by_stmt;
mod regularity_axiom_by_stmt;
mod symmetric_prop_by_stmt;
mod thm_by_stmt;
mod transitive_prop_by_stmt;
mod zorn_lemma_by_stmt;

impl Runtime {
    pub fn parse_by_prefixed_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(BY)?;
        let second_keyword = tb.current()?;
        match second_keyword {
            CASES => self.parse_by_cases_stmt(tb),
            CONTRA => self.parse_by_contra_stmt(tb),
            ENUMERATE => self.parse_by_enumerate_stmt(tb),
            INDUC => self.parse_by_induc_stmt(tb),
            STRONG_INDUC => self.parse_strong_induc_stmt(tb),
            FOR => self.parse_by_for_stmt(tb),
            EXTENSION => self.parse_by_extension_stmt(tb),
            TRANSITIVE_PROP => self.parse_by_transitive_prop_stmt(tb),
            SYMMETRIC_PROP => self.parse_by_symmetric_prop_stmt(tb),
            REFLEXIVE_PROP => self.parse_by_reflexive_prop_stmt(tb),
            ANTISYMMETRIC_PROP => self.parse_by_antisymmetric_prop_stmt(tb),
            ZORN_LEMMA => self.parse_by_zorn_lemma_stmt(tb),
            AXIOM_OF_CHOICE => self.parse_by_axiom_of_choice_stmt(tb),
            REGULARITY_AXIOM => self.parse_by_regularity_axiom_stmt(tb),
            THM => self.parse_by_thm_stmt(tb),
            CLOSED_RANGE => self.parse_by_closed_range_as_cases_stmt(tb),
            _ => Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(format!(
                    "by: expected cases, contra, enumerate finite_set/range/closed_range, closed_range as cases, induc, strong_induc, for, extension, transitive_prop, symmetric_prop, reflexive_prop, antisymmetric_prop, zorn_lemma, axiom_of_choice, regularity_axiom, or thm after `by`, got `{}`",
                    second_keyword
                ), tb.line_file.clone())))),
        }
    }
}
