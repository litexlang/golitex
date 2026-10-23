//! Parse-only compilation into mathematical LaTeX with localized prose.
mod compile;
mod fact;
mod helper;
mod language;
mod math_display;
mod obj;
mod source;
mod stmt;
#[cfg(test)]
mod tests;

pub use compile::{to_latex_document, to_latex_from_ast};
pub(crate) use fact::parameters as parameters_to_latex;
pub(crate) use math_display::{fact_to_display_latex, predicate_to_display_latex};
pub use source::{to_latex, to_latex_from_file, to_latex_from_repository, to_latex_from_source};
