//! Statements that explicitly choose a verifier operation.
//!
//! This includes both `by …` selection forms and `release thm` /
//! `release struct def`.
mod axiom_of_choice;
mod cases;
mod contra;
mod definition;
mod enumerate;
mod extension;
mod finite_set_induc;
mod for_stmt;
mod induc;
mod range;
mod reflexive_prop;
mod regularity_axiom;
mod struct_release;
mod symmetric_prop;
mod theorem_release;
mod theorem_selection;
mod transitive_prop;
mod zorn_lemma;
pub use axiom_of_choice::ByAxiomOfChoiceStmt;
pub use cases::ByCasesStmt;
pub use contra::ByContraStmt;
pub use definition::ByDefStmt;
pub use enumerate::ByEnumerateFiniteSetStmt;
pub use extension::ByExtensionStmt;
pub use finite_set_induc::ByFiniteSetInducStmt;
pub use for_stmt::{ByForExpansion, ByForStmt, ClosedRangeOrRange};
pub use induc::ByInducStmt;
pub use range::{ByClosedRangeAsCasesStmt, ByEnumerateRangeStmt};
pub use reflexive_prop::ByReflexivePropStmt;
pub use regularity_axiom::ByRegularityAxiomStmt;
pub use struct_release::ReleaseStructDefStmt;
pub use symmetric_prop::BySymmetricPropStmt;
pub use theorem_release::ReleaseThmStmt;
pub use theorem_selection::ByThmStmt;
pub use transitive_prop::ByTransitivePropStmt;
pub use zorn_lemma::ByZornLemmaStmt;
