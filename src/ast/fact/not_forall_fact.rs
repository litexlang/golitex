use super::QuantifierFreeFact;
use super::super::line_file::SourceLine;
use super::super::param::TypedParameterList;
use crate::runtime::FactId;

// Negated universal: counterexample dual of an exist body.
//
// Dom/then are QuantifierFreeFact only (atomic / and / chain / or) — the same
// shapes that may appear inside `exist … st {…}`. Nested exist/forall are
// rejected at parse so De Morgan → exist does not need UnsupportedBodyShape
// for quantifier nesting.
//
// Example:
//   not forall x R:
//       x > 0
// is the claim that `exist x R st {not x > 0}` holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotForallFact {
    pub fact_id: FactId,
    pub typed_parameters: TypedParameterList,
    pub dom_facts: Vec<QuantifierFreeFact>,
    pub then_facts: Vec<QuantifierFreeFact>,
    pub line_file: Option<SourceLine>,
}
