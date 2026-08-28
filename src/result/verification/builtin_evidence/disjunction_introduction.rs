//! Disjunction-introduction builtin evidence.

use crate::prelude::*;
use std::fmt;

/// Exact introduction certificate for one selected branch of an `or` fact.
/// The enclosing result retains exactly one child proving
/// `expected_selected`; `selected_index` fixes its position in
/// `expected_target`.
#[derive(Clone)]
pub struct DisjunctionIntroductionBuiltinRuleEvidence {
    pub expected_target: Fact,
    pub expected_selected: Fact,
    pub selected_index: usize,
}

impl DisjunctionIntroductionBuiltinRuleEvidence {
    pub fn new(expected_target: Fact, expected_selected: Fact, selected_index: usize) -> Self {
        Self {
            expected_target,
            expected_selected,
            selected_index,
        }
    }
}

impl fmt::Debug for DisjunctionIntroductionBuiltinRuleEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("DisjunctionIntroductionBuiltinRuleEvidence")
            .field("expected_target", &self.expected_target.to_string())
            .field("expected_selected", &self.expected_selected.to_string())
            .field("selected_index", &self.selected_index)
            .finish()
    }
}
