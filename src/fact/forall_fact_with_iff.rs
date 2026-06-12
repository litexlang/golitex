use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ForallFactWithIff {
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: LineFile,
}

impl ForallFactWithIff {
    pub fn new(
        forall_fact: ForallFact,
        iff_facts: Vec<ExistOrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Result<Self, RuntimeError> {
        let forall_fact_with_iff = ForallFactWithIff {
            forall_fact,
            iff_facts,
            line_file,
        };
        check_forall_fact_with_iff_has_no_duplicate_forall_free_parameter(&forall_fact_with_iff)?;
        Ok(forall_fact_with_iff)
    }
}

impl fmt::Display for ForallFactWithIff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}\n{}{}\n{}",
            self.forall_fact,
            to_string_and_add_four_spaces_at_beginning_of_each_line(&EQUIVALENT_SIGN, 1),
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.iff_facts, 2)
        )
    }
}

impl ForallFactWithIff {
    // Split `forall ... <=>:` into two forall facts used to verify both directions:
    // 1. `dom + then` proves `iff`.
    // 2. `dom + iff` proves `then`.
    pub fn to_two_forall_facts(&self) -> Result<(ForallFact, ForallFact), RuntimeError> {
        let f = &self.forall_fact;
        let mut dom_then = f.dom_facts.clone();
        dom_then.extend(
            f.then_facts
                .iter()
                .cloned()
                .map(ExistOrAndChainAtomicFact::to_fact),
        );
        let forall_then_implies_iff = ForallFact::new(
            f.params_def_with_type.clone(),
            dom_then,
            self.iff_facts.clone(),
            self.line_file.clone(),
        )?;

        let mut dom_iff = f.dom_facts.clone();
        dom_iff.extend(
            self.iff_facts
                .iter()
                .cloned()
                .map(ExistOrAndChainAtomicFact::to_fact),
        );
        let forall_iff_implies_then = ForallFact::new(
            f.params_def_with_type.clone(),
            dom_iff,
            f.then_facts.clone(),
            self.line_file.clone(),
        )?;

        Ok((forall_then_implies_iff, forall_iff_implies_then))
    }
}
