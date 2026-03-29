use crate::prelude::*;
use super::fact_inside_forall::ExistOrAndChainAtomicFact;
use super::forall_fact::ForallFact;
use std::fmt;

#[derive(Clone)]
pub struct ForallFactWithIff {
    pub forall_fact: ForallFact,
    pub iff_facts: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: (usize, usize),
}

impl ForallFactWithIff {
    pub fn new(
        forall_fact: ForallFact,
        iff_facts: Vec<ExistOrAndChainAtomicFact>,
        line_file: (usize, usize),
    ) -> Self {
        ForallFactWithIff {
            forall_fact,
            iff_facts,
            line_file,
        }
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
    pub fn to_two_forall_facts(self) -> (ForallFact, ForallFact) {
        let ForallFact {
            params_def_with_type,
            dom_facts,
            then_facts,
            line_file,
        } = self.forall_fact;
        let iff_facts = self.iff_facts;

        let mut dom_then = dom_facts.clone();
        dom_then.extend(then_facts.clone());
        let forall_then_implies_iff = ForallFact::new(
            params_def_with_type.clone(),
            dom_then,
            iff_facts.clone(),
            line_file,
        );

        let mut dom_iff = dom_facts;
        dom_iff.extend(iff_facts);
        let forall_iff_implies_then =
            ForallFact::new(params_def_with_type, dom_iff, then_facts, line_file);

        (forall_then_implies_iff, forall_iff_implies_then)
    }
}
