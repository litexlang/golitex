use super::calculate_closed_atomic_fact::calculate_closed_atomic_fact;
use super::direct_atomic_fact_search_result::DirectAtomicFactSearchResult;
use super::{AtomicExceptEqualityFactSearchedProof, AtomicFactSearchedProof};
use crate::ast::fact::AtomicFact;
use crate::runtime::Runtime;

impl Runtime {
    // Truth only: the caller owns WD. No state parameter, premises or recursive
    // search. The existing known lookup allocates comparison IDs but stores no facts.
    pub fn search_atomic_fact_proof_by_known_fact_or_closed_calculation(
        &mut self,
        fact: &AtomicFact,
    ) -> DirectAtomicFactSearchResult {
        match fact {
            AtomicFact::EqualFact(f) => {
                if let Some(proof) = self.lookup_known_obj_equality(&f.left, &f.right) {
                    return DirectAtomicFactSearchResult::ByKnownFact(
                        AtomicFactSearchedProof::Equality(proof),
                    );
                }
            }
            f => {
                if let Some(proof) = self.lookup_known_atomic_fact(f) {
                    return DirectAtomicFactSearchResult::ByKnownFact(
                        AtomicFactSearchedProof::AtomicExceptEquality(
                            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof),
                        ),
                    );
                }
            }
        }
        match calculate_closed_atomic_fact(fact) {
            Some(proof) => DirectAtomicFactSearchResult::ByClosedCalculation(proof),
            None => DirectAtomicFactSearchResult::NotFound,
        }
    }
}
