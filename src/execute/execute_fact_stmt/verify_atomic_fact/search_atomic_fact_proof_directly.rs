use super::calculate_closed_atomic_fact::calculate_closed_atomic_fact;
use super::direct_atomic_fact_search_result::DirectAtomicFactSearchResult;
use super::{AtomicExceptEqualityFactSearchedProof, AtomicFactSearchedProof};
use crate::ast::fact::AtomicFact;
use crate::runtime::Runtime;

impl Runtime {
    // Truth only: the caller owns WD. No state parameter or recursive proof
    // search; structural membership descends only through smaller expressions. The existing known lookup allocates comparison IDs but stores no facts.
    pub fn search_atomic_fact_proof_directly(
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
        if let Some(proof) = calculate_closed_atomic_fact(fact) {
            return DirectAtomicFactSearchResult::ByClosedCalculation(proof);
        }
        if let AtomicFact::InFact(member) = fact {
            if let crate::ast::obj::Obj::StandardSet(set) = &member.set {
                if let Some(proof) = self.search_structural_membership(&member.element, set) {
                    return DirectAtomicFactSearchResult::ByStructuralMembership(proof);
                }
            }
        }
        DirectAtomicFactSearchResult::NotFound
    }
}
