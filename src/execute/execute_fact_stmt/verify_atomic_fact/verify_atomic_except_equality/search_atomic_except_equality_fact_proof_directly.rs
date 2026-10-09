use crate::prelude::*;

impl Runtime {
    // Truth only after WD. Structural membership descends through smaller
    // expressions; lookup may allocate comparison IDs but stores no facts.
    pub fn search_atomic_except_equality_fact_proof_directly(
        &mut self,
        fact: &AtomicFact,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        use AtomicExceptEqualityFactSearchedProof as P;

        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Err(RuntimeError::InternalBug(
                "EqualFact truth search must use search_equal_fact_proof".to_string(),
            ));
        }
        if let Some(proof) = self.lookup_known_atomic_fact(fact) {
            return Ok(Some(P::ByKnownAtomicFact(proof)));
        }
        if let Some(proof) = calculate_closed_atomic_except_equality_fact(fact) {
            return Ok(Some(P::ByClosedCalculation(proof)));
        }
        if let AtomicFact::InFact(member) = fact {
            if let Obj::StandardSet(set) = &member.set {
                if let Some(proof) = self.search_structural_membership(&member.element, set) {
                    return Ok(Some(P::ByStructuralMembership(proof)));
                }
            }
        }
        Ok(None)
    }
}
