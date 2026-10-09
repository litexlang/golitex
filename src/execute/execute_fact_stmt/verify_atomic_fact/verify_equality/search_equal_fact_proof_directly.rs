use crate::prelude::*;

impl Runtime {
    // Truth only after WD; no recursive proof search or fact publication.
    pub fn search_equal_fact_proof_directly(
        &mut self,
        fact: &EqualFact,
    ) -> Option<EqualFactSearchedProof> {
        if let Some(proof) = self.lookup_known_obj_equality(&fact.left, &fact.right) {
            return Some(proof);
        }
        calculate_closed_equal_fact(fact).map(EqualFactSearchedProof::ByClosedCalculation)
    }
}
