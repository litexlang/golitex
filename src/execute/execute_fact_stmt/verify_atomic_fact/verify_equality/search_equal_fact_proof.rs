use crate::prelude::*;

impl Runtime {
    // Truth only: the caller must have established WD for both objects.
    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        use EqualFactSearchedProof as P;
        use VerifyStateLevel::*;

        if let Some(proof) = self.search_equal_fact_proof_directly(fact) {
            return Ok(Some(proof));
        }
        if let Some(child) = state.for_premises(KnownSpecialProperty) {
            if let Some(proof) = self.search_equal_fact_proof_by_known_special_property(fact)? {
                return Ok(Some(P::ByKnownSpecialProperty(proof)));
            }
            if let Some(proof) =
                self.search_equal_fact_proof_by_matching_one_arg_by_one(fact, child)?
            {
                return Ok(Some(P::ByMatchingOneArgByOne(proof)));
            }
        }
        if let Some(child) = state.for_premises(BuiltinRule) {
            if let Some(proof) = self.search_equal_fact_builtin_rule(fact, child)? {
                return Ok(Some(P::ByBuiltinRule(proof)));
            }
        }
        if let Some(child) = state.for_premises(Strategy) {
            if let Some(proof) = self.verify_by_strategy_equal(fact, child)? {
                return Ok(Some(proof));
            }
            if let Some(proof) = self.search_equal_fact_proof_by_equivalence_class(fact, child)? {
                return Ok(Some(P::ByEquivalenceClass(proof)));
            }
        }
        if let Some(child) = state.for_premises(DefinitionAndForall) {
            if let Some(proof) = self.search_equal_fact_proof_by_object_definition(fact, child)? {
                return Ok(Some(P::ByObjectDefinition(proof)));
            }
            if let Some(proof) = self.search_equal_fact_proof_by_known_forall_fact(fact, child)? {
                return Ok(Some(proof));
            }
        }
        if let Some(child) = state.after_rewrite() {
            if let Some(proof) = self.search_equal_fact_proof_by_builtin_rewrite(fact, child)? {
                return Ok(Some(P::ByBuiltinRewrite(proof)));
            }
        }
        Ok(None)
    }
}
