use crate::prelude::*;

impl Runtime {
    // Truth only: the caller must have established WD for the target.
    pub fn search_atomic_except_equality_fact_proof(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        if let Some(proof) = self.search_atomic_except_equality_fact_proof_directly(fact)? {
            return Ok(Some(proof));
        }
        match fact {
            AtomicFact::InFact(member)
                if matches!(&member.set, Obj::InstantiatedTemplateObj(_)) =>
            {
                self.search_in_fact_proof(member, state)
            }
            _ => self.search_atomic_except_equality_fact_proof_by_rules(fact, state),
        }
    }

    // Original rule pipeline; membership conversion is owned by InFact.
    pub(super) fn search_atomic_except_equality_fact_proof_by_rules(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        use AtomicExceptEqualityFactSearchedProof as P;
        use VerifyStateLevel::*;
        if let Some(child) = state.for_premises(KnownSpecialProperty) {
            if let Some(proof) =
                self.search_atomic_except_equality_fact_proof_by_known_atomic_fact(fact, child)?
            {
                return Ok(Some(P::ByKnownAtomicFact(proof)));
            }
            if let Some(proof) = self
                .search_atomic_except_equality_fact_proof_by_known_special_property_at_ceiling(
                    fact, state,
                )
            {
                return Ok(Some(P::ByKnownSpecialProperty(proof)));
            }
        }
        if let Some(child) = state.for_premises(BuiltinRule) {
            if let Some(proof) =
                self.search_atomic_except_equality_fact_proof_by_builtin_rule(fact, child)?
            {
                return Ok(Some(P::ByBuiltinRule(proof)));
            }
        }
        if let Some(child) = state.for_premises(Strategy) {
            if let Some(proof) = self.verify_by_strategy_atomic_except_equality(fact, child)? {
                return Ok(Some(proof));
            }
        }
        if let Some(child) = state.for_premises(DefinitionAndForall) {
            if let Ok(proof) =
                self.search_atomic_except_equality_fact_proof_by_definition(fact, child)?
            {
                return Ok(Some(P::ByDefinition(proof)));
            }
            if let Some(proof) =
                self.search_atomic_except_equality_fact_proof_by_known_forall_fact(fact, child)?
            {
                return Ok(Some(P::ByKnownForallFact(proof)));
            }
        }
        if let Some(child) = state.after_rewrite() {
            if let Some(proof) =
                self.search_atomic_except_equality_fact_proof_by_builtin_rewrite(fact, child)?
            {
                return Ok(Some(P::ByBuiltinRewrite(proof)));
            }
            if let Some(proof) =
                self.search_atomic_except_equality_fact_proof_by_known_rewrite(fact, child)?
            {
                return Ok(Some(P::ByKnownRewrite(proof)));
            }
        }
        Ok(None)
    }
}
