use super::closed_calculation_proof::ClosedCalculationProof;
use super::direct_atomic_fact_search_result::DirectAtomicFactSearchResult;
// One permission schedule for both atomic families. Rule entries receive an
// already restricted premise state; family dispatch never resets permissions.
use super::{AtomicExceptEqualityFactSearchedProof, EqualFactSearchedProof};
use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::runtime::{Runtime, RuntimeResult};

pub enum AtomicFactSearchedProof {
    Equality(EqualFactSearchedProof),
    AtomicExceptEquality(AtomicExceptEqualityFactSearchedProof),
}

impl Runtime {
    // Truth only: the caller must have established WD for the target.
    pub fn search_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicFactSearchedProof>> {
        use AtomicExceptEqualityFactSearchedProof as AP;
        use AtomicFactSearchedProof::{AtomicExceptEquality as A, Equality as E};
        use EqualFactSearchedProof as EP;
        use VerifyStateLevel::*;

        match self.search_atomic_fact_proof_directly(fact) {
            DirectAtomicFactSearchResult::ByKnownFact(proof) => return Ok(Some(proof)),
            DirectAtomicFactSearchResult::ByClosedCalculation(proof) => {
                return Ok(Some(match proof {
                    ClosedCalculationProof::Equality(p) => E(EP::ByClosedCalculation(p)),
                    ClosedCalculationProof::AtomicExceptEquality(p) => A(AP::ByClosedCalculation(p)),
                }));
            }
            DirectAtomicFactSearchResult::ByStructuralMembership(proof) => {
                return Ok(Some(A(AP::ByStructuralMembership(proof))));
            }
            DirectAtomicFactSearchResult::NotFound => {}
        }
        if let Some(child) = state.for_premises(KnownSpecialProperty) {
            match fact {
                AtomicFact::EqualFact(f) => {
                    if let Some(p) = self.search_equal_fact_proof_by_known_special_property(f)? {
                        return Ok(Some(E(EP::ByKnownSpecialProperty(p))));
                    }
                    if let Some(p) =
                        self.search_equal_fact_proof_by_matching_one_arg_by_one(f, child)?
                    {
                        return Ok(Some(E(EP::ByMatchingOneArgByOne(p))));
                    }
                }
                f => {
                    if let Some(p) = self
                        .search_atomic_except_equality_fact_proof_by_known_atomic_fact(f, child)?
                    {
                        return Ok(Some(A(AP::ByKnownAtomicFact(p))));
                    }
                    if let Some(p) =
                        self.search_atomic_except_equality_fact_proof_by_known_special_property(f)
                    {
                        return Ok(Some(A(AP::ByKnownSpecialProperty(p))));
                    }
                }
            }
        }
        if let Some(child) = state.for_premises(BuiltinRule) {
            match fact {
                AtomicFact::EqualFact(f) => {
                    if let Some(p) = self.search_equal_fact_builtin_rule(f, child)? {
                        return Ok(Some(E(EP::ByBuiltinRule(p))));
                    }
                }
                f => {
                    if let Some(p) =
                        self.search_atomic_except_equality_fact_proof_by_builtin_rule(f, child)?
                    {
                        return Ok(Some(A(AP::ByBuiltinRule(p))));
                    }
                }
            }
        }
        if let Some(child) = state.for_premises(Strategy) {
            match fact {
                AtomicFact::EqualFact(f) => {
                    if let Some(p) = self.verify_by_strategy_equal(f, child)? {
                        return Ok(Some(E(p)));
                    }
                    if let Some(p) = self.search_equal_fact_proof_by_equivalence_class(f, child)? {
                        return Ok(Some(E(EP::ByEquivalenceClass(p))));
                    }
                }
                f => {
                    if let Some(p) = self.verify_by_strategy_atomic_except_equality(f, child)? {
                        return Ok(Some(A(p)));
                    }
                }
            }
        }
        if let Some(child) = state.for_premises(DefinitionAndForall) {
            match fact {
                AtomicFact::EqualFact(f) => {
                    if let Some(p) = self.search_equal_fact_proof_by_object_definition(f, child)? {
                        return Ok(Some(E(EP::ByObjectDefinition(p))));
                    }
                    if let Some(p) = self.search_equal_fact_proof_by_known_forall_fact(f, child)? {
                        return Ok(Some(E(p)));
                    }
                }
                f => {
                    if let Some(p) =
                        self.search_atomic_except_equality_fact_proof_by_definition(f, child)?
                    {
                        return Ok(Some(A(AP::ByDefinition(p))));
                    }
                    if let Some(p) = self
                        .search_atomic_except_equality_fact_proof_by_known_forall_fact(f, child)?
                    {
                        return Ok(Some(A(AP::ByKnownForallFact(p))));
                    }
                }
            }
        }
        if let Some(child) = state.after_rewrite() {
            match fact {
                AtomicFact::EqualFact(f) => {
                    if let Some(p) = self.search_equal_fact_proof_by_builtin_rewrite(f, child)? {
                        return Ok(Some(E(EP::ByBuiltinRewrite(p))));
                    }
                }
                f => {
                    if let Some(p) =
                        self.search_atomic_except_equality_fact_proof_by_builtin_rewrite(f, child)?
                    {
                        return Ok(Some(A(AP::ByBuiltinRewrite(p))));
                    }
                    if let Some(p) =
                        self.search_atomic_except_equality_fact_proof_by_known_rewrite(f, child)?
                    {
                        return Ok(Some(A(AP::ByKnownRewrite(p))));
                    }
                }
            }
        }
        Ok(None)
    }
}
