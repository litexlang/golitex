use crate::ast::fact::EqualFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    equal_fact_result_from_search_fail, equal_fact_result_from_success,
    equal_fact_result_from_wd_fail, EqualFactSearchedProofByKnownForallViaSymmetry,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::VerifyEqualFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

use super::EqualitySearchProofByBuiltinStrategy;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof =
            match self.verify_equal_fact_well_definedness(fact, verify_state.clone())? {
                VerifyEqualFactWellDefinedResult::Success(proof) => proof,
                VerifyEqualFactWellDefinedResult::Failed(reason) => {
                    return Ok(equal_fact_result_from_wd_fail(reason));
                }
            };
        match self.search_equal_fact_proof(fact, verify_state)? {
            Some(searched_proof) => Ok(equal_fact_result_from_success(
                fact,
                well_defined_proof,
                searched_proof,
            )),
            None => Ok(equal_fact_result_from_search_fail(fact, well_defined_proof)),
        }
    }

    // Stage order: builtin rule → equivalence class → object definition → builtin strategy →
    // matching one arg by one → known forall → (if allowed) builtin rewrite.
    // MatchingOneArgByOne is constructor peel (not rewrite).
    //
    // Why rewrite: Calculation needs closed numeric trees; goals may still
    // mention identifiers equal to a stored closed form. Rewrite substitutes
    // those representatives, then proves the residual with rewrite off — see
    // EqualitySearchProofByBuiltinRewrite (ClosedNumeric only; not general congruence).
    // Ok(None) means no proof found; that is not a runtime error.
    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        if let Some(result) = self.search_equal_fact_builtin_rule(fact, verify_state.clone())? {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinRule(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_equivalence_class(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByEquivalenceClass(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_object_definition(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByObjectDefinition(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinStrategy(result)));
        }

        // Child equalities: no forall, no rewrite, no WD store.
        let matching_child_state = VerifyState {
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
        if let Some(result) =
            self.search_equal_fact_proof_by_matching_one_arg_by_one(fact, matching_child_state)?
        {
            return Ok(Some(EqualFactSearchedProof::ByMatchingOneArgByOne(result)));
        }

        if verify_state.can_use_def_and_known_forall_and_known_strategy {
            if let Some(result) =
                self.search_equal_fact_proof_by_known_forall_fact(fact, verify_state.clone())?
            {
                return Ok(Some(result));
            }
        }

        if verify_state.can_use_rewrite {
            if let Some(result) =
                self.search_equal_fact_proof_by_builtin_rewrite(fact, verify_state)?
            {
                return Ok(Some(EqualFactSearchedProof::ByBuiltinRewrite(result)));
            }
        }

        Ok(None)
    }

    pub fn search_equal_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinStrategy>> {
        if let Some(proof) =
            self.search_equal_fact_by_rational_with_nonzero_premises(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ));
        }
        if let Some(proof) =
            self.search_equal_fact_by_extremum_equality(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::ExtremumEquality(proof),
            ));
        }
        if let Some(proof) =
            self.search_equal_fact_by_finite_set_product_pointwise(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::FiniteSetProductPointwiseEquality(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_mod_congruence(fact, verify_state)? {
            return Ok(Some(EqualitySearchProofByBuiltinStrategy::ModCongruence(
                proof,
            )));
        }
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        if let Some(proof) = self.search_atomic_fact_proof_by_known_forall_fact(
            &(fact.clone().into()),
            verify_state.clone(),
        )? {
            return Ok(Some(EqualFactSearchedProof::ByKnownForallFact(Box::new(
                proof,
            ))));
        }
        // Legacy equality symmetry: try known forall on the swapped sides.
        let reversed = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: fact.right.clone(),
            right: fact.left.clone(),
            line_file: fact.line_file.clone(),
        };
        if let Some(proof) = self.search_atomic_fact_proof_by_known_forall_fact(
            &(reversed.clone().into()),
            verify_state,
        )? {
            return Ok(Some(EqualFactSearchedProof::ByKnownForallFactViaSymmetry(
                Box::new(EqualFactSearchedProofByKnownForallViaSymmetry {
                    reversed_equal: reversed,
                    known_forall: proof,
                }),
            )));
        }
        Ok(None)
    }
}
