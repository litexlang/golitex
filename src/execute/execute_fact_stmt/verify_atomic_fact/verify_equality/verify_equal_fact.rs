use crate::ast::fact::EqualFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    equal_fact_result_from_search_fail, equal_fact_result_from_success,
    equal_fact_result_from_wd_fail, EqualFactSearchedProofByKnownForallViaSymmetry,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::VerifyEqualFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

use super::EqualitySearchProofByBuiltinStrategy;

impl Runtime {
    // Verify both objects first, then select one successful truth-search route.
    // Identity does not bypass WD; a search miss is a soft failure, not an error.
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
        let searched_proof = match self.search_equal_fact_proof(fact, verify_state)? {
            Some(proof) => Some(proof),
            None => self.try_parent_checked_beta_with_parent_well_definedness(
                fact,
                &well_defined_proof,
                verify_state,
            )?.map(|proof| {
                use super::by_object_definition::by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition;
                EqualFactSearchedProof::ByObjectDefinition(
                    super::EqualitySearchProofByObjectDefinition::ByFnApplication(
                        EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(proof),
                    ),
                )
            }),
        };
        match searched_proof {
            Some(searched_proof) => Ok(equal_fact_result_from_success(
                fact,
                well_defined_proof,
                searched_proof,
            )),
            None => Ok(equal_fact_result_from_search_fail(fact, well_defined_proof)),
        }
    }

    // Family-specific proof wrapper; permissions are scheduled centrally.
    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        use super::super::AtomicFactSearchedProof;
        Ok(
            match self.search_atomic_fact(&fact.clone().into(), state)? {
                Some(AtomicFactSearchedProof::Equality(p)) => Some(p),
                None => None,
                Some(AtomicFactSearchedProof::AtomicExceptEquality(_)) => {
                    unreachable!("equality dispatch")
                }
            },
        )
    }

    pub fn search_equal_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &EqualFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinStrategy>> {
        if let Some(proof) = self.search_equal_fact_by_cos_zero_integer_offset(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::CosZeroIntegerOffset(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_tuple_components(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::TupleComponentEquality(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_arithmetic_congruence(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_complex_with_nonzero_premises(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::ComplexWithNonzeroPremises(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_rational_with_nonzero_premises(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_extremum_equality(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::ExtremumEquality(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_finite_set_product_pointwise(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::FiniteSetProductPointwiseEquality(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_mod_congruence(fact, ctx)? {
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
