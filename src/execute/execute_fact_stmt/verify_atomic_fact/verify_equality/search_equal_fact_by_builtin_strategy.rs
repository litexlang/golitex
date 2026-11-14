//! Tier 2 equality strategy dispatcher: append-only registry of builtin strategies.
//! Top-level equality verification lives in Tier 1 `verify_equal_fact.rs`.

use super::EqualitySearchProofByBuiltinStrategy;
use crate::ast::fact::EqualFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_equal_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &EqualFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinStrategy>> {
        if let Some(proof) = self.search_riemann_integral_value_strategy(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::RiemannIntegralValue(proof),
            ));
        }
        if let Some(proof) = self.search_derivative_value_strategy(fact, ctx)? {
            return Ok(Some(EqualitySearchProofByBuiltinStrategy::DerivativeValue(
                proof,
            )));
        }
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
        if let Some(proof) = self.search_cartesian_coordinate_equality(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::CartesianCoordinateEquality(proof),
            ));
        }
        if let Some(proof) = self.search_abs_product_from_factors(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::AbsProductFromFactors(proof),
            ));
        }
        if let Some(proof) = self.search_function_application_congruence(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::FunctionApplicationCongruence(proof),
            ));
        }
        if let Some(proof) = self.search_matrix_structural_equality(fact, ctx)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::MatrixStructuralEquality(proof),
            ));
        }
        Ok(None)
    }
}
