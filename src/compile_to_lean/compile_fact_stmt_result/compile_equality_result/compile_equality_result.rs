use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_equality_result(
        &self,
        result: &VerifyEqualityResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        match result {
            VerifyEqualityResult::Success(success) => {
                let left = self.compile_wd(&success.well_defined_proof.left, position)?;
                let right = self.compile_wd(
                    &success.well_defined_proof.right,
                    &SourcePosition {
                        before: 1,
                        ..*position
                    },
                )?;
                let formed = SourcePosition {
                    before: 2,
                    ..*position
                };
                let position = &formed;
                ensure_object(&success.fact.left, &success.well_defined_proof.left)?;
                ensure_object(&success.fact.right, &success.well_defined_proof.right)?;
                let proof = self.compile_equality_search_with_parent_wd(
                    &success.fact,
                    &success.searched_proof,
                    Some(&success.well_defined_proof),
                    position,
                )?;
                Ok((format!("Litex.Same {left} {right}"), proof))
            }
            VerifyEqualityResult::Failed(_) => Err(LeanCompileError::new(
                "Equality/Failed",
                "Failed verification is not proof evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_equality_search(
        &self,
        fact: &EqualFact,
        proof: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_equality_search_with_parent_wd(fact, proof, None, position)
    }

    pub(in crate::compile_to_lean) fn compile_equality_search_with_parent_wd(
        &self,
        fact: &EqualFact,
        proof: &EqualFactSearchedProof,
        parent_wd: Option<&EqualFactWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let left = self.compile_object_reference(&fact.left, position)?;
        self.compile_object_reference(&fact.right, position)?;
        let proof = match proof {
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_)) => {
                if fact.left.ir() != fact.right.ir() {
                    return Err(LeanCompileError::new(
                        "SameIr",
                        "Identity evidence has different endpoints.",
                    ));
                }
                format!("(Litex.sameRefl {left})")
            }
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameFreeParamShape(
                _,
            )) => return Err(LeanCompileError::unsupported("Equality/SameFreeParamShape")),
            EqualFactSearchedProof::ByClosedCalculation(proof) => {
                self.compile_closed_equality(fact, proof, position)?
            }
            EqualFactSearchedProof::ByKnownSpecialProperty(_) => {
                return Err(LeanCompileError::unsupported(
                    "Equality/KnownSpecialProperty",
                ))
            }
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(proof),
            ) => self.compile_abs_nonnegative_identity(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
                    ElementaryArithmeticProof::AbsEvenPower,
                ),
            ) => self.compile_abs_even_power_identity(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::PowerProductSameBase(proof),
            ) => self.compile_natural_power_product(
                fact,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::PowerOfPower(proof),
            ) => self.compile_natural_power_of_power(
                fact,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AddZeroRightFromEqualities(proof),
            ) => self.compile_add_zero_from_equalities(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Calculation(
                    EqualitySearchProofByCalculation::Rational {},
                ),
            ) => self.compile_rational(fact, &[], &[], false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(proof),
            ) => self.compile_scalar_division_relation(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(_) => {
                return Err(LeanCompileError::unsupported("Equality/BuiltinRule"))
            }
            EqualFactSearchedProof::ByEquivalenceClass(proof) => {
                self.compile_equivalence_class(fact, proof, position)?
            }
            EqualFactSearchedProof::ByObjectDefinition(proof) => {
                self.compile_function_definition(fact, proof, parent_wd, position)?
            }
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(proof),
            ) => self.compile_arithmetic_congruence_strategy(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ) => self.compile_rational(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                true,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinStrategy(_) => {
                return Err(LeanCompileError::unsupported("Equality/BuiltinStrategy"))
            }
            EqualFactSearchedProof::ByMatchingOneArgByOne(proof) => self
                .compile_matching_one_arg_by_one(
                    fact,
                    &proof.corresponding_arg_equal_proofs,
                    position,
                )?,
            EqualFactSearchedProof::ByKnownForallFact(proof) => {
                self.compile_known_application(&fact.clone().into(), proof, position)?
                    .1
            }
            EqualFactSearchedProof::ByKnownForallFactViaSymmetry(proof) => {
                if proof.reversed_equal.left.ir() != fact.right.ir()
                    || proof.reversed_equal.right.ir() != fact.left.ir()
                {
                    return Err(LeanCompileError::new(
                        "Equality/KnownForallSymmetryEndpoints",
                        "The original symmetry capture must reverse both exact goal endpoints.",
                    ));
                }
                let reversed = self
                    .compile_known_application(
                        &proof.reversed_equal.clone().into(),
                        &proof.known_forall,
                        position,
                    )?
                    .1;
                format!("(Eq.symm {reversed})")
            }
            EqualFactSearchedProof::ByBuiltinRewrite(proof) => {
                self.compile_equality_builtin_rewrite(fact, proof, position)?
            }
        };
        Ok(proof)
    }
}
