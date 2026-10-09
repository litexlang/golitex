use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

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
                let proof =
                    self.compile_equality_search(&success.fact, &success.searched_proof, position)?;
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
                self.compile_function_definition(fact, proof, position)?
            }
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
                .compile_arithmetic_congruence(
                    fact,
                    &proof.corresponding_arg_equal_proofs,
                    position,
                )?,
            EqualFactSearchedProof::ByKnownForallFact(_) => {
                return Err(LeanCompileError::unsupported("Equality/KnownForallFact"))
            }
            EqualFactSearchedProof::ByKnownForallFactViaSymmetry(_) => {
                return Err(LeanCompileError::unsupported(
                    "Equality/KnownForallFactViaSymmetry",
                ))
            }
            EqualFactSearchedProof::ByBuiltinRewrite(proof) => {
                self.compile_equality_builtin_rewrite(fact, proof, position)?
            }
        };
        Ok(proof)
    }
}
