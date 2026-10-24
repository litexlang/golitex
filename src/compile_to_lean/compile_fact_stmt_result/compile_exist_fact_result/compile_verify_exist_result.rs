use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_exist_result(
        &self,
        result: &VerifyExistShapedFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        match result {
            VerifyExistShapedFactResult::NotExistFact(result) => {
                self.compile_verify_not_exist_result(result, position)
            }
            VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(
                proof,
            )) => self.compile_verify_unique_success(proof, position),
            VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(
                proof,
            )) => self.compile_verify_plain_exist_success(proof, position),
            VerifyExistShapedFactResult::ExistUniqueFact(_) => {
                Err(LeanCompileError::unsupported("ExistUnique/Failed"))
            }
            VerifyExistShapedFactResult::PlainExistFact(_) => Err(LeanCompileError::new(
                "Exist/Failed",
                "A failed existence result is not proof evidence.",
            )),
        }
    }

    /// Obtain retains this exact success directly, without a VerifyFact wrapper.
    pub(in crate::compile_to_lean) fn compile_verify_plain_exist_success(
        &self,
        proof: &VerifyPlainExistFactSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let ExistShapedFact::Exist(fact) = &proof.fact else {
            return Err(LeanCompileError::new(
                "Exist/Family",
                "The successful plain-exist result contains another family.",
            ));
        };
        let proposition =
            self.compile_exist_formation(fact, &proof.well_defined_proof, position)?;
        let evidence = match &proof.searched_proof {
            ExistShapedFactSearchedProof::ByKnownExistShapedFact(known) => {
                let registered = self.cited_fact_reference(known.cite_fact_id, position)?;
                let (source, unique) = match registered.0 {
                    Fact::ExistFact(source) => (source, false),
                    Fact::ExistUniqueFact(source) => (source, true),
                    _ => return Err(LeanCompileError::unsupported("Exist/CitationFamily")),
                };
                if source.fact_id != known.cite_fact_id
                    || !plain_exist_facts_alpha_equal(source, fact)
                {
                    return Err(LeanCompileError::new(
                        "Exist/CitationSubject",
                        "The original cited existential differs from this goal.",
                    ));
                }
                if unique {
                    format!("({}).1", registered.1)
                } else {
                    registered.1
                }
            }
            ExistShapedFactSearchedProof::ByBuiltinRule(builtin) => {
                self.compile_exist_builtin_result(fact, builtin, position)?
            }
            ExistShapedFactSearchedProof::ByKnownForallFact(known) => self
                .compile_exist_known_forall(
                    &proof.fact,
                    &proof.well_defined_proof,
                    known,
                    position,
                )?,
        };
        Ok((proposition, evidence))
    }
}
