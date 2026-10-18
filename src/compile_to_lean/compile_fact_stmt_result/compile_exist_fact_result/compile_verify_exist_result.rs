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
        let VerifyExistShapedFactResult::PlainExistFact(result) = result else {
            return Err(LeanCompileError::unsupported("Exist/UniqueOrNegative"));
        };
        let VerifyPlainExistFactResult::Success(proof) = result else {
            return Err(LeanCompileError::new(
                "Exist/Failed",
                "A failed existence result is not proof evidence.",
            ));
        };
        self.compile_verify_plain_exist_success(proof, position)
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
                let Fact::ExistFact(source) = registered.0 else {
                    return Err(LeanCompileError::unsupported("Exist/CitationFamily"));
                };
                if source.fact_id != known.cite_fact_id
                    || !plain_exist_facts_alpha_equal(source, fact)
                {
                    return Err(LeanCompileError::new(
                        "Exist/CitationSubject",
                        "The original cited existential differs from this goal.",
                    ));
                }
                registered.1
            }
            ExistShapedFactSearchedProof::ByBuiltinRule(_) => {
                return Err(LeanCompileError::unsupported("Exist/BuiltinRule"))
            }
            ExistShapedFactSearchedProof::ByKnownForallFact(_) => {
                return Err(LeanCompileError::unsupported("Exist/KnownForall"))
            }
        };
        Ok((proposition, evidence))
    }
}
