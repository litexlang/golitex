use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError,LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::FiniteProperInclusionProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_cardinality_weak_bound(
        &self,
        goal: &AtomicFact,
        subset: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (Some(a), Some(b)) = (finite_size_set(low), finite_size_set(high)) else {
            return Err(LeanCompileError::unsupported(
                "FiniteCardinalityBound/SizeObjects",
            ));
        };
        if !matches!(goal, AtomicFact::LessEqualFact(_))
            || strict
            || !matches!(source_subject(subset)?,Fact::AtomicFact(AtomicFact::SubsetFact(ref p)) if p.left.ir()==a.ir() && p.right.ir()==b.ir())
        {
            return Err(LeanCompileError::unsupported(
                "FiniteCardinalityBound/Subset",
            ));
        }
        let proof = self
            .compile_verify(subset, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        Ok(format!(
            "(Litex.finiteCardinalitySubsetLe {} {} {proof})",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(high, &complete)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_finite_cardinality_strict_bound(
        &self,
        goal: &AtomicFact,
        inclusion: &FiniteProperInclusionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (Some(a), Some(b)) = (finite_size_set(low), finite_size_set(high)) else {
            return Err(LeanCompileError::unsupported(
                "FiniteCardinalityStrict/SizeObjects",
            ));
        };
        if !matches!(goal, AtomicFact::LessFact(_)) || !strict {
            return Err(LeanCompileError::unsupported(
                "FiniteCardinalityStrict/Strength",
            ));
        }
        let (proof, count) = match inclusion {
            FiniteProperInclusionProof::ByProperSubset {
                proper_subset_proof: p,
            } => {
                if !matches!(source_subject(p)?,Fact::AtomicFact(AtomicFact::ProperSubsetFact(ref f)) if f.left.ir()==a.ir() && f.right.ir()==b.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "FiniteCardinalityStrict/ProperSubset",
                    ));
                }
                (
                    self.compile_verify(p, &position.atomic_search_prior(0)?)?.1,
                    1,
                )
            }
            FiniteProperInclusionProof::BySubsetAndNotEqual {
                subset_proof,
                not_equal_proof,
            } => {
                if !matches!(source_subject(subset_proof)?,Fact::AtomicFact(AtomicFact::SubsetFact(ref f)) if f.left.ir()==a.ir() && f.right.ir()==b.ir())
                    || !matches!(source_subject(not_equal_proof)?,Fact::AtomicFact(AtomicFact::NotEqualFact(ref f)) if f.left.ir()==a.ir() && f.right.ir()==b.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "FiniteCardinalityStrict/SubsetAndDifference",
                    ));
                }
                let subset = self
                    .compile_verify(subset_proof, &position.atomic_search_prior(0)?)?
                    .1;
                let different = self
                    .compile_verify(not_equal_proof, &position.atomic_search_prior(1)?)?
                    .1;
                (format!("(And.intro {subset} {different})"), 2)
            }
        };
        let complete = position.atomic_search_prior(count)?;
        Ok(format!(
            "(Litex.finiteCardinalityProperSubsetLt {} {} {proof})",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(high, &complete)?
        ))
    }
}
