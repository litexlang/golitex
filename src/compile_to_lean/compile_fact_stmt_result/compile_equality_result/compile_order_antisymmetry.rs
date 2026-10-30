use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave7::EqualityFromTwoSidedWeakOrderBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_extremum_equality_strategy(
        &self,
        goal: &EqualFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let has_extremum = [&goal.left, &goal.right].iter().any(|object| {
            matches!(
                object,
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(_))
                    | Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(_))
                    | Obj::ArithmeticOperator(ArithmeticOperator::Max(_))
                    | Obj::ArithmeticOperator(ArithmeticOperator::Min(_))
            )
        });
        if !has_extremum || requirements.len() != 2 || children.len() != 2 {
            return Err(LeanCompileError::unsupported(
                "ExtremumEquality/Requirements",
            ));
        }
        let mut premises = Vec::new();
        for (index, ((requirement, child), (left, right))) in requirements
            .iter()
            .zip(children)
            .zip([(&goal.left, &goal.right), (&goal.right, &goal.left)])
            .enumerate()
        {
            let subject = source_subject(child)?;
            if subject.fact_id() != requirement.fact_id() || subject.ir() != requirement.ir() {
                return Err(LeanCompileError::unsupported(
                    "ExtremumEquality/RequirementSubject",
                ));
            }
            if !matches!(requirement,
                Fact::AtomicFact(AtomicFact::LessEqualFact(f))
                    if f.left.ir() == left.ir() && f.right.ir() == right.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "ExtremumEquality/RequirementSubject",
                ));
            }
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(children),
                index,
            );
            premises.push(self.compile_verify(child, &prior)?.1);
        }
        Ok(format!(
            "(Litex.sameOfLeAntisymm {} {} {} {})",
            self.compile_object_reference(&goal.left, position)?,
            self.compile_object_reference(&goal.right, position)?,
            premises[0],
            premises[1]
        ))
    }

    pub(super) fn compile_order_antisymmetry(
        &self,
        goal: &EqualFact,
        proof: &EqualityFromTwoSidedWeakOrderBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut premises = Vec::new();
        for (left, right, premise) in [
            (&goal.left, &goal.right, &proof.left_le_right_proof),
            (&goal.right, &goal.left, &proof.right_le_left_proof),
        ] {
            let (low, high, strict) = source_order_oriented(&premise.fact)?;
            if strict || low.ir() != left.ir() || high.ir() != right.ir() {
                return Err(LeanCompileError::unsupported(
                    "OrderAntisymmetry/PremiseSubject",
                ));
            }
            premises.push(self.compile_order_known_premise(premise, position)?.1);
        }
        Ok(format!(
            "(Litex.sameOfLeAntisymm {} {} {} {})",
            self.compile_object_reference(&goal.left, position)?,
            self.compile_object_reference(&goal.right, position)?,
            premises[0],
            premises[1]
        ))
    }
}
