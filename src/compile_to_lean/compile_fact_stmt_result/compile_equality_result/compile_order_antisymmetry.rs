use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave7::EqualityFromTwoSidedWeakOrderBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
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
