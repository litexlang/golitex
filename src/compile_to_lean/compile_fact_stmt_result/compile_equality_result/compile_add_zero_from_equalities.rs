use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::add_zero_from_equalities_builtin_rule_proof::AddZeroRightFromEqualitiesBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_add_zero_from_equalities(
        &self,
        fact: &EqualFact,
        proof: &AddZeroRightFromEqualitiesBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (expression, target) = if proof.reversed {
            (&fact.right, &fact.left)
        } else {
            (&fact.left, &fact.right)
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = expression else {
            return Err(LeanCompileError::new(
                "AddZeroRight/Orientation",
                "The selected direction must put its original sum on the recorded side.",
            ));
        };
        let remaining = source_subject(&proof.remaining_equal)?;
        let zero = source_subject(&proof.zero_equal)?;
        match (&remaining, &zero) {
            (Fact::AtomicFact(AtomicFact::EqualFact(remaining)), Fact::AtomicFact(AtomicFact::EqualFact(zero)))
                if remaining.left.ir() == sum.left.ir()
                    && remaining.right.ir() == target.ir()
                    && zero.left.ir() == sum.right.ir()
                    && is_exact_zero(&zero.right)
                    && remaining.fact_id != zero.fact_id => {}
            _ => return Err(LeanCompileError::new("AddZeroRight/RequirementSubject", "The actual ordered equality identities must relate the remaining operand to its target and the other operand to literal zero.")),
        }
        let remaining = self.compile_verify(&proof.remaining_equal, position)?.1;
        let zero = self.compile_verify(&proof.zero_equal, position)?.1;
        let term = self.compile_object_reference(expression, position)?;
        let target = self.compile_object_reference(target, position)?;
        let conclude = if proof.reversed {
            "_litex_add_zero_result.symm"
        } else {
            "_litex_add_zero_result"
        };
        // Constructor WD supplies its original C certificate. The recorded zero
        // equality transports only the denotation; addZero and the recorded
        // remaining equality then finish this selected route in source order.
        Ok(format!("(by\n  let _litex_zero_sum := {term}\n  have _litex_remaining : Litex.Same _litex_zero_sum.val.left {target} := {remaining}\n  have _litex_zero : Litex.Same _litex_zero_sum.val.right (Litex.number (M := M) 0) := {zero}\n  have _litex_add_zero_result : Litex.Same _litex_zero_sum {target} := ((congrArg (fun zero_value => M.addValue (Litex.denote _litex_zero_sum.val.left) zero_value) _litex_zero).trans (Litex.addZero _litex_zero_sum.val.left _litex_zero_sum.wd.1)).trans _litex_remaining\n  exact {conclude}\n)"))
    }
}
