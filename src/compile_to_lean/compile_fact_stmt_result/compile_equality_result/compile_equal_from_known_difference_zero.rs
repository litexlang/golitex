use crate::compile_to_lean::helper::is_exact_zero;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equal_from_known_difference_zero::EqualFromKnownDifferenceZeroBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_equal_from_known_difference_zero(
        &self,
        goal: &EqualFact,
        proof: &EqualFromKnownDifferenceZeroBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (cited, reference) = self.cited_fact_reference(proof.cite_fact_id, position)?;
        let Fact::AtomicFact(AtomicFact::EqualFact(cited)) = cited else {
            return Err(LeanCompileError::new(
                "DifferenceZero/Citation",
                "The selected citation is not an equality.",
            ));
        };
        let (difference, zero, zero_on_left) = if is_exact_zero(&cited.right) {
            (&cited.left, &cited.right, false)
        } else if is_exact_zero(&cited.left) {
            (&cited.right, &cited.left, true)
        } else {
            // The producer can select an edge inside zero's equivalence class.
            // Its ID alone does not record that edge's remaining path to zero.
            return Err(LeanCompileError::unsupported(
                "DifferenceZero/UncapturedZeroPath",
            ));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = difference else {
            return Err(LeanCompileError::new(
                "DifferenceZero/Constructor",
                "The cited zero equality has no subtraction.",
            ));
        };
        let forward = sub.left.ir() == goal.left.ir() && sub.right.ir() == goal.right.ir();
        let reverse = sub.left.ir() == goal.right.ir() && sub.right.ir() == goal.left.ir();
        if !forward && !reverse {
            return Err(LeanCompileError::new(
                "DifferenceZero/Subjects",
                "The cited subtraction has different operands.",
            ));
        }
        let difference = self.compile_object_reference(difference, position)?;
        self.compile_object_reference(zero, position)?;
        let equality = if zero_on_left {
            format!("({reference}).symm")
        } else {
            reference
        };
        let conclude = if forward {
            "_litex_same"
        } else {
            "_litex_same.symm"
        };
        Ok(format!("(by\n  let _litex_difference := {difference}\n  have _litex_zero : Litex.Same _litex_difference (Litex.number (M := M) 0) := {equality}\n  have _litex_same := Litex.sameOfSubZero _litex_difference.val.left _litex_difference.val.right _litex_difference.wd.1 _litex_difference.wd.2 _litex_zero\n  exact {conclude}\n)"))
    }
}
