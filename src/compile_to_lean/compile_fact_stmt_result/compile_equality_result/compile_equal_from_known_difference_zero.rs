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
        let (difference, peer) = if proof.difference_on_left {
            (&cited.left, &cited.right)
        } else {
            (&cited.right, &cited.left)
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
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".into(),
        }));
        let zero_path = self.compile_equality_path(peer, &zero, &proof.zero_path, position)?;
        let difference = self.compile_object_reference(difference, position)?;
        let edge = if proof.difference_on_left {
            reference
        } else {
            format!("({reference}).symm")
        };
        let equality = if proof.zero_path.path.is_empty() {
            edge
        } else {
            format!("({edge}).trans ({zero_path})")
        };
        let conclude = if forward {
            "_litex_same"
        } else {
            "_litex_same.symm"
        };
        Ok(format!("(by\n  let _litex_difference := {difference}\n  have _litex_zero : Litex.Same _litex_difference (Litex.number (M := M) 0) := {equality}\n  have _litex_same := Litex.sameOfSubZero _litex_difference.val.left _litex_difference.val.right _litex_difference.wd.1 _litex_difference.wd.2 _litex_zero\n  exact {conclude}\n)"))
    }
}
