use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_difference_zero_from_equal(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported("DifferenceZero/Requirements"));
        }
        let (difference, reverse) = if is_exact_zero(&goal.right) {
            (&goal.left, false)
        } else if is_exact_zero(&goal.left) {
            (&goal.right, true)
        } else {
            return Err(LeanCompileError::unsupported("DifferenceZero/Target"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(operands)) = difference else {
            return Err(LeanCompileError::unsupported("DifferenceZero/Target"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported("DifferenceZero/Premise"));
        };
        if equal.left.ir() != operands.left.ir() || equal.right.ir() != operands.right.ir() {
            return Err(LeanCompileError::unsupported("DifferenceZero/Premise"));
        }
        let prior = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            0,
        );
        let equality = self.compile_verify(&requirements[0], &prior)?.1;
        let complete = SourcePosition { before: 1, ..prior };
        let term = self.compile_object_reference(difference, &complete)?;
        let proof = format!("(by\n  let _difference := {term}\n  have _same : Litex.Same _difference.val.left _difference.val.right := {equality}\n  have _value := Litex.NativeBridge.asComplex_spec _difference.val.left _difference.wd.1\n  change M.subValue (Litex.denote _difference.val.left) (Litex.denote _difference.val.right) = M.number 0\n  rw [← _same, _value, M.sub_numbers, sub_self]\n)");
        Ok(if reverse {
            format!("(Eq.symm {proof})")
        } else {
            proof
        })
    }
}
