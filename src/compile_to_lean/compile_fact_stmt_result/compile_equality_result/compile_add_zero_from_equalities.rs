use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_add_zero_from_equalities(
        &self,
        fact: &EqualFact,
        remaining_equal: &VerifyFactResult,
        zero_equal: &VerifyFactResult,
        reversed: bool,
        zero_left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (expression, target) = if reversed {
            (&fact.right, &fact.left)
        } else {
            (&fact.left, &fact.right)
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = expression else {
            return Err(LeanCompileError::new(
                if zero_left {
                    "AddZeroLeft/Orientation"
                } else {
                    "AddZeroRight/Orientation"
                },
                "The selected direction must put its original sum on the recorded side.",
            ));
        };
        let (
            remaining_operand,
            zero_operand,
            remaining_field,
            zero_field,
            wd_field,
            law,
            requirement,
        ) = if zero_left {
            (
                &sum.right,
                &sum.left,
                "right",
                "left",
                "2",
                "zeroAdd",
                "AddZeroLeft/RequirementSubject",
            )
        } else {
            (
                &sum.left,
                &sum.right,
                "left",
                "right",
                "1",
                "addZero",
                "AddZeroRight/RequirementSubject",
            )
        };
        let remaining = source_subject(remaining_equal)?;
        let zero = source_subject(zero_equal)?;
        match (&remaining, &zero) {
            (Fact::AtomicFact(AtomicFact::EqualFact(remaining)), Fact::AtomicFact(AtomicFact::EqualFact(zero)))
                if remaining.left.ir() == remaining_operand.ir()
                    && remaining.right.ir() == target.ir()
                    && zero.left.ir() == zero_operand.ir()
                    && is_exact_zero(&zero.right)
                    && remaining.fact_id != zero.fact_id => {}
            _ => return Err(LeanCompileError::new(requirement, "The actual ordered equality identities must relate the remaining operand to its target and the other operand to literal zero.")),
        }
        let remaining = self.compile_verify(remaining_equal, position)?.1;
        let zero = self.compile_verify(zero_equal, position)?.1;
        let term = self.compile_object_reference(expression, position)?;
        let target = self.compile_object_reference(target, position)?;
        let conclude = if reversed {
            "_litex_add_zero_result.symm"
        } else {
            "_litex_add_zero_result"
        };
        // Constructor WD supplies its original C certificate. The recorded zero
        // equality transports only the denotation; addZero and the recorded
        // remaining equality then finish this selected route in source order.
        let transport = if zero_left {
            "M.addValue zero_value (Litex.denote _litex_zero_sum.val.right)"
        } else {
            "M.addValue (Litex.denote _litex_zero_sum.val.left) zero_value"
        };
        Ok(format!("(by\n  let _litex_zero_sum := {term}\n  have _litex_remaining : Litex.Same _litex_zero_sum.val.{remaining_field} {target} := {remaining}\n  have _litex_zero : Litex.Same _litex_zero_sum.val.{zero_field} (Litex.number (M := M) 0) := {zero}\n  have _litex_add_zero_result : Litex.Same _litex_zero_sum {target} := ((congrArg (fun zero_value => {transport}) _litex_zero).trans (Litex.{law} _litex_zero_sum.val.{remaining_field} _litex_zero_sum.wd.{wd_field})).trans _litex_remaining\n  exact {conclude}\n)"))
    }
}
