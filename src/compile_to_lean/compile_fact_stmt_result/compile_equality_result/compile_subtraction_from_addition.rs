use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_subtraction_from_addition(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "SubtractionFromAddition/Requirements",
            ));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(premise)) = source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported(
                "SubtractionFromAddition/Premise",
            ));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &premise.left else {
            return Err(LeanCompileError::unsupported("SubtractionFromAddition/Sum"));
        };
        let matched = [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ]
        .into_iter()
        .find_map(|(target, difference, reversed)| {
            let (subtracted, negated) = match difference {
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub))
                    if sub.left.ir() == premise.right.ir() =>
                {
                    (sub.right.as_ref(), false)
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg))
                    if is_exact_zero(&premise.right) =>
                {
                    (neg.arg.as_ref(), true)
                }
                _ => return None,
            };
            if target.ir() == sum.left.ir() && subtracted.ir() == sum.right.ir() {
                Some((difference, reversed, false, negated))
            } else if target.ir() == sum.right.ir() && subtracted.ir() == sum.left.ir() {
                Some((difference, reversed, true, negated))
            } else {
                None
            }
        })
        .ok_or_else(|| LeanCompileError::unsupported("SubtractionFromAddition/Endpoints"))?;
        let (difference, reversed, commuted, negated) = matched;
        let prior = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            0,
        );
        let child = self.compile_verify(&requirements[0], &prior)?.1;
        let complete = SourcePosition { before: 1, ..prior };
        let sum = self.compile_object_reference(&premise.left, &complete)?;
        let difference = self.compile_object_reference(difference, &complete)?;
        let target_field = if commuted { "right" } else { "left" };
        let subtracted_field = if commuted { "left" } else { "right" };
        let law = if commuted { "(add_comm _ _)" } else { "rfl" };
        let proof = if negated {
            let order = if commuted {
                "((add_comm _ _).trans _zero)"
            } else {
                "_zero"
            };
            format!("(by\n  let _sum := {sum}\n  let _difference := {difference}\n  have _sumEqual : Litex.Same _sum (Litex.number (M := M) 0) := {}\n  have _left := Litex.NativeBridge.asComplex_spec _sum.val.left _sum.wd.1\n  have _right := Litex.NativeBridge.asComplex_spec _sum.val.right _sum.wd.2\n  change M.addValue (Litex.denote _sum.val.left) (Litex.denote _sum.val.right) = M.number 0 at _sumEqual\n  rw [_left, _right, M.add_numbers] at _sumEqual\n  have _zero := M.number_injective _sumEqual\n  change Litex.denote _sum.val.{target_field} = M.negValue (Litex.denote _sum.val.{subtracted_field})\n  rw [_left, _right, M.neg_numbers]\n  exact congrArg M.number (eq_neg_of_add_eq_zero_left {order}))", child.replace('\n', "\n  "))
        } else {
            format!("(by\n  let _sum := {sum}\n  let _difference := {difference}\n  have _sumEqual : Litex.Same _sum _difference.val.left := {}\n  have _left := Litex.NativeBridge.asComplex_spec _sum.val.left _sum.wd.1\n  have _right := Litex.NativeBridge.asComplex_spec _sum.val.right _sum.wd.2\n  change Litex.denote _sum.val.{target_field} = M.subValue (Litex.denote _difference.val.left) (Litex.denote _difference.val.right)\n  rw [← _sumEqual]\n  change Litex.denote _sum.val.{target_field} = M.subValue (M.addValue (Litex.denote _sum.val.left) (Litex.denote _sum.val.right)) (Litex.denote _sum.val.{subtracted_field})\n  rw [_left, _right, M.add_numbers, M.sub_numbers]\n  exact congrArg M.number (eq_sub_iff_add_eq.mpr {law}))", child.replace('\n', "\n  "))
        };
        Ok(if reversed {
            format!("(Eq.symm {proof})")
        } else {
            proof
        })
    }
}
