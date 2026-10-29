use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave6::AbsNonnegEqualsSelfBuiltinRuleProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_abs_even_power_identity(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left, right, reversed) = match (&goal.left, &goal.right) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Pow(left)), Obj::ArithmeticOperator(ArithmeticOperator::Pow(right))) if matches!(left.base.as_ref(), Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))) => (left, right, false),
            (Obj::ArithmeticOperator(ArithmeticOperator::Pow(left)), Obj::ArithmeticOperator(ArithmeticOperator::Pow(right))) if matches!(right.base.as_ref(), Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))) => (right, left, true),
            _ => return Err(LeanCompileError::new("AbsEvenPower/Constructor", "The selected identity must compare a power of the original absolute value with its argument's power.")),
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = left.base.as_ref() else {
            unreachable!()
        };
        let n = closed_integer(&left.exponent)
            .filter(|n| *n > 0 && n % 2 == 0)
            .ok_or_else(|| {
                LeanCompileError::new(
                    "AbsEvenPower/Exponent",
                    "The original exponent must be a positive even integer literal.",
                )
            })?;
        if abs.arg.ir() != right.base.ir() || left.exponent.ir() != right.exponent.ir() {
            return Err(LeanCompileError::new(
                "AbsEvenPower/Subject",
                "The selected identity changes its original base or exponent.",
            ));
        }
        let he_left = self.compile_literal_natural_identity(&left.exponent, n, position)?;
        let he_right = self.compile_literal_natural_identity(&right.exponent, n, position)?;
        let (left_object, right_object) = if reversed {
            (&goal.right, &goal.left)
        } else {
            (&goal.left, &goal.right)
        };
        let symmetric = if reversed { ".symm" } else { "" };
        Ok(format!("(by\n  let _litex_abs_power := {}\n  let _litex_argument_power := {}\n  exact (Litex.absPowStructuralSame _litex_abs_power _litex_argument_power ({n} : ℕ) (Litex.sameRefl _litex_abs_power.val.base.val.arg) {he_left} {he_right} (by norm_num)){symmetric}\n)", self.compile_object_reference(left_object, position)?, self.compile_object_reference(right_object, position)?))
    }

    pub(in crate::compile_to_lean) fn compile_abs_nonnegative_identity(
        &self,
        goal: &EqualFact,
        proof: &AbsNonnegEqualsSelfBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (abs_object, argument, reversed) = match (&goal.left, &goal.right) {
            (left @ Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)), right) if abs.arg.ir() == right.ir() => (left, right, false),
            (left, right @ Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs))) if abs.arg.ir() == left.ir() => (right, left, true),
            _ => return Err(LeanCompileError::new("AbsNonnegative/Subject", "The selected identity must compare the owned absolute value with its exact argument.")),
        };
        if proof.proof_of_requirement_facts.len() != 1 {
            return Err(LeanCompileError::new(
                "AbsNonnegative/Requirements",
                "The selected identity requires its one actual nonnegative argument proof.",
            ));
        }
        let requirement = &proof.proof_of_requirement_facts[0];
        let Fact::AtomicFact(subject) = source_subject(requirement)? else {
            return Err(LeanCompileError::unsupported(
                "AbsNonnegative/RequirementFamily",
            ));
        };
        let (zero, positive, strict) = source_order_oriented(&subject)?;
        if !is_exact_zero(zero) || positive.ir() != argument.ir() {
            return Err(LeanCompileError::new(
                "AbsNonnegative/RequirementSubject",
                "The selected argument proof must certify its exact lower bound zero.",
            ));
        }
        let nonnegative = self.compile_verify(requirement, position)?.1;
        let nonnegative = if strict {
            format!(
                "(Litex.ltToLe (Litex.number (M := M) 0) {} {nonnegative})",
                self.compile_object_reference(argument, position)?
            )
        } else {
            nonnegative
        };
        let term = self.compile_object_reference(abs_object, position)?;
        let symmetric = if reversed { ".symm" } else { "" };
        Ok(format!("(by\n  let _litex_abs := {term}\n  exact (Litex.absOfNonnegative _litex_abs.val.arg _litex_abs.wd {nonnegative}){symmetric}\n)"))
    }
}
