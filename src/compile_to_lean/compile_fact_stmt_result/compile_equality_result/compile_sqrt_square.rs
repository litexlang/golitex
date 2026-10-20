use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_sqrt_square(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (power_object, power, other, reversed) = match (&goal.left, &goal.right) {
            (value @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)), other)
                if matches!(
                    power.base.as_ref(),
                    Obj::ExpLogOperator(ExpLogOperator::Sqrt(_))
                ) =>
            {
                (value, power, other, false)
            }
            (other, value @ Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)))
                if matches!(
                    power.base.as_ref(),
                    Obj::ExpLogOperator(ExpLogOperator::Sqrt(_))
                ) =>
            {
                (value, power, other, true)
            }
            _ => {
                return Err(LeanCompileError::new(
                    "SqrtSquare/Constructor",
                    "The selected identity requires the square of the original square root.",
                ))
            }
        };
        let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) = power.base.as_ref() else {
            unreachable!()
        };
        if root.arg.ir() != other.ir()
            || !matches!(power.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "2")
        {
            return Err(LeanCompileError::new("SqrtSquare/Endpoints", "The root argument must equal the opposite endpoint and the original exponent must be literal 2."));
        }
        if requirements.len() != 1 {
            return Err(LeanCompileError::new(
                "SqrtSquare/Requirements",
                "The square rule needs its one original nonnegative argument proof.",
            ));
        }
        if !matches!(source_subject(&requirements[0])?,
            Fact::AtomicFact(AtomicFact::LessEqualFact(ref fact))
                if is_exact_zero(&fact.left) && fact.right.ir() == root.arg.ir())
        {
            return Err(LeanCompileError::new(
                "SqrtSquare/RequirementSubject",
                "The selected child must prove zero <= the exact square-root argument.",
            ));
        }
        let child_position = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            0,
        );
        let nonnegative = self.compile_verify(&requirements[0], &child_position)?.1;
        let term = self.compile_object_reference(power_object, position)?;
        let exponent = self.compile_literal_natural_identity(&power.exponent, 2, position)?;
        let proof = format!("(by\n  let _litex_power := {term}\n  have _litex_nonnegative : Litex.Le (Litex.number (M := M) 0) _litex_power.val.base.val.arg := {nonnegative}\n  have _litex_exponent : Litex.denote _litex_power.val.exponent = M.number ((2 : ℕ) : ℂ) := {exponent}\n  have _litex_square := Litex.sqrtSquareValue _litex_power.val.base.val.arg _litex_power.val.base.wd.1 _litex_nonnegative\n  exact (show M.powValue (Litex.denote _litex_power.val.base) (Litex.denote _litex_power.val.exponent) = Litex.denote _litex_power.val.base.val.arg from by\n    rw [_litex_exponent]\n    exact _litex_square))");
        Ok(if reversed {
            format!("({proof}).symm")
        } else {
            proof
        })
    }
}
