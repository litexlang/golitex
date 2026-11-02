use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_abs_idempotent(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (nested, single, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(outer)) = nested else {
                continue;
            };
            if !matches!(single, Obj::ArithmeticOperator(ArithmeticOperator::Abs(_)))
                || outer.arg.ir() != single.ir()
            {
                continue;
            }
            let term = self.compile_object_reference(single, position)?;
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!("(Litex.absIdempotent {term}){symmetric}"));
        }
        Err(LeanCompileError::unsupported("Abs/IdempotentSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_abs_negation(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (negative, original, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(negative_abs)),
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(original_abs)),
            ) = (negative, original)
            else {
                continue;
            };
            let argument = match negative_abs.arg.as_ref() {
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => Some(p.arg.as_ref()),
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if is_exact_zero(&p.left) => {
                    Some(p.right.as_ref())
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                    if closed_integer(&p.left) == Some(-1) {
                        Some(p.right.as_ref())
                    } else if closed_integer(&p.right) == Some(-1) {
                        Some(p.left.as_ref())
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if !argument.is_some_and(|a| a.ir() == original_abs.arg.ir()) {
                continue;
            }
            let normalized = self.compile_negated_value(
                &negative_abs.arg,
                "_abs.val.arg",
                "(Litex.realToComplex _abs.val.arg _abs.wd)",
                position,
            )?;
            let term = self.compile_object_reference(original, position)?;
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!("(by\n  let _abs := {term}\n  exact ((congrArg (Litex.absValue (M := M)) {normalized}).trans (Litex.absNegation _abs)){symmetric}\n)"));
        }
        Err(LeanCompileError::unsupported("Abs/NegationSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_abs_product(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (absolute, product, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(outer)) = absolute else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(inner)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)),
            ) = (outer.arg.as_ref(), product)
            else {
                continue;
            };
            let (
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(b)),
            ) = (product.left.as_ref(), product.right.as_ref())
            else {
                continue;
            };
            let reverse_args = if inner.left.ir() == a.arg.ir() && inner.right.ir() == b.arg.ir() {
                false
            } else if inner.left.ir() == b.arg.ir() && inner.right.ir() == a.arg.ir() {
                true
            } else {
                continue;
            };
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(Litex.absProduct {} {} {reverse_args}){symmetric}",
                self.compile_object_reference(&product.left, position)?,
                self.compile_object_reference(&product.right, position)?,
            ));
        }
        Err(LeanCompileError::unsupported("Abs/ProductSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_abs_nonpositive(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 1 {
            return Err(LeanCompileError::unsupported("Abs/NonpositiveRequirements"));
        }
        for (absolute, negative, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) = absolute else {
                continue;
            };
            let same_argument = match negative {
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(n)) => n.arg.ir() == p.arg.ir(),
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(n)) => {
                    is_exact_zero(&n.left) && n.right.ir() == p.arg.ir()
                }
                _ => false,
            };
            if !same_argument {
                continue;
            }
            let Fact::AtomicFact(subject) = source_subject(&requirements[0])? else {
                return Err(LeanCompileError::unsupported("Abs/NonpositiveFamily"));
            };
            let (left, right, strict) = source_order_oriented(&subject)?;
            if left.ir() != p.arg.ir() || !is_exact_zero(right) {
                return Err(LeanCompileError::unsupported("Abs/NonpositiveSubject"));
            }
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            let proof = self.compile_verify(&requirements[0], &child)?.1;
            let proof = if strict {
                format!("(Litex.ltToLe _abs.val.arg (Litex.number (M := M) 0) {proof})")
            } else {
                proof
            };
            let normalized = self.compile_negated_value(
                negative,
                "_abs.val.arg",
                "(Litex.realToComplex _abs.val.arg _abs.wd)",
                position,
            )?;
            let term = self.compile_object_reference(absolute, position)?;
            let symmetric = if reversed { ".symm" } else { "" };
            return Ok(format!("(by\n  let _abs := {term}\n  exact ((Litex.absOfNonpositive _abs {proof}).trans ({normalized}).symm){symmetric}\n)"));
        }
        Err(LeanCompileError::unsupported("Abs/NonpositiveEndpoints"))
    }
}
