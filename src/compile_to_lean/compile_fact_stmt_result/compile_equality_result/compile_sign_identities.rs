use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn sign_argument(object: &Obj) -> Option<&Obj> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(p)) => Some(&p.arg),
        _ => None,
    }
}

fn abs_argument(object: &Obj) -> Option<&Obj> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) => Some(&p.arg),
        _ => None,
    }
}

fn negative_one(object: &Obj) -> bool {
    let one = |o: &Obj| matches!(o, Obj::Literal(Literal::Number(n)) if n.normalized_value == "1");
    match object {
        Obj::Literal(Literal::Number(n)) => n.normalized_value == "-1",
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => one(&p.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
            is_exact_zero(&p.left) && one(&p.right)
        }
        _ => false,
    }
}

// Exactly the negation spellings recognized by the selected wave7 producer.
fn negated_argument(object: &Obj) -> Option<&Obj> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => Some(&p.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if is_exact_zero(&p.left) => {
            Some(&p.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) if negative_one(&p.left) => {
            Some(&p.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) if negative_one(&p.right) => {
            Some(&p.left)
        }
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_sign_product(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (signed, target, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Some(Obj::ArithmeticOperator(ArithmeticOperator::Mul(inner))) =
                sign_argument(signed)
            else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = target else {
                continue;
            };
            let (Some(a), Some(b)) = (sign_argument(&product.left), sign_argument(&product.right))
            else {
                continue;
            };
            let reverse_args = if inner.left.ir() == a.ir() && inner.right.ir() == b.ir() {
                false
            } else if inner.left.ir() == b.ir() && inner.right.ir() == a.ir() {
                true
            } else {
                continue;
            };
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(Litex.signProduct {} {} {reverse_args}){symm}",
                self.compile_object_reference(&product.left, position)?,
                self.compile_object_reference(&product.right, position)?
            ));
        }
        Err(LeanCompileError::unsupported("Sign/ProductSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_sign_abs_identity(
        &self,
        goal: &EqualFact,
        abs_target: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (product, target, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = product else {
                continue;
            };
            for (signed, other, sign_first) in [
                (&product.left, &product.right, true),
                (&product.right, &product.left, false),
            ] {
                let Some(arg) = sign_argument(signed) else {
                    continue;
                };
                let matching = if abs_target {
                    abs_argument(target).is_some_and(|a| a.ir() == arg.ir())
                        && other.ir() == arg.ir()
                } else {
                    abs_argument(other).is_some_and(|a| a.ir() == arg.ir())
                        && target.ir() == arg.ir()
                };
                if !matching {
                    continue;
                }
                let law = if abs_target {
                    "absEqualsSignTimes"
                } else {
                    "signTimesAbs"
                };
                let symm = if reversed != abs_target { ".symm" } else { "" };
                return Ok(format!(
                    "(Litex.{law} {} {sign_first}){symm}",
                    self.compile_object_reference(signed, position)?
                ));
            }
        }
        Err(LeanCompileError::unsupported("Sign/AbsIdentitySubject"))
    }

    pub(in crate::compile_to_lean) fn compile_sign_negation(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Some(negative) = sign_argument(left) else {
                continue;
            };
            let (Some(arg), Some(signed)) = (negated_argument(negative), negated_argument(right))
            else {
                continue;
            };
            let Some(original) = sign_argument(signed) else {
                continue;
            };
            if arg.ir() != original.ir() {
                continue;
            }
            let before = self.compile_negated_value(
                negative,
                "_sign.val.arg",
                "(Litex.realToComplex _sign.val.arg _sign.wd)",
                position,
            )?;
            let after = self.compile_negated_value(
                right,
                "_sign",
                "(Litex.integerToComplex _sign (Litex.signInZ _sign))",
                position,
            )?;
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(by\n  let _sign := {}\n  exact (((congrArg (Litex.signValue (M := M)) {before}).trans (Litex.signNegation _sign)).trans ({after}).symm){symm}\n)",
                self.compile_object_reference(signed, position)?
            ));
        }
        Err(LeanCompileError::unsupported("Sign/NegationSubject"))
    }

    fn compile_negated_value(
        &self,
        negative: &Obj,
        argument: &str,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match negative {
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(_)) => {
                Ok(format!("(Eq.refl (M.negValue (Litex.denote {argument})))"))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) if is_exact_zero(&p.left) => {
                Ok(format!("(Litex.zeroSubValue {argument} {member})"))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                let (coefficient, first) = if negative_one(&p.left) {
                    (&p.left, true)
                } else if negative_one(&p.right) {
                    (&p.right, false)
                } else {
                    return Err(LeanCompileError::unsupported("Sign/NegationCoefficient"));
                };
                let native = self.compile_numeric_observation(coefficient, position)?;
                let coefficient = format!(
                    "(({}).trans (congrArg M.number (by norm_num : {} = (-1 : ℂ))))",
                    native.1, native.0
                );
                let (operation, law) = if first {
                    (
                        format!("fun _c => M.mulValue _c (Litex.denote {argument})"),
                        "negOneMulValue",
                    )
                } else {
                    (
                        format!("fun _c => M.mulValue (Litex.denote {argument}) _c"),
                        "mulNegOneValue",
                    )
                };
                Ok(format!("((congrArg ({operation}) {coefficient}).trans (Litex.{law} {argument} {member}))"))
            }
            _ => Err(LeanCompileError::unsupported("Sign/NegationConstructor")),
        }
    }
}
