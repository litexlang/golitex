use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_exp_ln_inverse(
        &self,
        fact: &EqualFact,
        exp_of_ln: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut selected = None;
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let argument = match (object, exp_of_ln) {
                (Obj::ExpLogOperator(ExpLogOperator::Exp(e)), true) => match e.arg.as_ref() {
                    Obj::ExpLogOperator(ExpLogOperator::Ln(l)) => &l.arg,
                    _ => continue,
                },
                (Obj::ExpLogOperator(ExpLogOperator::Ln(l)), false) => match l.arg.as_ref() {
                    Obj::ExpLogOperator(ExpLogOperator::Exp(e)) => &e.arg,
                    _ => continue,
                },
                _ => continue,
            };
            if argument.ir() == other.ir() {
                selected = Some((object, argument.as_ref(), reversed));
                break;
            }
        }
        let (object, argument, reversed) =
            selected.ok_or_else(|| LeanCompileError::unsupported("ExpLn/InverseSubject"))?;
        if requirements.len() != usize::from(exp_of_ln) {
            return Err(LeanCompileError::unsupported("ExpLn/InverseRequirements"));
        }
        let term = self.compile_object_reference(object, position)?;
        let proof = if exp_of_ln {
            let positive = match source_subject(&requirements[0])? {
                Fact::AtomicFact(AtomicFact::LessFact(f)) => {
                    is_exact_zero(&f.left) && f.right.ir() == argument.ir()
                }
                Fact::AtomicFact(AtomicFact::GreaterFact(f)) => {
                    f.left.ir() == argument.ir() && is_exact_zero(&f.right)
                }
                _ => false,
            };
            if !positive {
                return Err(LeanCompileError::unsupported("ExpLn/InversePositive"));
            }
            let child = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                0,
            );
            format!(
                "(Litex.expLn {term} {})",
                self.compile_verify(&requirements[0], &child)?.1
            )
        } else {
            format!("(Litex.lnExp {term})")
        };
        Ok(if reversed {
            format!("{proof}.symm")
        } else {
            proof
        })
    }

    pub(in crate::compile_to_lean) fn compile_euler_identity(
        &self,
        fact: &EqualFact,
        logarithm: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let valid = match (object, logarithm) {
                (Obj::ExpLogOperator(ExpLogOperator::Ln(p)), true) => {
                    matches!(p.arg.as_ref(), Obj::Literal(Literal::EulerNumber(_)))
                        && matches!(other, Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
                }
                (Obj::ExpLogOperator(ExpLogOperator::Exp(p)), false) => {
                    matches!(p.arg.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
                        && matches!(other, Obj::Literal(Literal::EulerNumber(_)))
                }
                _ => false,
            };
            if !valid {
                continue;
            }
            let term = self.compile_object_reference(object, position)?;
            let other = self.compile_object_reference(other, position)?;
            let proof = if logarithm {
                format!("(Litex.lnEuler {term} rfl)")
            } else {
                format!("(show Litex.Same {term} {other} from Litex.denoteExp {term} 1 rfl)")
            };
            return Ok(if reversed {
                format!("{proof}.symm")
            } else {
                proof
            });
        }
        Err(LeanCompileError::unsupported("EulerIdentity/Subject"))
    }

    pub(in crate::compile_to_lean) fn compile_log_basic_identity(
        &self,
        fact: &EqualFact,
        self_argument: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let one =
            |x: &Obj| matches!(x, Obj::Literal(Literal::Number(n)) if n.normalized_value=="1");
        let mut chosen = None;
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::ExpLogOperator(ExpLogOperator::Log(p)) = object else {
                continue;
            };
            let valid = if self_argument {
                p.base.ir() == p.arg.ir() && one(other)
            } else {
                one(&p.arg) && is_exact_zero(other)
            };
            if valid {
                chosen = Some((object, p, reversed));
                break;
            }
        }
        let (object, p, reversed) =
            chosen.ok_or_else(|| LeanCompileError::unsupported("LogIdentity/Subject"))?;
        let term = self.compile_object_reference(object, position)?;
        let mut children = Vec::new();
        let mut subjects = Vec::new();
        for (i, requirement) in requirements.iter().enumerate() {
            subjects.push(source_subject(requirement)?);
            children.push(
                self.compile_verify(
                    requirement,
                    &SourcePosition::new(
                        Some(position),
                        SourceOwner::EqualityRequirements(requirements),
                        i,
                    ),
                )?
                .1,
            );
        }
        let (positive, nonunit) = match subjects.as_slice() {
            [subject] => {
                let valid = match subject {
                    Fact::AtomicFact(AtomicFact::LessFact(f)) => {
                        one(&f.left) && f.right.ir() == p.base.ir()
                    }
                    Fact::AtomicFact(AtomicFact::GreaterFact(f)) => {
                        one(&f.right) && f.left.ir() == p.base.ir()
                    }
                    _ => false,
                };
                if !valid {
                    return Err(LeanCompileError::unsupported("LogIdentity/BaseAboveOne"));
                }
                let guard = format!("(Litex.logGuardAbove {term}.val.base {})", children[0]);
                (format!("{guard}.1"), format!("{guard}.2"))
            }
            [positive, nonunit] => {
                let valid = match positive {
                    Fact::AtomicFact(AtomicFact::LessFact(f)) => {
                        is_exact_zero(&f.left) && f.right.ir() == p.base.ir()
                    }
                    Fact::AtomicFact(AtomicFact::GreaterFact(f)) => {
                        is_exact_zero(&f.right) && f.left.ir() == p.base.ir()
                    }
                    _ => false,
                };
                if !valid {
                    return Err(LeanCompileError::unsupported("LogIdentity/BasePositive"));
                }
                let nonunit = match nonunit {
                    Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                        if f.left.ir() == p.base.ir() && one(&f.right) =>
                    {
                        children[1].clone()
                    }
                    Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                        if f.right.ir() == p.base.ir() && one(&f.left) =>
                    {
                        format!("(fun h => {} h.symm)", children[1])
                    }
                    Fact::AtomicFact(AtomicFact::LessFact(f))
                        if f.left.ir() == p.base.ir() && one(&f.right) =>
                    {
                        format!(
                            "(Litex.ltNotSame {term}.val.base (Litex.number 1) {})",
                            children[1]
                        )
                    }
                    _ => return Err(LeanCompileError::unsupported("LogIdentity/BaseNonunit")),
                };
                (children[0].clone(), nonunit)
            }
            _ => return Err(LeanCompileError::unsupported("LogIdentity/Requirements")),
        };
        let law = if self_argument { "logSelf" } else { "logOne" };
        let proof = format!("(Litex.{law} {term} rfl {positive} {nonunit})");
        Ok(if reversed {
            format!("{proof}.symm")
        } else {
            proof
        })
    }
}
