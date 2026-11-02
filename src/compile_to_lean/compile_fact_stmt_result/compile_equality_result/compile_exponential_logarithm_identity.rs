use crate::compile_to_lean::helper::{source_order_oriented, source_subject, is_exact_zero};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_exponential_logarithm_identities::ExponentialLogarithmIdentityProof as Identity;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_exponential_logarithm_identity(
        &self,
        fact: &EqualFact,
        proof: &Identity,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            Identity::ExpDifference(_) => self.compile_exp_log_binary(fact, 0, position),
            Identity::LnProduct(_) => self.compile_exp_log_binary(fact, 1, position),
            Identity::LnQuotient(_) => self.compile_exp_log_binary(fact, 2, position),
            Identity::ExpInjective(p) => self.compile_exp_log_injective(
                fact,
                false,
                [&p.left_real, &p.right_real],
                &p.image_equality,
                position,
            ),
            Identity::LnInjective(p) => self.compile_exp_log_injective(
                fact,
                true,
                [&p.left_positive, &p.right_positive],
                &p.image_equality,
                position,
            ),
            Identity::LogFromKnownPower(p) => {
                for (object, exponent, reverse) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    let Obj::ExpLogOperator(ExpLogOperator::Log(log)) = object else {
                        continue;
                    };
                    self.exp_log_member(&p.exponent_integer, exponent, StandardSet::Z)?;
                    let base = self.compile_log_guard(&log.base, &p.base_proof, position)?;
                    let integer = self.compile_verify(&p.exponent_integer, position)?.1;
                    // The producer searches exactly base^exponent = argument.
                    // This view gives that recorded search its original subjects;
                    // it is never stored or turned into a new verification result.
                    let image = EqualFact {
                        fact_id: fact.fact_id,
                        left: Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                            base: log.base.clone(),
                            exponent: Box::new(exponent.clone()),
                        })),
                        right: log.arg.as_ref().clone(),
                        line_file: None,
                    };
                    let image =
                        self.compile_equality_search(&image, &p.power_equality, position)?;
                    return Ok(format!(
                        "(Litex.logarithmFromPowerValue {} {} {base} {integer} {image}){}",
                        self.compile_object_reference(object, position)?,
                        self.compile_object_reference(exponent, position)?,
                        if reverse { ".symm" } else { "" }
                    ));
                }
                Err(invalid("LogPowerSubject"))
            }
            Identity::PowerFromKnownLog(p) => {
                for (object, argument, reverse) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = object else {
                        continue;
                    };
                    self.exp_log_member(&p.exponent_integer, &power.exponent, StandardSet::Z)?;
                    let Fact::AtomicFact(positive) = source_subject(&p.argument_positive)? else {
                        return Err(invalid("PositiveArgumentFamily"));
                    };
                    let (zero, subject, strict) = source_order_oriented(&positive)?;
                    if !strict || !is_exact_zero(zero) || subject.ir() != argument.ir() {
                        return Err(invalid("PositiveArgumentSubject"));
                    }
                    let base = self.compile_log_guard(&power.base, &p.base_proof, position)?;
                    let positive = self.compile_verify(&p.argument_positive, position)?.1;
                    let integer = self.compile_verify(&p.exponent_integer, position)?.1;
                    let log = Obj::ExpLogOperator(ExpLogOperator::Log(Log {
                        base: power.base.clone(),
                        arg: Box::new(argument.clone()),
                    }));
                    let image = EqualFact {
                        fact_id: fact.fact_id,
                        left: log.clone(),
                        right: power.exponent.as_ref().clone(),
                        line_file: None,
                    };
                    let image =
                        self.compile_equality_search(&image, &p.logarithm_equality, position)?;
                    return Ok(format!("(Litex.powerFromLogarithmValue {} {} {base} {positive} {integer} {image}){}",
                        self.compile_object_reference(&log,position)?,self.compile_object_reference(&power.exponent,position)?,if reverse {".symm"}else{""}));
                }
                Err(invalid("PowerLogSubject"))
            }
        }
    }

    fn exp_log_member(
        &self,
        proof: &VerifyFactResult,
        object: &Obj,
        set: StandardSet,
    ) -> Result<(), LeanCompileError> {
        if matches!(source_subject(proof)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==object.ir() && f.set==Obj::StandardSet(set))
        {
            Ok(())
        } else {
            Err(invalid("OriginalMembershipSubject"))
        }
    }

    fn compile_exp_log_injective(
        &self,
        fact: &EqualFact,
        logarithm: bool,
        children: [&VerifyFactResult; 2],
        image: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let set = if logarithm {
            StandardSet::RPos
        } else {
            StandardSet::R
        };
        self.exp_log_member(children[0], &fact.left, set.clone())?;
        self.exp_log_member(children[1], &fact.right, set)?;
        let left = self.compile_verify(children[0], position)?.1;
        let right = self.compile_verify(children[1], position)?.1;
        let wrap = |arg: &Obj| {
            if logarithm {
                Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
                    arg: Box::new(arg.clone()),
                }))
            } else {
                Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
                    arg: Box::new(arg.clone()),
                }))
            }
        };
        let subject = EqualFact {
            fact_id: fact.fact_id,
            left: wrap(&fact.left),
            right: wrap(&fact.right),
            line_file: None,
        };
        let image = self.compile_equality_search(&subject, image, position)?;
        let law = if logarithm {
            "logarithmInjectiveValue"
        } else {
            "exponentialInjectiveValue"
        };
        Ok(format!(
            "(Litex.{law} {} {} {left} {right} {image})",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?
        ))
    }

    fn compile_exp_log_binary(
        &self,
        fact: &EqualFact,
        kind: u8,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (unary, other, reverse) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let (a, b) = match (unary, kind) {
                (Obj::ExpLogOperator(ExpLogOperator::Exp(p)), 0) => match p.arg.as_ref() {
                    Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => (&p.left, &p.right),
                    _ => continue,
                },
                (Obj::ExpLogOperator(ExpLogOperator::Ln(p)), 1) => match p.arg.as_ref() {
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => (&p.left, &p.right),
                    _ => continue,
                },
                (Obj::ExpLogOperator(ExpLogOperator::Ln(p)), 2) => match p.arg.as_ref() {
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => (&p.left, &p.right),
                    _ => continue,
                },
                _ => continue,
            };
            let (left, right) = match (other, kind) {
                (Obj::ArithmeticOperator(ArithmeticOperator::Div(p)), 0) => (&p.left, &p.right),
                (Obj::ArithmeticOperator(ArithmeticOperator::Add(p)), 1) => (&p.left, &p.right),
                (Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)), 2) => (&p.left, &p.right),
                _ => continue,
            };
            if !argument(left, kind).is_some_and(|x| x.ir() == a.ir())
                || !argument(right, kind).is_some_and(|x| x.ir() == b.ir())
            {
                continue;
            }
            let law = match kind {
                0 => "exponentialDifferenceValue",
                1 => "logarithmProductValue",
                _ => "logarithmQuotientValue",
            };
            return Ok(format!("(let _exp_log_pair := {}; (Litex.{law} _exp_log_pair.val.left _exp_log_pair.val.right){})",self.compile_object_reference(other,position)?,if reverse {".symm"}else{""}));
        }
        Err(invalid("OriginalBinarySubject"))
    }
}

fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ExponentialLogarithm/{part}"))
}

fn argument(object: &Obj, kind: u8) -> Option<&Obj> {
    match (object, kind) {
        (Obj::ExpLogOperator(ExpLogOperator::Exp(p)), 0) => Some(&p.arg),
        (Obj::ExpLogOperator(ExpLogOperator::Ln(p)), 1 | 2) => Some(&p.arg),
        _ => None,
    }
}
