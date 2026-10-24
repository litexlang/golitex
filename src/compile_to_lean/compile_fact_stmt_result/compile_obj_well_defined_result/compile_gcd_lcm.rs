use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn gcd_lcm_arguments(
    object: &Obj,
    least: bool,
) -> Option<(&Obj, &Obj)> {
    match object {
        Obj::IntegerOperator(IntegerOperator::Gcd(p)) if !least => Some((&p.left, &p.right)),
        Obj::IntegerOperator(IntegerOperator::Lcm(p)) if least => Some((&p.left, &p.right)),
        _ => None,
    }
}

fn abs_argument(object: &Obj) -> Option<&Obj> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) => Some(&p.arg),
        _ => None,
    }
}

// Normalize only the certificate the constructor actually returned. An Or
// certificate does not choose a nonzero operand.
fn gcd_guard(
    subject: &Fact,
    left: &Obj,
    right: &Obj,
    proof: &str,
) -> Result<String, LeanCompileError> {
    if let Fact::OrFact(disjunction) = subject {
        if let [first, second] = disjunction.facts.as_slice() {
            let first = crate::ast::fact::and_chain_as_fact(first);
            let second = crate::ast::fact::and_chain_as_fact(second);
            if ensure_nonzero_subject(&first, left).is_ok()
                && ensure_nonzero_subject(&second, right).is_ok()
            {
                return Ok(proof.into());
            }
            if ensure_nonzero_subject(&first, right).is_ok()
                && ensure_nonzero_subject(&second, left).is_ok()
            {
                return Ok(format!("(Or.symm {proof})"));
            }
        }
    } else if ensure_nonzero_subject(subject, left).is_ok() {
        return Ok(format!("(Or.inl {proof})"));
    } else if ensure_nonzero_subject(subject, right).is_ok() {
        return Ok(format!("(Or.inr {proof})"));
    }
    Err(LeanCompileError::unsupported("WD/GcdNonzeroPair"))
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_gcd_lcm_wd(
        &self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        least: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 2 || requirements.len() != if least { 2 } else { 3 } {
            return Err(LeanCompileError::unsupported("WD/GcdLcmStages"));
        }
        ensure_object(left, &children[0])?;
        ensure_object(right, &children[1])?;
        if membership_subject(&source_subject(&requirements[0])?, left)? != StandardSet::Z
            || membership_subject(&source_subject(&requirements[1])?, right)? != StandardSet::Z
        {
            return Err(LeanCompileError::unsupported("WD/GcdLcmDomain"));
        }
        if !least {
            gcd_guard(&source_subject(&requirements[2])?, left, right, "")?;
        }
        let mut args = Vec::new();
        for (index, child) in children.iter().enumerate() {
            args.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, requirement) in requirements.iter().enumerate() {
            let proof = self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: 2 + index,
                    ..*position
                },
            )?;
            args.push(if index == 2 {
                gcd_guard(&source_subject(requirement)?, left, right, &proof)?
            } else {
                proof
            });
        }
        let name = if least { "lcm" } else { "gcd" };
        Ok(format!("(Litex.{name} {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn numeric_gcd_lcm_wd(
        &self,
        wd: &ObjWellDefinedProof,
        children: &[Box<ObjWellDefinedProof>],
        least: bool,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        if children.len() != 2 || gcd_lcm_arguments(wd.obj(), least).is_none() {
            return Err(LeanCompileError::unsupported(
                "GcdLcm/ObservationConstructor",
            ));
        }
        let term = self.compile_wd(wd, position)?;
        let name = if least { "lcm" } else { "gcd" };
        let setup = format!("let _intop := {term};\nlet _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.{name}InN _intop);");
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let mut arguments = Vec::new();
            let mut denotations = Vec::new();
            for (index, child) in children.iter().enumerate() {
                let observation = self.numeric_wd(
                    child,
                    &SourcePosition {
                        before: index,
                        ..*position
                    },
                )?;
                let integer = observation
                    .3
                    .as_ref()
                    .and_then(EvalRational::to_i128_if_integer)
                    .ok_or_else(|| LeanCompileError::unsupported("GcdLcm/ClosedInteger"))?;
                arguments.push(format!("({integer} : ℤ)"));
                denotations.push(format!(
                    "(({}).trans (congrArg M.number (by norm_num : {} = (({integer} : ℤ) : ℂ))))",
                    observation.1, observation.0
                ));
            }
            let exact = exact_rational_literal(&value, "ℂ")?;
            return Ok((exact.clone(), format!(
                "({setup}\n(Litex.{name}DenoteInt _intop {} {} {} {}).trans (congrArg M.number (by norm_num [Int.{name}_eq_natAbs_{name}_natAbs])))",
                arguments[0], arguments[1], denotations[0], denotations[1]),
                format!("({setup}\n_member)"), Some(value)));
        }
        Ok((
            format!("({setup}\nLitex.NativeBridge.asComplex _intop _member)"),
            format!("({setup}\nLitex.NativeBridge.asComplex_spec _intop _member)"),
            format!("({setup}\n_member)"),
            None,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_gcd_lcm_commutative(
        &self,
        goal: &EqualFact,
        least: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (Some((a, b)), Some((c, d))) = (
            gcd_lcm_arguments(&goal.left, least),
            gcd_lcm_arguments(&goal.right, least),
        ) else {
            return Err(LeanCompileError::unsupported(
                "GcdLcm/CommutativeConstructor",
            ));
        };
        if a.ir() != d.ir() || b.ir() != c.ir() {
            return Err(LeanCompileError::unsupported("GcdLcm/CommutativeArguments"));
        }
        let name = if least { "lcm" } else { "gcd" };
        Ok(format!(
            "(Litex.{name}Commutative {})",
            self.compile_object_reference(&goal.left, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_gcd_lcm_self_abs(
        &self,
        goal: &EqualFact,
        least: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, target, reverse) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let (Some((a, b)), Some(arg)) =
                (gcd_lcm_arguments(object, least), abs_argument(target))
            else {
                continue;
            };
            if a.ir() != b.ir() || a.ir() != arg.ir() {
                continue;
            }
            let name = if least { "lcm" } else { "gcd" };
            let term = self.compile_object_reference(object, position)?;
            let symm = if reverse { ".symm" } else { "" };
            return Ok(format!("(by\n  let _intop := {term}\n  exact (Litex.{name}SelfAbs _intop (Litex.sameRefl _intop.val.left)){symm}\n)"));
        }
        Err(LeanCompileError::unsupported("GcdLcm/SelfAbsSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_gcd_zero_abs(
        &self,
        goal: &EqualFact,
        left_zero: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, target, reverse) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let (Some((a, b)), Some(arg)) =
                (gcd_lcm_arguments(object, false), abs_argument(target))
            else {
                continue;
            };
            let (zero, nonzero) = if left_zero { (a, b) } else { (b, a) };
            if !is_exact_zero(zero) || nonzero.ir() != arg.ir() {
                continue;
            }
            let [requirement] = requirements else {
                return Err(LeanCompileError::unsupported("Gcd/ZeroIdentityPremise"));
            };
            ensure_nonzero_subject(&source_subject(requirement)?, nonzero)?;
            let proof = self.compile_verify(requirement, position)?.1;
            let term = self.compile_object_reference(object, position)?;
            let side = if left_zero { "Left" } else { "Right" };
            let symm = if reverse { ".symm" } else { "" };
            return Ok(format!("(Litex.gcd{side}ZeroAbs {term} (Litex.sameRefl (Litex.number (M := M) 0)) {proof}){symm}"));
        }
        Err(LeanCompileError::unsupported("Gcd/ZeroIdentitySubject"))
    }

    pub(in crate::compile_to_lean) fn compile_gcd_euclidean_step(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use super::compile_integer_division::integer_division_arguments;
        for (object, target, reverse) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let (Some((a, b)), Some((first, remainder))) = (
                gcd_lcm_arguments(object, false),
                gcd_lcm_arguments(target, false),
            ) else {
                continue;
            };
            let Some((r_a, r_b)) = integer_division_arguments(remainder, false) else {
                continue;
            };
            if b.ir() != first.ir() || a.ir() != r_a.ir() || b.ir() != r_b.ir() {
                continue;
            }
            let symm = if reverse { ".symm" } else { "" };
            return Ok(format!(
                "(Litex.gcdEuclideanStep {}){symm}",
                self.compile_object_reference(object, position)?
            ));
        }
        Err(LeanCompileError::unsupported("Gcd/EuclideanSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_gcd_lcm_product(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (product, target, reverse) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = product else {
                continue;
            };
            let Some(Obj::ArithmeticOperator(ArithmeticOperator::Mul(inner))) =
                abs_argument(target)
            else {
                continue;
            };
            for (gcd, lcm, first) in [
                (&product.left, &product.right, true),
                (&product.right, &product.left, false),
            ] {
                let (Some((a, b)), Some((c, d))) =
                    (gcd_lcm_arguments(gcd, false), gcd_lcm_arguments(lcm, true))
                else {
                    continue;
                };
                if a.ir() != c.ir() || b.ir() != d.ir() {
                    continue;
                }
                let reverse_args = if inner.left.ir() == a.ir() && inner.right.ir() == b.ir() {
                    false
                } else if inner.left.ir() == b.ir() && inner.right.ir() == a.ir() {
                    true
                } else {
                    continue;
                };
                let symm = if reverse { ".symm" } else { "" };
                return Ok(format!(
                    "(Litex.gcdLcmProduct {} {first} {reverse_args}){symm}",
                    self.compile_object_reference(gcd, position)?
                ));
            }
        }
        Err(LeanCompileError::unsupported("GcdLcm/ProductSubject"))
    }
}
