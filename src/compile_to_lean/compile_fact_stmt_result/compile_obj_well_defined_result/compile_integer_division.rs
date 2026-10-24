use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn integer_division_arguments(
    object: &Obj,
    quotient: bool,
) -> Option<(&Obj, &Obj)> {
    match object {
        Obj::IntegerOperator(IntegerOperator::Quot(p)) if quotient => Some((&p.left, &p.right)),
        Obj::IntegerOperator(IntegerOperator::Mod(p)) if !quotient => Some((&p.left, &p.right)),
        _ => None,
    }
}

fn is_one(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_integer_division_wd(
        &self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        quotient: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        // The verifier derives this divisor's nonzero property from its gcd
        // construction, rather than returning a separate requirement fact.
        let gcd_modulus =
            !quotient && matches!(right, Obj::IntegerOperator(IntegerOperator::Gcd(_)));
        if children.len() != 2 || requirements.len() != if quotient || gcd_modulus { 2 } else { 3 }
        {
            return Err(LeanCompileError::unsupported("WD/IntegerDivisionStages"));
        }
        ensure_object(left, &children[0])?;
        ensure_object(right, &children[1])?;
        if membership_subject(&source_subject(&requirements[0])?, left)? != StandardSet::Z
            || membership_subject(&source_subject(&requirements[1])?, right)?
                != if quotient {
                    StandardSet::NPos
                } else {
                    StandardSet::Z
                }
        {
            return Err(LeanCompileError::unsupported("WD/IntegerDivisionDomain"));
        }
        if !quotient && !gcd_modulus {
            ensure_nonzero_subject(&source_subject(&requirements[2])?, right)?;
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
            args.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: 2 + index,
                    ..*position
                },
            )?);
        }
        if gcd_modulus {
            args.push(format!("(Litex.gcdNonzero {})", args[1]));
        }
        let name = if quotient { "quot" } else { "mod" };
        Ok(format!("(Litex.{name} {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn numeric_integer_division_wd(
        &self,
        wd: &ObjWellDefinedProof,
        children: &[Box<ObjWellDefinedProof>],
        quotient: bool,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        if children.len() != 2 || integer_division_arguments(wd.obj(), quotient).is_none() {
            return Err(LeanCompileError::unsupported(
                "IntegerDivision/ObservationConstructor",
            ));
        }
        let term = self.compile_wd(wd, position)?;
        let name = if quotient { "quot" } else { "mod" };
        let setup = format!("let _intop := {term};\nlet _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.{name}InZ _intop);");
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
                    .ok_or_else(|| {
                        LeanCompileError::unsupported("IntegerDivision/ClosedInteger")
                    })?;
                arguments.push(format!("({integer} : ℤ)"));
                denotations.push(format!(
                    "(({}).trans (congrArg M.number (by norm_num : {} = (({integer} : ℤ) : ℂ))))",
                    observation.1, observation.0
                ));
            }
            let exact = exact_rational_literal(&value, "ℂ")?;
            return Ok((exact.clone(), format!(
                "({setup}\n(Litex.{name}DenoteInt _intop {} {} {} {}).trans (congrArg M.number (by norm_num)))",
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

    pub(in crate::compile_to_lean) fn compile_quot_identity(
        &self,
        goal: &EqualFact,
        self_division: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, target, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Some((left, right)) = integer_division_arguments(object, true) else {
                continue;
            };
            if if self_division {
                left.ir() != right.ir() || !is_one(target)
            } else {
                left.ir() != target.ir() || !is_one(right)
            } {
                continue;
            }
            let term = self.compile_object_reference(object, position)?;
            let proof = if self_division {
                let [requirement] = requirements else {
                    return Err(LeanCompileError::unsupported("Quot/IdentityPremise"));
                };
                if membership_subject(&source_subject(requirement)?, right)? != StandardSet::NPos {
                    return Err(LeanCompileError::unsupported("Quot/IdentityPremise"));
                }
                let premise = self.compile_verify(requirement, position)?.1;
                format!("Litex.quotSelfOne _quot (Litex.sameRefl _quot.val.left) {premise}")
            } else {
                if !requirements.is_empty() {
                    return Err(LeanCompileError::unsupported("Quot/IdentityPremise"));
                }
                "Litex.quotByOne _quot (Litex.sameRefl (Litex.number (M := M) 1))".into()
            };
            let symm = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(by\n  let _quot := {term}\n  exact ({proof}){symm}\n)"
            ));
        }
        Err(LeanCompileError::unsupported("Quot/IdentitySubject"))
    }

    pub(in crate::compile_to_lean) fn compile_quot_decomposition(
        &self,
        goal: &EqualFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (dividend, expression, reversed) in [
            (&goal.left, &goal.right, false),
            (&goal.right, &goal.left, true),
        ] {
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = expression else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = sum.left.as_ref()
            else {
                continue;
            };
            let Some((a, b)) = integer_division_arguments(&sum.right, false) else {
                continue;
            };
            if a.ir() != dividend.ir() {
                continue;
            }
            for (quotient, divisor, quotient_first) in [
                (&product.left, &product.right, true),
                (&product.right, &product.left, false),
            ] {
                let Some((q_a, q_b)) = integer_division_arguments(quotient, true) else {
                    continue;
                };
                if q_a.ir() != a.ir() || q_b.ir() != b.ir() || divisor.ir() != b.ir() {
                    continue;
                }
                let term = self.compile_object_reference(quotient, position)?;
                let symm = if reversed { ".symm" } else { "" };
                return Ok(format!(
                    "(Litex.quotDecomposition {term} {quotient_first}){symm}"
                ));
            }
        }
        Err(LeanCompileError::unsupported("Quot/DecompositionSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_mod_bound(
        &self,
        goal: &AtomicFact,
        strict_rule: bool,
        dividend: &VerifyFactResult,
        modulus: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let object = if strict_rule { low } else { high };
        let Some((a, b)) = integer_division_arguments(object, false) else {
            return Err(LeanCompileError::unsupported("Mod/BoundSubject"));
        };
        if strict != strict_rule
            || (if strict_rule {
                b.ir() != high.ir()
            } else {
                !is_exact_zero(low)
            })
            || membership_subject(&source_subject(dividend)?, a)? != StandardSet::Z
            || membership_subject(&source_subject(modulus)?, b)? != StandardSet::NPos
        {
            return Err(LeanCompileError::unsupported("Mod/BoundPremises"));
        }
        let ha = self
            .compile_verify(dividend, &position.atomic_search_prior(0)?)?
            .1;
        let hb = self
            .compile_verify(modulus, &position.atomic_search_prior(1)?)?
            .1;
        let term = self.compile_object_reference(object, &position.atomic_search_prior(2)?)?;
        let name = if strict_rule {
            "modStrictUpper"
        } else {
            "modNonnegative"
        };
        Ok(format!("(Litex.{name} {term} {ha} {hb})"))
    }
}
