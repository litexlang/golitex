use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

pub(in crate::compile_to_lean) fn rounding_argument(object: &Obj, ceiling: bool) -> Option<&Obj> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(p)) if !ceiling => Some(&p.arg),
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(p)) if ceiling => Some(&p.arg),
        _ => None,
    }
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_rounding_wd(
        &self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        ceiling: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 1 || requirements.len() != 1 {
            return Err(LeanCompileError::unsupported("WD/RoundingStages"));
        }
        ensure_object(argument, &children[0])?;
        if membership_subject(&source_subject(&requirements[0])?, argument)? != StandardSet::R {
            return Err(LeanCompileError::unsupported("WD/RoundingRealDomain"));
        }
        let term = self.compile_wd(
            &children[0],
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let member = self.compile_wd_requirement(
            &requirements[0],
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let name = if ceiling { "ceil" } else { "floor" };
        Ok(format!("(Litex.{name} {term} {member})"))
    }

    pub(in crate::compile_to_lean) fn numeric_rounding_wd(
        &self,
        wd: &ObjWellDefinedProof,
        children: &[Box<ObjWellDefinedProof>],
        ceiling: bool,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        if rounding_argument(wd.obj(), ceiling).is_none() {
            return Err(LeanCompileError::unsupported(
                "Rounding/ObservationConstructor",
            ));
        }
        let term = self.compile_wd(wd, position)?;
        let setup = format!(
            "let _round := {term};\nlet _member : Litex.In _round Litex.C := Litex.integerToComplex _round (Litex.roundingInZ _round);"
        );
        if let Some(value) = EvalRational::from_obj(wd.obj()) {
            let child = self.numeric_wd(
                &children[0],
                &SourcePosition {
                    before: 0,
                    ..*position
                },
            )?;
            let exact = child
                .3
                .as_ref()
                .ok_or_else(|| LeanCompileError::unsupported("Rounding/ClosedArgument"))?;
            let real = exact_rational_literal(exact, "ℝ")?;
            let value_term = exact_rational_literal(&value, "ℂ")?;
            let integer = value
                .to_i128_if_integer()
                .ok_or_else(|| LeanCompileError::unsupported("Rounding/ClosedInteger"))?;
            let name = if ceiling { "ceil" } else { "floor" };
            let denotation = format!(
                "({}).trans (congrArg M.number (by norm_num : {} = (({real} : ℝ) : ℂ)))",
                child.1, child.0
            );
            return Ok((
                value_term.clone(),
                format!(
                    "({setup}\n(Litex.roundingDenoteReal _round {real} ({denotation})).trans (congrArg M.number (by have _value : Int.{name} {real} = ({integer} : ℤ) := Int.{name}_eq_iff.mpr ⟨by norm_num, by norm_num⟩; change ((Int.{name} {real} : ℤ) : ℂ) = {value_term}; rw [_value]; norm_num)))"
                ),
                format!("({setup}\n_member)"),
                Some(value),
            ));
        }
        Ok((
            format!("({setup}\nLitex.NativeBridge.asComplex _round _member)"),
            format!("({setup}\nLitex.NativeBridge.asComplex_spec _round _member)"),
            format!("({setup}\n_member)"),
            None,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_rounding_integer_identity(
        &self,
        goal: &EqualFact,
        ceiling: bool,
        nested: bool,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let matches = |object: &Obj, target: &Obj| {
            let argument = rounding_argument(object, ceiling).and_then(|arg| {
                if nested {
                    rounding_argument(arg, !ceiling)
                } else {
                    Some(arg)
                }
            });
            argument.is_some_and(|arg| arg.ir() == target.ir())
        };
        let (object, target, reversed) = if matches(&goal.left, &goal.right) {
            (&goal.left, &goal.right, false)
        } else if matches(&goal.right, &goal.left) {
            (&goal.right, &goal.left, true)
        } else {
            return Err(LeanCompileError::unsupported("Rounding/IntegerSubject"));
        };
        let [requirement] = requirements else {
            return Err(LeanCompileError::unsupported("Rounding/IntegerRequirement"));
        };
        if membership_subject(&source_subject(requirement)?, target)? != StandardSet::Z {
            return Err(LeanCompileError::unsupported("Rounding/IntegerCarrier"));
        }
        let member = self.compile_verify(requirement, position)?.1;
        let term = self.compile_object_reference(object, position)?;
        let proof = if nested {
            format!(
                "(Litex.roundingOfInteger _round (Litex.roundingInZ _round.val.arg)).trans (Litex.roundingOfInteger _round.val.arg {member})"
            )
        } else {
            format!("Litex.roundingOfInteger _round {member}")
        };
        let symmetric = if reversed { ".symm" } else { "" };
        Ok(format!(
            "(by\n  let _round := {term}\n  exact ({proof}){symmetric}\n)"
        ))
    }

    pub(in crate::compile_to_lean) fn compile_rounding_bound(
        &self,
        goal: &AtomicFact,
        ceiling: bool,
        strict_rule: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict != strict_rule {
            return Err(LeanCompileError::unsupported("Rounding/BoundStrength"));
        }
        let (object, argument, rounded) = match (ceiling, strict_rule) {
            (false, false) => (low, high, low),
            (true, false) => (high, low, high),
            (false, true) => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = high else {
                    return Err(LeanCompileError::unsupported("Rounding/BoundConstructor"));
                };
                if !matches!(sum.right.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
                {
                    return Err(LeanCompileError::unsupported("Rounding/BoundUnit"));
                }
                (high, low, sum.left.as_ref())
            }
            (true, true) => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Sub(diff)) = low else {
                    return Err(LeanCompileError::unsupported("Rounding/BoundConstructor"));
                };
                if !matches!(diff.right.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
                {
                    return Err(LeanCompileError::unsupported("Rounding/BoundUnit"));
                }
                (low, high, diff.left.as_ref())
            }
        };
        if !rounding_argument(rounded, ceiling).is_some_and(|arg| arg.ir() == argument.ir()) {
            return Err(LeanCompileError::unsupported("Rounding/BoundArgument"));
        }
        let name = match (ceiling, strict_rule) {
            (false, false) => "floorLeArgument",
            (true, false) => "argumentLeCeil",
            (false, true) => "floorStrictUpper",
            (true, true) => "ceilStrictLower",
        };
        let unit = if strict_rule {
            " (Litex.sameRefl (Litex.number (M := M) 1))"
        } else {
            ""
        };
        Ok(format!(
            "(Litex.{name} {}{unit})",
            self.compile_object_reference(object, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_rounding_monotone(
        &self,
        goal: &AtomicFact,
        ceiling: bool,
        argument_order: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (Some(left), Some(right)) = (
            rounding_argument(low, ceiling),
            rounding_argument(high, ceiling),
        ) else {
            return Err(LeanCompileError::unsupported(
                "Rounding/MonotoneConstructor",
            ));
        };
        let Fact::AtomicFact(subject) = source_subject(argument_order)? else {
            return Err(LeanCompileError::unsupported("Rounding/OrderPremise"));
        };
        let (a, b, premise_strict) = source_order_oriented(&subject)?;
        if strict || premise_strict || a.ir() != left.ir() || b.ir() != right.ir() {
            return Err(LeanCompileError::unsupported("Rounding/OrderPremise"));
        }
        let order = self
            .compile_verify(argument_order, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        Ok(format!(
            "(Litex.roundingMonotone {} {} {order})",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(high, &complete)?
        ))
    }
}
