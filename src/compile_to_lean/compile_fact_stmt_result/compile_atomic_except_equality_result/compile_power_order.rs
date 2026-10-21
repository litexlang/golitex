use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_power_weak_order_strategy(
        &self,
        goal: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left_obj, right_obj, strict) = source_order_oriented(goal)?;
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(right)),
        ) = (left_obj, right_obj)
        else {
            return Err(LeanCompileError::unsupported("PowerOrder/Constructor"));
        };
        if strict
            || left.exponent.ir() != right.exponent.ir()
            || requirements.len() != 3
            || proofs.len() != 3
        {
            return Err(LeanCompileError::unsupported("PowerOrder/Requirements"));
        }
        let n = closed_integer(&left.exponent)
            .filter(|n| *n > 0)
            .ok_or_else(|| LeanCompileError::unsupported("PowerOrder/PositiveLiteralExponent"))?;
        if membership_subject(&requirements[0], &left.exponent)? != StandardSet::NPos {
            return Err(LeanCompileError::unsupported("PowerOrder/ExponentSubject"));
        }
        for (requirement, expected_left, expected_right) in [
            (&requirements[1], None, left.base.as_ref()),
            (
                &requirements[2],
                Some(left.base.as_ref()),
                right.base.as_ref(),
            ),
        ] {
            let Fact::AtomicFact(atomic) = requirement else {
                return Err(LeanCompileError::unsupported("PowerOrder/Premise"));
            };
            let (a, b, strict) = source_order_oriented(atomic)?;
            if strict
                || b.ir() != expected_right.ir()
                || match expected_left {
                    Some(expected) => a.ir() != expected.ir(),
                    None => !is_exact_zero(a),
                }
            {
                return Err(LeanCompileError::unsupported("PowerOrder/Premise"));
            }
        }
        let mut children = Vec::new();
        for (index, (requirement, proof)) in requirements.iter().zip(proofs).enumerate() {
            if *requirement != source_subject(proof)? {
                return Err(LeanCompileError::unsupported("PowerOrder/ChildSubject"));
            }
            children.push(
                self.compile_verify(proof, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(3)?;
        let left_term = self.compile_object_reference(left_obj, &complete)?;
        let right_term = self.compile_object_reference(right_obj, &complete)?;
        let he_left = self.compile_literal_natural_identity(&left.exponent, n, &complete)?;
        let he_right = self.compile_literal_natural_identity(&right.exponent, n, &complete)?;
        Ok(format!("(by\n  let _left := {left_term}\n  let _right := {right_term}\n  have _positiveExponent : Litex.In _left.val.exponent Litex.NPos := {}\n  exact Litex.powStructuralLe _left _right ({n} : ℕ) {he_left} {he_right} {} {}\n)", children[0], children[1], children[2]))
    }

    pub(in crate::compile_to_lean) fn compile_power_positive(
        &self,
        goal: &AtomicFact,
        positive: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (zero, value, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = value else {
            return Err(LeanCompileError::new(
                "PositivePower/Constructor",
                "The selected power rule has another source constructor.",
            ));
        };
        if !strict || !is_exact_zero(zero) {
            return Err(LeanCompileError::new(
                "PositivePower/Goal",
                "The selected power rule must prove the exact strict zero lower bound.",
            ));
        }
        let subject = source_subject(positive)?;
        let Fact::AtomicFact(atomic) = &subject else {
            return Err(LeanCompileError::new(
                "PositivePower/ChildFamily",
                "The actual child is not an atomic positive-base result.",
            ));
        };
        let (zero, base, strict) = source_order_oriented(atomic)?;
        if !strict || !is_exact_zero(zero) || base.ir() != power.base.ir() {
            return Err(LeanCompileError::new(
                "PositivePower/ChildSubject",
                "The actual positivity child belongs to another base or is weak.",
            ));
        }
        let positive = self.compile_verify(positive, position)?.1;
        Ok(format!(
            "(Litex.powStructuralPositiveOfPositive {} {positive})",
            self.compile_object_reference(value, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_even_power_positive(
        &self,
        goal: &AtomicFact,
        real: &VerifyFactResult,
        nonzero: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (zero, value, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = value else {
            return Err(LeanCompileError::unsupported(
                "PositiveEvenPower/Constructor",
            ));
        };
        if !strict || !is_exact_zero(zero) {
            return Err(LeanCompileError::new(
                "PositiveEvenPower/Goal",
                "The selected even-power rule must prove strict positivity.",
            ));
        }
        let n = closed_integer(&power.exponent)
            .filter(|n| *n > 0 && n % 2 == 0)
            .ok_or_else(|| {
                LeanCompileError::new(
                    "PositiveEvenPower/Exponent",
                    "The original exponent must be a positive even integer literal.",
                )
            })?;
        if !matches!(power.exponent.as_ref(), Obj::Literal(Literal::Number(_)))
            || membership_subject(&source_subject(real)?, &power.base)? != StandardSet::R
        {
            return Err(LeanCompileError::new("PositiveEvenPower/Base", "The actual child must prove this exact real base and the source exponent must remain literal."));
        }
        ensure_nonzero_subject(&source_subject(nonzero)?, &power.base)?;
        let real = self.compile_verify(real, position)?.1;
        let nonzero = self.compile_verify(nonzero, position)?.1;
        let he = self.compile_literal_natural_identity(&power.exponent, n, position)?;
        Ok(format!("(Litex.powStructuralPositiveOfEven {} {real} ({n} : ℕ) {he} (by norm_num) (by norm_num) {nonzero})", self.compile_object_reference(value, position)?))
    }

    pub(in crate::compile_to_lean) fn compile_literal_natural_identity(
        &self,
        exponent: &Obj,
        n: i128,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if n < 0
            || !matches!(exponent, Obj::Literal(Literal::Number(_)))
            || closed_integer(exponent) != Some(n)
        {
            return Err(LeanCompileError::new(
                "Power/LiteralIdentity",
                "The selected native exponent must equal the original natural literal.",
            ));
        }
        let observation = self.compile_numeric_observation(exponent, position)?;
        Ok(format!("(Litex.NativeBridge.sameOfDenoteNumber {} (Litex.number (M := M) (({n} : ℕ) : ℂ)) {} (({n} : ℕ) : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (({n} : ℕ) : ℂ)) (by norm_num))", self.compile_object_reference(exponent, position)?, observation.0, observation.1))
    }

    pub(in crate::compile_to_lean) fn compile_literal_one_identity(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(object, Obj::Literal(Literal::Number(_))) || closed_integer(object) != Some(1)
        {
            return Err(LeanCompileError::new(
                "Order/LiteralOneIdentity",
                "The selected original closed endpoint must remain the literal one.",
            ));
        }
        let observation = self.compile_numeric_observation(object, position)?;
        Ok(format!("(Litex.NativeBridge.sameOfDenoteNumber {} (Litex.number (M := M) (1 : ℂ)) {} (1 : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))", self.compile_object_reference(object, position)?, observation.0, observation.1))
    }
}
