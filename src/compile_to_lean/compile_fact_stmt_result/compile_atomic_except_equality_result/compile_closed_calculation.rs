use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_closed_not_equal(
        &self,
        fact: &AtomicFact,
        proof: &ClosedNotEqualCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let goal = match fact {
            AtomicFact::NotEqualFact(x) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "ClosedNotEqual/Subject",
                    "Closed inequality evidence has another fact family.",
                ))
            }
        };
        let left = EvalRational::from_obj(&goal.left)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedNotEqual/Expression"))?;
        let right = EvalRational::from_obj(&goal.right)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedNotEqual/Expression"))?;
        let matching = match &proof.values {
            ClosedValuePair::Decimal { left: a, right: b } => {
                scalar_decimal(a)? == left && scalar_decimal(b)? == right
            }
            ClosedValuePair::Rational { left: a, right: b } => a == &left && b == &right,
            ClosedValuePair::Complex {
                left_real: a,
                left_imaginary: ai,
                right_real: b,
                right_imaginary: bi,
            } => a == &left && b == &right && ai.is_zero() && bi.is_zero(),
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("ClosedNotEqual/Radical"))
            }
        };
        if !matching || left == right {
            return Err(LeanCompileError::new(
                "ClosedNotEqual/Values",
                "Closed scalar values differ from the source endpoints or are equal.",
            ));
        }
        let x = self.compile_numeric_observation(&goal.left, position)?;
        let y = self.compile_numeric_observation(&goal.right, position)?;
        Ok(format!(
            "(Litex.NativeBridge.notSameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.compile_object_reference(&goal.left, position)?,
            self.compile_object_reference(&goal.right, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        ))
    }

    pub(in crate::compile_to_lean) fn compile_closed_membership(
        &self,
        element: &Obj,
        set: &Obj,
        proof: &ClosedMembershipCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (value, target) = match proof {
            ClosedMembershipCalculationProof::StandardSet { value, set: target }
                if set.ir() == Obj::StandardSet(target.clone()).ir() =>
            {
                (value, target)
            }
            ClosedMembershipCalculationProof::StandardSet { .. } => {
                return Err(LeanCompileError::new(
                    "ClosedMembership/Set",
                    "Closed membership changes the target set.",
                ))
            }
            ClosedMembershipCalculationProof::IntegerRange { .. } => {
                return Err(LeanCompileError::unsupported(
                    "ClosedMembership/IntegerRange",
                ))
            }
        };
        // Existing literal membership is unbounded integer syntax. It must not
        // inherit the i128 bound of the new closed-arithmetic evaluator.
        if let (Obj::Literal(Literal::Number(number)), ClosedScalarValue::Decimal(recorded)) =
            (element, value)
        {
            if &number.normalized_value != recorded {
                return Err(LeanCompileError::new(
                    "ClosedMembership/Value",
                    "The literal certificate records another numeric payload.",
                ));
            }
            let native = self.compile_numeric_observation(element, position)?;
            if *target == StandardSet::C {
                return Ok(format!("(Litex.numberInC (M := M) {})", native.0));
            }
            let (bridge, representative) = match target {
                StandardSet::R => ("numberInROfEq", number_literal(number, "ℝ")?),
                StandardSet::Q => ("numberInQOfEq", number_literal(number, "ℚ")?),
                StandardSet::N | StandardSet::Z => {
                    let value = &number.normalized_value;
                    let unsigned = value.strip_prefix('-').unwrap_or(value);
                    if !unsigned.bytes().all(|b| b.is_ascii_digit())
                        || (*target == StandardSet::N && value.starts_with('-'))
                    {
                        return Err(LeanCompileError::unsupported(
                            "ClosedMembership/IntegerLiteral",
                        ));
                    }
                    if *target == StandardSet::N {
                        ("numberInNOfEq", format!("({value} : ℕ)"))
                    } else {
                        ("numberInZOfEq", format!("({value} : ℤ)"))
                    }
                }
                _ => return Err(LeanCompileError::unsupported("ClosedMembership/Carrier")),
            };
            return Ok(format!("(Litex.NativeBridge.inOfDenoteNumber {} {} {} {} (Litex.NativeBridge.{bridge} {} {representative} (by norm_num)))", self.compile_object_reference(element, position)?, native.0, standard_term(target)?, native.1, native.0));
        }
        let calculated = self
            .compile_numeric_observation(element, position)?
            .3
            .ok_or_else(|| LeanCompileError::unsupported("ClosedMembership/Expression"))?;
        let scalar = match value {
            ClosedScalarValue::Decimal(value) => scalar_decimal(value)?,
            ClosedScalarValue::ExactComplex { real, imaginary } if imaginary.is_zero() => {
                real.clone()
            }
            ClosedScalarValue::ExactComplex { .. } => {
                return Err(LeanCompileError::unsupported(
                    "ClosedMembership/ComplexScalar",
                ))
            }
        };
        if calculated != scalar {
            return Err(LeanCompileError::new(
                "ClosedMembership/Value",
                "The recorded exact scalar differs from its source arithmetic.",
            ));
        }
        let object = self.compile_object_reference(element, position)?;
        let native = self.compile_numeric_observation(element, position)?;
        if *target == StandardSet::C {
            let scalar = exact_rational_literal(&scalar, "ℂ")?;
            let denotation = format!(
                "({}).trans (congrArg M.number (by norm_num : {} = {scalar}))",
                native.1, native.0
            );
            return Ok(format!("(Litex.NativeBridge.inOfDenoteNumber {object} {scalar} {} ({denotation}) (Litex.numberInC (M := M) {scalar}))", standard_term(target)?));
        }
        let (bridge, representative) = match target {
            StandardSet::N => {
                let integer = scalar
                    .to_i128_if_integer()
                    .filter(|n| *n >= 0)
                    .ok_or_else(|| {
                        LeanCompileError::new(
                            "ClosedMembership/N",
                            "A natural certificate has no exact natural value.",
                        )
                    })?;
                ("numberInNOfEq", format!("({integer} : ℕ)"))
            }
            StandardSet::Z => {
                let integer = scalar.to_i128_if_integer().ok_or_else(|| {
                    LeanCompileError::new(
                        "ClosedMembership/Z",
                        "An integer certificate has no exact integer value.",
                    )
                })?;
                ("numberInZOfEq", format!("({integer} : ℤ)"))
            }
            StandardSet::R => ("numberInROfEq", exact_rational_literal(&scalar, "ℝ")?),
            StandardSet::Q => ("numberInQOfEq", exact_rational_literal(&scalar, "ℚ")?),
            _ => return Err(LeanCompileError::unsupported("ClosedMembership/Carrier")),
        };
        let number_member = format!(
            "(Litex.NativeBridge.{bridge} {} {representative} (by norm_num))",
            native.0
        );
        Ok(format!(
            "(Litex.NativeBridge.inOfDenoteNumber {object} {} {} {} {number_member})",
            native.0,
            standard_term(target)?,
            native.1
        ))
    }
}
