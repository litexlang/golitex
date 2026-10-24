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
        if matches!(proof.values, ClosedValuePair::Complex { .. }) {
            return self.compile_closed_complex_relation(
                &goal.left,
                &goal.right,
                &proof.values,
                false,
                position,
            );
        }
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
            ClosedMembershipCalculationProof::IntegerRange {
                value,
                set: recorded,
                start,
                end,
            } => {
                if recorded.ir() != set.ir() {
                    return Err(LeanCompileError::new(
                        "ClosedMembership/RangeSubject",
                        "The integer-range certificate names another source set.",
                    ));
                }
                return self
                    .compile_closed_range_membership(element, set, value, start, end, position);
            }
        };
        self.compile_closed_standard_membership(element, value, target, position)
    }

    fn compile_closed_standard_membership(
        &self,
        element: &Obj,
        value: &ClosedScalarValue,
        target: &StandardSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Some((base, name)) = numeric_refinement(target) {
            let nonzero = matches!(
                target,
                StandardSet::QStar | StandardSet::ZStar | StandardSet::RStar | StandardSet::CStar
            );
            let positive = *target == StandardSet::QPos;
            let (decimal, exact_real) = match value {
                ClosedScalarValue::Decimal(recorded) => {
                    if let Obj::Literal(Literal::Number(number)) = element {
                        if &number.normalized_value != recorded {
                            return Err(LeanCompileError::unsupported("ClosedMembership/Value"));
                        }
                    }
                    // Preserve the existing unbounded literal path.
                    let order = compare_number_strings(recorded, "0");
                    let valid = if nonzero {
                        order != NumberCompareResult::Equal
                    } else if positive {
                        order == NumberCompareResult::Greater
                    } else {
                        order == NumberCompareResult::Less
                    };
                    if !valid {
                        return Err(LeanCompileError::unsupported(
                            "ClosedMembership/RefinedSign",
                        ));
                    }
                    (Some(recorded.clone()), None)
                }
                ClosedScalarValue::ExactComplex { real, imaginary } => {
                    let Some((a, b)) =
                        crate::rational_expression::exact_complex::exact_complex_coordinates(
                            element,
                        )
                    else {
                        return Err(LeanCompileError::unsupported(
                            "ClosedMembership/ComplexExpression",
                        ));
                    };
                    if &a != real || &b != imaginary {
                        return Err(LeanCompileError::unsupported("ClosedMembership/Value"));
                    }
                    let order = real.compare(&scalar_decimal("0")?);
                    let valid = if nonzero {
                        !real.is_zero() || !imaginary.is_zero()
                    } else {
                        imaginary.is_zero()
                            && order
                                == Some(if positive {
                                    NumberCompareResult::Greater
                                } else {
                                    NumberCompareResult::Less
                                })
                    };
                    if !valid {
                        return Err(LeanCompileError::unsupported(
                            "ClosedMembership/RefinedSign",
                        ));
                    }
                    (None, Some(real))
                }
            };
            let base_proof =
                self.compile_closed_standard_membership(element, value, &base, position)?;
            let native = self.compile_numeric_observation(element, position)?;
            let object = self.compile_object_reference(element, position)?;
            let condition = if nonzero {
                format!("(Litex.NativeBridge.notSameOfDenoteNumber {object} (Litex.number (M := M) 0) {} 0 {} rfl (by norm_num [Complex.ext_iff]))", native.0, native.1)
            } else {
                let representative = if let Some(real) = decimal {
                    format!("({real} : ℝ)")
                } else {
                    exact_rational_literal(exact_real.unwrap(), "ℝ")?
                };
                let denotation = format!(
                    "(({}).trans (congrArg M.number (by norm_num : {} = ({representative} : ℂ))))",
                    native.1, native.0
                );
                if positive {
                    format!("(Litex.NativeBridge.ltOfDenoteReal (Litex.number (M := M) 0) {object} 0 {representative} rfl {denotation} (by norm_num))")
                } else {
                    format!("(Litex.NativeBridge.ltOfDenoteReal {object} (Litex.number (M := M) 0) {representative} 0 {denotation} rfl (by norm_num))")
                }
            };
            return Ok(format!(
                "(Litex.in{name}_intro {object} {base_proof} {condition})"
            ));
        }
        if *target == StandardSet::RPos {
            return self.compile_closed_positive_real_membership(element, value, position);
        }
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
            if *target == StandardSet::NPos {
                let value = &number.normalized_value;
                if !value.bytes().all(|b| b.is_ascii_digit()) || value.bytes().all(|b| b == b'0') {
                    return Err(LeanCompileError::unsupported(
                        "ClosedMembership/PositiveNaturalLiteral",
                    ));
                }
                return Ok(format!("(Litex.numberInNPosOfEq (M := M) {} ({value} : ℕ) (by norm_num) (by norm_num))", native.0));
            }
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
            // Literal objects already have this exact native payload. Their
            // closed certificate needs no round trip through denotation.
            return Ok(format!(
                "(Litex.NativeBridge.{bridge} (M := M) {} {representative} (by norm_num))",
                native.0
            ));
        }
        if *target == StandardSet::C {
            if let ClosedScalarValue::ExactComplex { real, imaginary } = value {
                return self.compile_closed_complex_membership(element, real, imaginary, position);
            }
        }
        let native = self.compile_numeric_observation(element, position)?;
        let calculated = native
            .3
            .as_ref()
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
        if calculated != &scalar {
            return Err(LeanCompileError::new(
                "ClosedMembership/Value",
                "The recorded exact scalar differs from its source arithmetic.",
            ));
        }
        let object = self.compile_object_reference(element, position)?;
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

    fn compile_closed_range_membership(
        &self,
        element: &Obj,
        set: &Obj,
        value: &ClosedScalarValue,
        start: &ClosedScalarValue,
        end: &ClosedScalarValue,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (range_start, range_end, closed) = match set {
            Obj::SetFormer(SetFormer::ClosedRange(r)) => (&r.start, &r.end, true),
            Obj::SetFormer(SetFormer::Range(r)) => (&r.start, &r.end, false),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "ClosedMembership/RangeSubject",
                ))
            }
        };
        let family = if closed { "ClosedRange" } else { "Range" };
        let integer = |object: &Obj,
                       recorded: &ClosedScalarValue|
         -> Result<(i128, String), LeanCompileError> {
            let scalar = match recorded {
                ClosedScalarValue::Decimal(value) => scalar_decimal(value)?,
                ClosedScalarValue::ExactComplex { real, imaginary } if imaginary.is_zero() => {
                    real.clone()
                }
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "ClosedMembership/RangeScalar",
                    ))
                }
            };
            let native = self.compile_numeric_observation(object, position)?;
            if native.3.as_ref() != Some(&scalar) {
                return Err(LeanCompileError::new(
                    "ClosedMembership/RangeValue",
                    "A recorded integer differs from the original closed expression.",
                ));
            }
            let value = scalar
                .to_i128_if_integer()
                .ok_or_else(|| LeanCompileError::unsupported("ClosedMembership/RangeInteger"))?;
            Ok((
                value,
                format!(
                    "(({}).trans (congrArg M.number (by norm_num : {} = (({value} : ℤ) : ℂ))))",
                    native.1, native.0
                ),
            ))
        };
        let (lower, h_lower) = integer(range_start, start)?;
        let (upper, h_upper) = integer(range_end, end)?;
        let (value, h_value) = integer(element, value)?;
        if lower > value
            || (if closed {
                value > upper
            } else {
                value >= upper
            })
        {
            return Err(LeanCompileError::new(
                "ClosedMembership/RangeBounds",
                "The recorded integer is outside the original source bounds.",
            ));
        }
        if [range_start, range_end, element]
            .into_iter()
            .all(|obj| matches!(obj, Obj::Literal(Literal::Number(_))))
        {
            // Keep the exact native payloads: an integer cast need not be
            // definitionally equal to the source's complex numeral.
            let literal = |obj: &Obj| match obj {
                Obj::Literal(Literal::Number(number)) => number_literal(number, "ℂ"),
                _ => unreachable!("checked literal endpoints and element"),
            };
            let a = literal(range_start)?;
            let b = literal(range_end)?;
            let p = literal(element)?;
            return Ok(format!(
                "(Litex.numberIn{family}OfEq (M := M) {a} {b} {p} ({lower} : ℤ) ({upper} : ℤ) ({value} : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))"
            ));
        }
        let term = self.compile_object_reference(set, position)?;
        let element = self.compile_object_reference(element, position)?;
        Ok(format!("(by\n  let _range := {term}\n  exact Litex.in{family}OfDenote _range.val.start _range.val.finish {element} _range.wd.1 _range.wd.2 ({lower} : ℤ) ({upper} : ℤ) ({value} : ℤ) {h_lower} {h_upper} {h_value} (by norm_num) (by norm_num))"))
    }
}
