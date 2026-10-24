use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::PositiveRealFromKnownStrictOrderProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_refined_numeric_strategy(
        &self,
        fact: &InFact,
        requirements: &[Fact],
        results: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if fact.set == Obj::StandardSet(StandardSet::N) {
            if requirements.len() != 2 || results.len() != 2 {
                return Err(LeanCompileError::unsupported("RefinedNatural/Requirements"));
            }
            if membership_subject(&requirements[0], &fact.element)? != StandardSet::Z {
                return Err(LeanCompileError::unsupported(
                    "RefinedNatural/IntegerSubject",
                ));
            }
            let Fact::AtomicFact(order) = &requirements[1] else {
                return Err(LeanCompileError::unsupported("RefinedNatural/OrderSubject"));
            };
            let (zero, element, strict) = source_order_oriented(order)?;
            if strict || !is_exact_zero(zero) || element.ir() != fact.element.ir() {
                return Err(LeanCompileError::unsupported("RefinedNatural/OrderSubject"));
            }
            let mut proofs = Vec::new();
            for (requirement, result) in requirements.iter().zip(results) {
                if source_subject(result)? != *requirement {
                    return Err(LeanCompileError::unsupported(
                        "RefinedNatural/RequirementCapture",
                    ));
                }
                proofs.push(self.compile_verify(result, position)?.1);
            }
            return Ok(format!(
                "(Litex.integerToNaturalOfNonnegative {} {} {})",
                self.compile_object_reference(&fact.element, position)?,
                proofs[0],
                proofs[1]
            ));
        }
        if let Obj::StandardSet(set) = &fact.set {
            if let Some((base, name)) = numeric_refinement(set) {
                if requirements.len() != 2 || results.len() != 2 {
                    return Err(LeanCompileError::unsupported(
                        "RefinedNumericCarrier/Requirements",
                    ));
                }
                if membership_subject(&requirements[0], &fact.element)? != base {
                    return Err(LeanCompileError::unsupported(
                        "RefinedNumericCarrier/BaseSubject",
                    ));
                }
                let condition_matches = match &requirements[1] {
                    Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                        if matches!(
                            set,
                            StandardSet::QStar
                                | StandardSet::ZStar
                                | StandardSet::RStar
                                | StandardSet::CStar
                        ) =>
                    {
                        f.left.ir() == fact.element.ir() && is_exact_zero(&f.right)
                    }
                    Fact::AtomicFact(f)
                        if matches!(
                            set,
                            StandardSet::QPos
                                | StandardSet::QNeg
                                | StandardSet::ZNeg
                                | StandardSet::RNeg
                        ) =>
                    {
                        let (left, right, strict) = source_order_oriented(f)?;
                        let (zero, value) = if *set == StandardSet::QPos {
                            (left, right)
                        } else {
                            (right, left)
                        };
                        strict && is_exact_zero(zero) && value.ir() == fact.element.ir()
                    }
                    _ => false,
                };
                if !condition_matches {
                    return Err(LeanCompileError::unsupported(
                        "RefinedNumericCarrier/ConditionSubject",
                    ));
                }
                let mut proofs = Vec::new();
                for (requirement, result) in requirements.iter().zip(results) {
                    if source_subject(result)? != *requirement {
                        return Err(LeanCompileError::unsupported(
                            "RefinedNumericCarrier/RequirementCapture",
                        ));
                    }
                    proofs.push(self.compile_verify(result, position)?.1);
                }
                return Ok(format!(
                    "(Litex.in{name}_intro {} {} {})",
                    self.compile_object_reference(&fact.element, position)?,
                    proofs[0],
                    proofs[1]
                ));
            }
        }
        if fact.set != Obj::StandardSet(StandardSet::RPos) {
            return Err(LeanCompileError::unsupported(
                "RefinedNumericCarrier/OtherTarget",
            ));
        }
        if requirements.len() != 2 || results.len() != 2 {
            return Err(LeanCompileError::new("RefinedPositiveReal/Requirements", "The selected refinement must retain its ordered real and strictly positive source results."));
        }
        if membership_subject(&requirements[0], &fact.element)? != StandardSet::R {
            return Err(LeanCompileError::new(
                "RefinedPositiveReal/RealSubject",
                "The original real-membership child must describe this exact element.",
            ));
        }
        let Fact::AtomicFact(positive) = &requirements[1] else {
            return Err(LeanCompileError::new(
                "RefinedPositiveReal/OrderFamily",
                "The original positivity child must be atomic.",
            ));
        };
        let (zero, element, strict) = source_order_oriented(positive)?;
        if !strict || !is_exact_zero(zero) || element.ir() != fact.element.ir() {
            return Err(LeanCompileError::new(
                "RefinedPositiveReal/OrderSubject",
                "The original positivity child changes its exact element or strict zero bound.",
            ));
        }
        let mut proofs = Vec::new();
        for (requirement, result) in requirements.iter().zip(results) {
            if source_subject(result)? != *requirement {
                return Err(LeanCompileError::new("RefinedPositiveReal/RequirementCapture", "An original ordered refinement result differs from its actual requirement identity."));
            }
            proofs.push(self.compile_verify(result, position)?.1);
        }
        Ok(format!(
            "(Litex.inRPos_intro {} {} {})",
            self.compile_object_reference(&fact.element, position)?,
            proofs[0],
            proofs[1]
        ))
    }

    pub(in crate::compile_to_lean) fn compile_positive_real_from_known_strict_order(
        &self,
        fact: &InFact,
        proof: &PositiveRealFromKnownStrictOrderProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(&proof.positive_order.fact)?;
        if fact.set != Obj::StandardSet(StandardSet::RPos)
            || !strict
            || !is_exact_zero(low)
            || high.ir() != fact.element.ir()
        {
            return Err(LeanCompileError::new(
                "PositiveReal/OrderSubject",
                "The selected strict-order premise must state positivity of this exact element.",
            ));
        }
        let (_, positive) = self.compile_order_known_premise(&proof.positive_order, position)?;
        let members =
            self.order_real_members_from_known(&proof.positive_order.fact, &positive, position)?;
        let real = match source_order_parts(&proof.positive_order.fact)?.0 {
            SourceOrderKind::Less => members.1,
            SourceOrderKind::Greater => members.0,
            SourceOrderKind::LessEqual | SourceOrderKind::GreaterEqual => {
                return Err(LeanCompileError::unsupported("PositiveReal/WeakOrder"));
            }
        };
        Ok(format!(
            "(Litex.inRPos_intro {} {real} {positive})",
            self.compile_object_reference(&fact.element, position)?,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_closed_positive_real_membership(
        &self,
        element: &Obj,
        value: &ClosedScalarValue,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let native = self.compile_numeric_observation(element, position)?;
        let representative =
            if let (Obj::Literal(Literal::Number(number)), ClosedScalarValue::Decimal(recorded)) =
                (element, value)
            {
                if number.normalized_value != *recorded
                    || compare_number_strings(recorded, "0") != NumberCompareResult::Greater
                {
                    return Err(LeanCompileError::new(
                        "PositiveReal/ClosedValue",
                        "The literal certificate must record this exact positive scalar.",
                    ));
                }
                number_literal(number, "ℝ")?
            } else {
                let scalar = match value {
                    ClosedScalarValue::Decimal(value) => scalar_decimal(value)?,
                    ClosedScalarValue::ExactComplex { real, imaginary } if imaginary.is_zero() => {
                        real.clone()
                    }
                    ClosedScalarValue::ExactComplex { .. } => {
                        return Err(LeanCompileError::unsupported("PositiveReal/ComplexScalar"))
                    }
                };
                let zero = scalar_decimal("0")?;
                if native.3.as_ref() != Some(&scalar)
                    || scalar.compare(&zero) != Some(NumberCompareResult::Greater)
                {
                    return Err(LeanCompileError::new(
                    "PositiveReal/ClosedValue",
                    "The recorded exact scalar must equal its checked expression and be positive.",
                ));
                }
                exact_rational_literal(&scalar, "ℝ")?
            };
        let object = self.compile_object_reference(element, position)?;
        Ok(format!(
            "(Litex.NativeBridge.inOfDenoteNumber {object} {} (Litex.RPos (M := M)) {} (Litex.NativeBridge.numberInRPosOfEq (M := M) {} {representative} (by norm_num) (by norm_num)))",
            native.0, native.1, native.0
        ))
    }
}
