use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::PositiveRealFromKnownStrictOrderProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
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
        let denotation = format!(
            "({}).trans (congrArg M.number (by norm_num : {} = ({representative} : ℂ)))",
            native.1, native.0
        );
        Ok(format!(
            "(Litex.NativeBridge.inOfDenoteNumber {object} ({representative} : ℂ) (Litex.RPos (M := M)) ({denotation}) (Litex.numberInRPos (M := M) {representative} (by norm_num)))"
        ))
    }
}
