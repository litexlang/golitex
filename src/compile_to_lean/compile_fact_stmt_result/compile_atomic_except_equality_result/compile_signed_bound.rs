use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::rational_expression::NumberCompareResult;

impl LitexToLeanCompiler {
    // The selected rule supplies a scoped citation, not a new search request.
    // Support exact closed rational bounds; runtime-resolved symbolic bounds
    // remain unsupported until their original resolution evidence is replayed.
    pub(super) fn compile_signed_literal_bound(
        &self,
        goal: &AtomicFact,
        cited: FactId,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let literal_zero = |object: &Obj| {
            matches!(object,
            Obj::Literal(Literal::Number(n)) if n.normalized_value == "0")
        };
        let (value, zero, requested_positive, unequal) = match goal {
            AtomicFact::NotEqualFact(f) if literal_zero(&f.right) => {
                (&f.left, &f.right, None, true)
            }
            AtomicFact::NotEqualFact(f) if literal_zero(&f.left) => (&f.right, &f.left, None, true),
            AtomicFact::LessFact(f) if literal_zero(&f.left) => {
                (&f.right, &f.left, Some(true), false)
            }
            AtomicFact::LessEqualFact(f) if literal_zero(&f.right) => {
                (&f.left, &f.right, Some(false), false)
            }
            _ => return Err(LeanCompileError::unsupported("SignedBound/Target")),
        };
        let (source, citation) = self.cited_fact_reference(cited, position)?;
        let Fact::AtomicFact(source) = source else {
            return Err(LeanCompileError::unsupported("SignedBound/CitedFamily"));
        };
        let (low, high, strict) = source_order_oriented(source)?;
        let (bound, positive) = if high.ir() == value.ir() {
            (low, true)
        } else if low.ir() == value.ir() {
            (high, false)
        } else {
            return Err(LeanCompileError::unsupported("SignedBound/CitedSubject"));
        };
        if requested_positive.is_some_and(|requested| requested != positive) {
            return Err(LeanCompileError::unsupported("SignedBound/Direction"));
        }
        let observed = self.compile_numeric_observation(bound, position)?;
        let scalar = observed
            .3
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("SignedBound/ClosedRational"))?;
        let comparison = scalar
            .compare(&crate::rational_expression::exact_rational::EvalRational::new(0, 1).unwrap())
            .ok_or_else(|| LeanCompileError::unsupported("SignedBound/EvaluationBound"))?;
        if !(match (positive, strict) {
            (true, true) => comparison != NumberCompareResult::Less,
            (true, false) => comparison == NumberCompareResult::Greater,
            (false, true) => comparison != NumberCompareResult::Greater,
            (false, false) => comparison == NumberCompareResult::Less,
        }) {
            return Err(LeanCompileError::unsupported(
                "SignedBound/SignAndStrictness",
            ));
        }
        let value_ref = self.compile_object_reference(value, position)?;
        let zero_ref = self.compile_object_reference(zero, position)?;
        let bound_ref = self.compile_object_reference(bound, position)?;
        let scalar = exact_rational_literal(scalar, "ℝ")?;
        let zero_denote = self.compile_numeric_observation(zero, position)?.1;
        let bound_denote = format!("(({}).trans (congrArg M.number (by norm_num)))", observed.1);
        // A strict cited comparison permits a weak comparison to zero;
        // a weak citation requires a strictly signed bound.
        let relation = if strict {
            "leOfDenoteReal"
        } else {
            "ltOfDenoteReal"
        };
        let bound_sign = if positive {
            format!("(Litex.NativeBridge.{relation} {zero_ref} {bound_ref} 0 {scalar} {zero_denote} {bound_denote} (by norm_num))")
        } else {
            format!("(Litex.NativeBridge.{relation} {bound_ref} {zero_ref} {scalar} 0 {bound_denote} {zero_denote} (by norm_num))")
        };
        let (a, b, sign) = match (positive, strict) {
            (true, true) => (
                &zero_ref,
                &value_ref,
                format!(
                    "(Litex.leLtTrans {zero_ref} {bound_ref} {value_ref} {bound_sign} {citation})"
                ),
            ),
            (true, false) => (
                &zero_ref,
                &value_ref,
                format!(
                    "(Litex.ltLeTrans {zero_ref} {bound_ref} {value_ref} {bound_sign} {citation})"
                ),
            ),
            (false, true) => (
                &value_ref,
                &zero_ref,
                format!(
                    "(Litex.ltLeTrans {value_ref} {bound_ref} {zero_ref} {citation} {bound_sign})"
                ),
            ),
            (false, false) => (
                &value_ref,
                &zero_ref,
                format!(
                    "(Litex.leLtTrans {value_ref} {bound_ref} {zero_ref} {citation} {bound_sign})"
                ),
            ),
        };
        if unequal {
            let not_same = format!("(Litex.ltNotSame {a} {b} {sign})");
            let AtomicFact::NotEqualFact(fact) = goal else {
                unreachable!()
            };
            if fact.left.ir() == if positive { zero.ir() } else { value.ir() } {
                Ok(not_same)
            } else {
                Ok(format!(
                    "(fun _signed_bound_same => {not_same} _signed_bound_same.symm)"
                ))
            }
        } else if positive {
            Ok(sign)
        } else {
            Ok(format!("(Litex.ltToLe {a} {b} {sign})"))
        }
    }
}
