//! Replay a cited order bound and its recorded exact subtraction certificate.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::closed_subtraction_bound::{
    BoundDirection, ClosedSubtractionBoundCertificate,
};
use crate::prelude::*;
use crate::rational_expression::NumberCompareResult;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ClosedSubtractionBound/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_closed_subtraction_bound(
        &self,
        goal: &AtomicFact,
        proof: &ClosedSubtractionBoundCertificate,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let lower = matches!(proof.direction, BoundDirection::Lower);
        let (difference, endpoint) = if lower { (high, low) } else { (low, high) };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = difference else {
            return Err(invalid("Difference"));
        };
        let (source, citation) = self.cited_fact_reference(proof.cite_fact_id, position)?;
        if source != &Fact::AtomicFact(proof.source_fact.clone()) {
            return Err(invalid("CitedSubject"));
        }
        let (source_low, source_high, source_strict) = source_order_oriented(&proof.source_fact)?;
        let (bound, base) = if lower {
            (source_low, source_high)
        } else {
            (source_high, source_low)
        };
        if base.ir() != sub.left.ir() {
            return Err(invalid("BaseSubject"));
        }
        let offset = EvalRational::from_obj(&sub.right).ok_or_else(|| invalid("ClosedOffset"))?;
        if proof.normalized_subtrahend.ir() != offset.to_obj().ir() {
            return Err(invalid("NormalizedOffset"));
        }
        let target = EvalRational::from_obj(endpoint);
        let mut bound_value = None;
        if let Some(target) = &target {
            let value = EvalRational::from_obj(bound).ok_or_else(|| invalid("ClosedBound"))?;
            let translated = value
                .sub(&offset)
                .ok_or_else(|| invalid("TranslatedBound"))?;
            let comparison = translated.compare(target);
            let sufficient = ((!strict || source_strict)
                && comparison == Some(NumberCompareResult::Equal))
                || matches!(
                    (lower, comparison),
                    (true, Some(NumberCompareResult::Greater))
                        | (false, Some(NumberCompareResult::Less))
                );
            if !sufficient
                || proof.translated_bound.ir() != translated.to_obj().ir()
                || proof.target_bound.ir() != target.to_obj().ir()
            {
                return Err(invalid("ClosedCertificate"));
            }
            bound_value = Some(value);
        } else {
            let zero = EvalRational::new(0, 1).unwrap();
            let sign = offset.compare(&zero).ok_or_else(|| invalid("OffsetSign"))?;
            let translated = Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                left: Box::new(bound.clone()),
                right: Box::new(offset.to_obj()),
            }));
            if bound.ir() != endpoint.ir()
                || proof.target_bound.ir() != endpoint.ir()
                || proof.translated_bound.ir() != translated.ir()
                || (strict && !source_strict && sign == NumberCompareResult::Equal)
                || matches!(
                    (lower, sign),
                    (true, NumberCompareResult::Greater) | (false, NumberCompareResult::Less)
                )
            {
                return Err(invalid("SymbolicCertificate"));
            }
        }
        let offset_real = exact_rational_literal(&offset, "ℝ")?;
        let offset_denote = self.compile_numeric_observation(&sub.right, position)?.1;
        let (base_real, base_denote, bound_real, bound_denote) = if lower {
            ("_stored_high", "_high_denote", "_stored_low", "_low_denote")
        } else {
            ("_stored_low", "_low_denote", "_stored_high", "_high_denote")
        };
        let mut lines = vec![
            format!("let _difference := {}", self.compile_object_reference(difference, position)?),
            format!("obtain ⟨_stored_low, _stored_high, _low_denote, _high_denote, _stored_order⟩ := {citation}"),
            format!("have _offset_denote : Litex.denote _difference.val.right = M.number (({offset_real} : ℝ) : ℂ) := ({offset_denote}).trans (congrArg M.number (by norm_num))"),
            format!("have _base_denote : Litex.denote _difference.val.left = M.number ({base_real} : ℂ) := {base_denote}"),
            format!("have _difference_denote : Litex.denote _difference = M.number (({base_real} - {offset_real} : ℝ) : ℂ) := ((congrArg₂ M.subValue _base_denote _offset_denote).trans (M.sub_numbers _ _)).trans (congrArg M.number (Complex.ofReal_sub _ _).symm)"),
        ];
        let (endpoint_real, endpoint_denote, premises) = if let (Some(target), Some(value)) =
            (&target, &bound_value)
        {
            let value = exact_rational_literal(value, "ℝ")?;
            let value_denote = self.compile_numeric_observation(bound, position)?.1;
            lines.push(format!("have _bound_value : {bound_real} = {value} := by\n  apply Complex.ofReal_injective\n  exact M.number_injective ({bound_denote}.symm.trans (({value_denote}).trans (congrArg M.number (by norm_num))))"));
            let target = exact_rational_literal(target, "ℝ")?;
            let denotation = self.compile_numeric_observation(endpoint, position)?.1;
            (
                target,
                format!("(({denotation}).trans (congrArg M.number (by norm_num)))"),
                "_stored_order, _bound_value",
            )
        } else {
            (bound_real.into(), bound_denote.into(), "_stored_order")
        };
        let endpoint_ref = self.compile_object_reference(endpoint, position)?;
        let (objects, values, denotations) = if lower {
            (
                format!("{endpoint_ref} _difference"),
                format!("{endpoint_real} ({base_real} - {offset_real})"),
                format!("{endpoint_denote} _difference_denote"),
            )
        } else {
            (
                format!("_difference {endpoint_ref}"),
                format!("({base_real} - {offset_real}) {endpoint_real}"),
                format!("_difference_denote {endpoint_denote}"),
            )
        };
        // One already-selected affine comparison; no target proof search.
        lines.push(format!("exact Litex.NativeBridge.{} {objects} {values} {denotations} (by linarith only [{premises}])", if strict { "ltOfDenoteReal" } else { "leOfDenoteReal" }));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
