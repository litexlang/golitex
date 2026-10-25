use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_numeric_bound_weaken(
        &self,
        goal: &AtomicFact,
        cited: FactId,
        upper: bool,
        target_strict: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict != target_strict {
            return Err(LeanCompileError::unsupported("NumericBound/GoalStrength"));
        }
        let source = self.resolve_fact(cited, position)?;
        let Fact::AtomicFact(atomic @ (AtomicFact::LessFact(_) | AtomicFact::LessEqualFact(_))) =
            &source
        else {
            return Err(LeanCompileError::unsupported("NumericBound/CitedFamily"));
        };
        let (old_low, old_high, old_strict) = source_order_oriented(atomic)?;
        let (old_bound, bound, same, original_same) = if upper {
            (old_high, high, low, old_low)
        } else {
            (old_low, low, high, old_high)
        };
        if same.ir() != original_same.ir() {
            return Err(LeanCompileError::unsupported("NumericBound/CitedSubject"));
        }
        // These builtin routes accept literal integers, not arbitrary closed
        // expressions or a newly discovered numeric observation of a variable.
        let literal = |obj: &Obj| match obj {
            Obj::Literal(Literal::Number(n)) => n.normalized_value.parse::<i128>().ok(),
            _ => None,
        };
        let old = literal(old_bound)
            .ok_or_else(|| LeanCompileError::unsupported("NumericBound/Literal"))?;
        let new =
            literal(bound).ok_or_else(|| LeanCompileError::unsupported("NumericBound/Literal"))?;
        let (left_bound, right_bound, left_value, right_value) = if upper {
            (old_bound, bound, old, new)
        } else {
            (bound, old_bound, new, old)
        };
        let link_strict = target_strict && !old_strict;
        if left_value > right_value || (link_strict && left_value == right_value) {
            return Err(LeanCompileError::unsupported(
                "NumericBound/WeakeningDirection",
            ));
        }
        let left = self.compile_object_reference(left_bound, position)?;
        let right = self.compile_object_reference(right_bound, position)?;
        let left_observation = self.compile_numeric_observation(left_bound, position)?;
        let right_observation = self.compile_numeric_observation(right_bound, position)?;
        let denote = |proof: &str| format!("(({proof}).trans (congrArg M.number (by norm_num)))");
        let adapter = if link_strict {
            "ltOfDenoteReal"
        } else {
            "leOfDenoteReal"
        };
        let link = format!("(Litex.NativeBridge.{adapter} {left} {right} ({left_value} : ℝ) ({right_value} : ℝ) {} {} (by norm_num))", denote(&left_observation.1), denote(&right_observation.1));
        let same = self.compile_object_reference(same, position)?;
        let mut citation = self.cited_fact_reference(cited, position)?.1;
        if !target_strict && old_strict {
            citation = format!(
                "(Litex.ltToLe {} {} {citation})",
                self.compile_object_reference(old_low, position)?,
                self.compile_object_reference(old_high, position)?
            );
        }
        let (a, b, c, first, second) = if upper {
            (same, left, right, citation, link)
        } else {
            (left, right, same, link, citation)
        };
        let law = if !target_strict {
            "leTrans"
        } else if upper == old_strict {
            "ltLeTrans"
        } else {
            "leLtTrans"
        };
        Ok(format!("(Litex.{law} {a} {b} {c} {first} {second})"))
    }
}
