use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_argument;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError,LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_inverse_principal_range_bound(
        &self,
        goal: &AtomicFact,
        kind: &str,
        lower: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (half, strict, name) = match kind {
            "Arcsin" => (true, false, "arcsine"),
            "Arccos" => (false, false, "arccosine"),
            "Arctan" => (true, true, "arctangent"),
            "Arccot" => (false, true, "arccotangent"),
            _ => return Err(invalid("Operation")),
        };
        let (low, high, goal_strict) = source_order_oriented(goal)?;
        let (bound, object) = if lower { (low, high) } else { (high, low) };
        let (n, d, real) = match (half, lower) {
            (true, true) => (-1, 2, "-(Real.pi / 2)"),
            (true, false) => (1, 2, "Real.pi / 2"),
            (false, true) => (0, 1, "0"),
            (false, false) => (1, 1, "Real.pi"),
        };
        if goal_strict != strict
            || !matches!(trig_argument(object),Some((op,_))if op==kind)
            || crate::rational_expression::pi_multiple::pi_coefficient(bound)
                .and_then(|c| EvalRational::from_obj(&c))
                != EvalRational::new(n, d)
        {
            return Err(invalid("BoundContract"));
        }
        let term = self.compile_object_reference(object, position)?;
        let bound_term = self.compile_object_reference(bound, position)?;
        let observed = self.compile_numeric_observation(bound, position)?;
        let normalize = if half {
            "push_cast; ring"
        } else if lower {
            "norm_num"
        } else {
            "ring"
        };
        let endpoint=format!("(show Litex.denote {bound_term} = M.number ((({real}) : ℝ) : ℂ) from (({}).trans (congrArg M.number (by {normalize}))))",observed.1);
        let law = format!(
            "{name}Principal{}Value",
            if lower { "Lower" } else { "Upper" }
        );
        Ok(format!("(Litex.{law} {term} {bound_term} {endpoint})"))
    }
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("InverseTrigRange/{part}"))
}
