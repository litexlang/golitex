use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_argument;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    // Normalize only the endpoint of the recorded comparison. The subject,
    // direction, strictness and original scoped proof must all be retained.
    pub(in crate::compile_to_lean) fn compile_principal_trig_bound(
        &self,
        source: &AtomicFact,
        proof: &str,
        subject: &Obj,
        half_pi: bool,
        lower: bool,
        strict: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, source_strict) = source_order_oriented(source)?;
        let (bound, actual_subject) = if lower { (low, high) } else { (high, low) };
        let (n, d, real) = match (half_pi, lower) {
            (true, true) => (-1, 2, "-(Real.pi / 2)"),
            (true, false) => (1, 2, "Real.pi / 2"),
            (false, true) => (0, 1, "0"),
            (false, false) => (1, 1, "Real.pi"),
        };
        if source_strict != strict
            || actual_subject.ir() != subject.ir()
            || crate::rational_expression::pi_multiple::pi_coefficient(bound)
                .and_then(|c| EvalRational::from_obj(&c))
                != EvalRational::new(n, d)
        {
            return Err(LeanCompileError::unsupported("Trig/PrincipalBoundContract"));
        }
        let old = self.compile_object_reference(bound, position)?;
        let value = self.compile_object_reference(subject, position)?;
        let observed = self.compile_numeric_observation(bound, position)?;
        let new = format!("(Litex.number ((({real}) : ℝ) : ℂ))");
        let normalize = if half_pi {
            "push_cast; ring"
        } else if lower {
            "norm_num"
        } else {
            "ring"
        };
        let same = format!(
            "(({}).trans (congrArg M.number (show {} = ((({real}) : ℝ) : ℂ) from by {normalize})))",
            observed.1, observed.0
        );
        let law = if strict { "ltOfSame" } else { "leOfSame" };
        Ok(if lower {
            format!("(Litex.{law} {old} {new} {value} {value} {same} rfl {proof})")
        } else {
            format!("(Litex.{law} {value} {value} {old} {new} rfl {same} {proof})")
        })
    }

    pub(super) fn compile_unit_circle_bound(
        &self,
        goal: &AtomicFact,
        lower: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let (bound, object) = if lower { (low, high) } else { (high, low) };
        let Some((kind @ ("Sin" | "Cos"), _)) = trig_argument(object) else {
            return Err(LeanCompileError::unsupported("Trig/UnitCircleSubject"));
        };
        let expected = if lower { -1 } else { 1 };
        if strict || EvalRational::from_obj(bound) != EvalRational::new(expected, 1) {
            return Err(LeanCompileError::unsupported("Trig/UnitCircleEndpoint"));
        }
        let term = self.compile_object_reference(object, position)?;
        let bound = self.compile_object_reference(bound, position)?;
        let observed =
            self.compile_numeric_observation(if lower { low } else { high }, position)?;
        let law = format!(
            "{}{}BoundValue",
            if kind == "Sin" { "sine" } else { "cosine" },
            if lower { "Lower" } else { "Upper" }
        );
        Ok(format!(
            "(Litex.{law} {term} {bound} (({}).trans (congrArg M.number (by norm_num))))",
            observed.1
        ))
    }

    pub(super) fn compile_principal_trig_nonzero(
        &self,
        goal: &AtomicFact,
        cosine: bool,
        lower: &AtomicExceptEqualityFactKnownProof,
        upper: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = goal else {
            return Err(LeanCompileError::unsupported("Trig/PrincipalNonzeroFamily"));
        };
        let (object, zero, reversed) = if is_exact_zero(&fact.right) {
            (&fact.left, &fact.right, false)
        } else if is_exact_zero(&fact.left) {
            (&fact.right, &fact.left, true)
        } else {
            return Err(LeanCompileError::unsupported("Trig/PrincipalNonzeroZero"));
        };
        let Some((kind, arg)) = trig_argument(object) else {
            return Err(LeanCompileError::unsupported(
                "Trig/PrincipalNonzeroSubject",
            ));
        };
        if kind != if cosine { "Cos" } else { "Sin" } {
            return Err(LeanCompileError::unsupported(
                "Trig/PrincipalNonzeroOperation",
            ));
        }
        let lo = self.compile_order_known_premise(lower, position)?.1;
        let hi = self.compile_order_known_premise(upper, position)?.1;
        let lo =
            self.compile_principal_trig_bound(&lower.fact, &lo, arg, cosine, true, true, position)?;
        let hi = self.compile_principal_trig_bound(
            &upper.fact,
            &hi,
            arg,
            cosine,
            false,
            true,
            position,
        )?;
        let object = self.compile_object_reference(object, position)?;
        let law = if cosine {
            "cosineNonzeroOnPrincipalInterval"
        } else {
            "sineNonzeroOnPrincipalInterval"
        };
        let zero_ref = self.compile_object_reference(zero, position)?;
        let zero = self.compile_numeric_observation(zero, position)?;
        let zero_denote = format!("(show Litex.denote {zero_ref} = M.number (0 : ℂ) from (({}).trans (congrArg M.number (by norm_num))))", zero.1);
        let same = if reversed {
            "_trig_zero.symm"
        } else {
            "_trig_zero"
        };
        Ok(format!(
            "(fun _trig_zero => (Litex.{law} {object} {lo} {hi}) (({same}).trans {zero_denote}))"
        ))
    }
}
