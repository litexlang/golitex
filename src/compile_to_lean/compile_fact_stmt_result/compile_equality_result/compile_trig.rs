use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_argument;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_periodic_trig::{PeriodicTrigBuiltinRuleProof, PeriodicTrigNonzeroBuiltinRuleProof};
use crate::prelude::*;

// A fixed normalization adapter for the selected exact-angle certificate.
// No theorem search or rule selection is performed here.
const EXACT_ANGLE_LAWS: &str = "Real.sin_zero, Real.cos_zero, Real.tan_zero, Real.sin_pi, Real.cos_pi, Real.tan_pi, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_pi_div_six, Real.cos_pi_div_three, Real.sin_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four, Real.tan_pi_div_four, Real.tan_pi_div_three, Litex.tanPiDivSix, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub, Real.tan_pi_sub, Real.sin_two_pi, Real.cos_two_pi";

fn validate_closed_coefficient(
    argument: &Obj,
    coefficient: &Obj,
    requirements: &[VerifyFactResult],
) -> Result<(), LeanCompileError> {
    let expected = crate::rational_expression::pi_multiple::pi_coefficient(argument)
        .ok_or_else(|| LeanCompileError::unsupported("Trig/AngleCoefficient"))?;
    if expected.ir() != coefficient.ir()
        || EvalRational::from_obj(coefficient).is_none()
        || !requirements.is_empty()
    {
        return Err(LeanCompileError::unsupported(
            "Trig/ClosedPeriodCertificate",
        ));
    }
    Ok(())
}

fn trig_square(obj: &Obj) -> Option<(&'static str, &Obj)> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) = obj else {
        return None;
    };
    if EvalRational::from_obj(&p.exponent) != EvalRational::new(2, 1) {
        return None;
    }
    trig_argument(&p.base)
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_periodic_trig(
        &self,
        fact: &EqualFact,
        proof: &PeriodicTrigBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (object, other) = if trig_argument(&fact.left).is_some() {
            (&fact.left, &fact.right)
        } else {
            (&fact.right, &fact.left)
        };
        let (_, argument) = trig_argument(object)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/PeriodicSubject"))?;
        validate_closed_coefficient(argument, &proof.coefficient, &proof.integer_requirements)?;
        if !crate::rational_expression::objs_equal_by_rational_expression_evaluation(
            other,
            &proof.value,
        ) {
            return Err(LeanCompileError::unsupported("Trig/PeriodicValue"));
        }
        let tactic = self.closed_trig_tactic(object, &proof.coefficient, position)?;
        self.compile_trig_native_identity(fact, &tactic, position)
    }

    pub(in crate::compile_to_lean) fn compile_periodic_trig_nonzero(
        &self,
        fact: &AtomicFact,
        proof: &PeriodicTrigNonzeroBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(f) = fact else {
            return Err(LeanCompileError::unsupported("Trig/NonzeroSubject"));
        };
        let (object, zero) = if trig_argument(&f.left).is_some() {
            (&f.left, &f.right)
        } else {
            (&f.right, &f.left)
        };
        let (kind, argument) = trig_argument(object)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/NonzeroSubject"))?;
        if kind == "Tan" || !is_exact_zero(zero) {
            return Err(LeanCompileError::unsupported("Trig/NonzeroSubject"));
        }
        validate_closed_coefficient(argument, &proof.coefficient, &proof.integer_requirements)?;
        let tactic = self.closed_trig_tactic(object, &proof.coefficient, position)?;
        let x = self.compile_numeric_observation(&f.left, position)?;
        let y = self.compile_numeric_observation(&f.right, position)?;
        Ok(format!(
            "(Litex.NativeBridge.notSameOfDenoteNumber {} {} {} {} {} {} (by {tactic}))",
            self.compile_object_reference(&f.left, position)?,
            self.compile_object_reference(&f.right, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        ))
    }

    fn closed_trig_tactic(
        &self,
        object: &Obj,
        coefficient: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, argument) = trig_argument(object)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/AngleSubject"))?;
        if !matches!(kind, "Sin" | "Cos" | "Tan") {
            return Err(LeanCompileError::unsupported("Trig/PeriodicOperation"));
        }
        let c = EvalRational::from_obj(coefficient)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/ClosedAngle"))?;
        let period = if kind == "Tan" { 1 } else { 2 };
        let r = c
            .modulo_integer(period)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/AngleOverflow"))?;
        let n = c
            .sub(&r)
            .and_then(|x| x.div(&EvalRational::new(period, 1)?))
            .and_then(|x| x.to_i128_if_integer())
            .ok_or_else(|| LeanCompileError::unsupported("Trig/AngleOverflow"))?;
        let greater = |num, den| {
            r.compare(&EvalRational::new(num, den).unwrap())
                .map(|o| o == crate::rational_expression::NumberCompareResult::Greater)
                .ok_or_else(|| LeanCompileError::unsupported("Trig/AngleOverflow"))
        };
        let (base, quadrant) = if greater(1, 2)? {
            if !greater(1, 1)? {
                (EvalRational::new(1, 1).unwrap().sub(&r), 1)
            } else if !greater(3, 2)? {
                (r.sub(&EvalRational::new(1, 1).unwrap()), 2)
            } else {
                (EvalRational::new(2, 1).unwrap().sub(&r), 3)
            }
        } else {
            (Some(r.clone()), 0)
        };
        let base = base.ok_or_else(|| LeanCompileError::unsupported("Trig/AngleOverflow"))?;
        let angle = match base.parts() {
            (0, 1) => "0".to_string(),
            (1, d @ (2 | 3 | 4 | 6)) => format!("Real.pi / {d}"),
            _ => return Err(LeanCompileError::unsupported("Trig/ExactAngleTable")),
        };
        let angle = match quadrant {
            0 => angle,
            1 => format!("(Real.pi - ({angle}))"),
            2 => format!("(Real.pi + ({angle}))"),
            _ => format!("(2 * Real.pi - ({angle}))"),
        };
        let native = self.compile_numeric_observation(argument, position)?.0;
        let op = kind.to_lowercase();
        let law = if kind == "Tan" {
            "tan_add_int_mul_pi".to_string()
        } else {
            format!("{op}_add_int_mul_two_pi")
        };
        let cycle = if period == 1 {
            "Real.pi"
        } else {
            "(2 * Real.pi)"
        };
        Ok(format!("have _angle : ({native}).re = ({angle}) + ({n} : ℤ) * {cycle} := (by (conv_lhs => norm_num); ring); rw [_angle, Real.{law}]; (conv_lhs => simp only [{EXACT_ANGLE_LAWS}]); (conv_rhs => simp only [{EXACT_ANGLE_LAWS}]); norm_num [neg_div]"))
    }

    pub(in crate::compile_to_lean) fn compile_trig_identity(
        &self,
        fact: &EqualFact,
        quotient: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (left, right, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let argument = if quotient {
                let Some(("Tan", arg)) = trig_argument(left) else {
                    continue;
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Div(d)) = right else {
                    continue;
                };
                if !matches!(trig_argument(&d.left),Some(("Sin",a)) if a.ir()==arg.ir())
                    || !matches!(trig_argument(&d.right),Some(("Cos",a)) if a.ir()==arg.ir())
                {
                    continue;
                }
                arg
            } else {
                if EvalRational::from_obj(right) != EvalRational::new(1, 1) {
                    continue;
                }
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) = left else {
                    continue;
                };
                let Some((l, x)) = trig_square(&a.left) else {
                    continue;
                };
                let Some((r, y)) = trig_square(&a.right) else {
                    continue;
                };
                if x.ir() != y.ir() || !matches!((l, r), ("Sin", "Cos") | ("Cos", "Sin")) {
                    continue;
                }
                // Native observations have identical original child representatives.
                return self.compile_trig_native_identity(
                    fact,
                    &format!(
                        "{}simpa only [add_comm] using (Litex.sinSqAddCosSq ({}).re)",
                        if reversed { "symm; " } else { "" },
                        self.compile_numeric_observation(x, position)?.0
                    ),
                    position,
                );
            };
            let x = self.compile_numeric_observation(argument, position)?.0;
            return self.compile_trig_native_identity(
                fact,
                &format!(
                    "{}exact Litex.tanQuotient ({x}).re",
                    if reversed { "symm; " } else { "" }
                ),
                position,
            );
        }
        Err(LeanCompileError::unsupported("Trig/IdentitySubject"))
    }

    pub(in crate::compile_to_lean) fn compile_trig_native_identity(
        &self,
        fact: &EqualFact,
        tactic: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let x = self.compile_numeric_observation(&fact.left, position)?;
        let y = self.compile_numeric_observation(&fact.right, position)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} (by {tactic}))",
            self.compile_object_reference(&fact.left, position)?,
            self.compile_object_reference(&fact.right, position)?,
            x.0,
            y.0,
            x.1,
            y.1
        ))
    }
}
