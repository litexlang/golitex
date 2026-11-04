use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_argument;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_periodic_trig::PeriodicTrigBuiltinRuleProof;
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
        if EvalRational::from_obj(&proof.coefficient).is_none()
            || !proof.integer_requirements.is_empty()
        {
            return self.compile_symbolic_periodic_trig(fact, proof, position);
        }
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

    pub(in crate::compile_to_lean) fn compile_periodic_trig_reduction(
        &self,
        object: &Obj,
        proof: &PeriodicTrigBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if EvalRational::from_obj(&proof.coefficient).is_none()
            || !proof.integer_requirements.is_empty()
        {
            return self.compile_symbolic_periodic_trig_reduction(object, proof, position);
        }
        let (kind, argument) = trig_argument(object)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/PeriodicSubject"))?;
        validate_closed_coefficient(argument, &proof.coefficient, &proof.integer_requirements)?;
        let (argument, argument_denotation) =
            self.compile_periodic_real_value(argument, position, 0)?;
        let (value, value_denotation) =
            self.compile_periodic_real_value(&proof.value, position, 0)?;
        let operation = crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_native_operation(kind)?;
        let tactic = closed_periodic_tactic(kind, &proof.coefficient, &argument, "ring")?;
        Ok(format!(
            "((congrArg (Litex.realUnaryValue (M := M) {operation}) {argument_denotation}).trans ((Litex.realUnaryValue_number (M := M) {operation} {argument}).trans ((congrArg M.number (show (({operation} {argument}) : ℂ) = (({value} : ℝ) : ℂ) from (by {tactic}))).trans ({value_denotation}).symm)))",
        ))
    }

    /// Intermediate certificate expressions have semantic values, not fresh
    /// source WD registrations. Replay their closed numeric denotation laws.
    pub(super) fn compile_periodic_real_value(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
        depth: usize,
    ) -> Result<(String, String), LeanCompileError> {
        if depth >= 64 {
            return Err(LeanCompileError::unsupported("Trig/ClosedValueDepth"));
        }
        if let Some(value) = EvalRational::from_obj(object) {
            let (_, equality) = self.compile_eval_closed_value(object, position)?;
            let real = exact_rational_literal(&value, "ℝ")?;
            let complex = exact_rational_literal(&value, "ℂ")?;
            return Ok((real.clone(), format!("(({equality}).trans (congrArg M.number (by norm_num : {complex} = (({real} : ℝ) : ℂ))))")));
        }
        if matches!(object, Obj::Literal(Literal::Pi(_))) {
            let raw = self.compile_normalization_value(object, position)?;
            return Ok((
                "Real.pi".into(),
                format!("(rfl : {raw} = M.number (Real.pi : ℂ))"),
            ));
        }
        if let Obj::ExpLogOperator(ExpLogOperator::Sqrt(p)) = object {
            let (arg, proof) = self.compile_periodic_real_value(&p.arg, position, depth + 1)?;
            return Ok((format!("(Real.sqrt {arg})"), format!("((congrArg (Litex.sqrtValue (M := M)) {proof}).trans (Litex.sqrtValue_number (M := M) {arg}))")));
        }
        if let Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) = object {
            let (arg, proof) = self.compile_periodic_real_value(&p.arg, position, depth + 1)?;
            return Ok((format!("(-{arg})"), format!("((congrArg M.negValue {proof}).trans ((M.neg_numbers (({arg} : ℝ) : ℂ)).trans (congrArg M.number (Complex.ofReal_neg {arg}).symm)))")));
        }
        let (left, right, operation, symbol, cast) = match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
                (&p.left, &p.right, "add", "+", "add")
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
                (&p.left, &p.right, "sub", "-", "sub")
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                (&p.left, &p.right, "mul", "*", "mul")
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => {
                (&p.left, &p.right, "div", "/", "div")
            }
            _ => return Err(LeanCompileError::unsupported("Trig/ClosedSemanticValue")),
        };
        if operation == "div" && !EvalRational::from_obj(right).is_some_and(|n| !n.is_zero()) {
            return Err(LeanCompileError::unsupported("Trig/ClosedDenominator"));
        }
        let (a, ha) = self.compile_periodic_real_value(left, position, depth + 1)?;
        let (b, hb) = self.compile_periodic_real_value(right, position, depth + 1)?;
        let nonzero = if operation == "div" {
            " (by norm_num)"
        } else {
            ""
        };
        Ok((format!("({a} {symbol} {b})"), format!("((congrArg₂ M.{operation}Value {ha} {hb}).trans ((M.{operation}_numbers (({a} : ℝ) : ℂ) (({b} : ℝ) : ℂ){nonzero}).trans (congrArg M.number (Complex.ofReal_{cast} {a} {b}).symm)))")))
    }

    fn closed_trig_tactic(
        &self,
        object: &Obj,
        coefficient: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, argument) = trig_argument(object)
            .ok_or_else(|| LeanCompileError::unsupported("Trig/AngleSubject"))?;
        let native = self.compile_numeric_observation(argument, position)?.0;
        closed_periodic_tactic(
            kind,
            coefficient,
            &format!("({native}).re"),
            "(conv_lhs => norm_num); ring",
        )
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

pub(super) fn closed_periodic_tactic(
    kind: &str,
    coefficient: &Obj,
    native: &str,
    angle_normalization: &str,
) -> Result<String, LeanCompileError> {
    if !matches!(kind, "Sin" | "Cos" | "Tan" | "Cot") {
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
    let reduce = if kind == "Cot" {
        "simp only [Litex.nativeCot]; rw [_angle, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]".to_string()
    } else {
        format!("rw [_angle, Real.{law}]")
    };
    let (rationalization, extra_laws) = if kind == "Cot" {
        if base.parts() == (1, 3) {
            (
                "have _sqrt_three_inverse : ((Real.sqrt 3 : ℝ) : ℂ)⁻¹ = (Real.sqrt 3 : ℂ) / 3 := (by exact_mod_cast (Real.sqrt_div_self (x := (3 : ℝ))).symm); ",
                ", div_neg, div_div_div_cancel_right₀, one_div, _sqrt_three_inverse",
            )
        } else {
            ("", ", div_neg, div_div_div_cancel_right₀, one_div")
        }
    } else {
        ("", "")
    };
    // Keep the certificate's sqrt(3)/3 form instead of the default 1/sqrt(3).
    Ok(format!("have _angle : ({native}) = ({angle}) + ({n} : ℤ) * {cycle} := (by {angle_normalization}); {reduce}; {rationalization}norm_num [{EXACT_ANGLE_LAWS}, neg_div, -Real.tan_pi_div_six{extra_laws}]"))
}
