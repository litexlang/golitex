//! Replay integral-period certificates; coefficient classification is shared
//! with the producer, and every integer premise retains its original FactId.
use super::compile_trig::closed_periodic_tactic;
use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::{trig_argument, trig_native_operation};
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_periodic_trig::{exact_trig_value, split_terms, CoefficientTerms, PeriodicTrigBuiltinRuleProof, PeriodicTrigNonzeroBuiltinRuleProof, TrigKind};
use crate::prelude::*;

fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("Trig/IntegerPeriod/{part}"))
}

fn coefficient_terms(
    argument: &Obj,
    coefficient: &Obj,
) -> Result<CoefficientTerms, LeanCompileError> {
    let expected = crate::rational_expression::pi_multiple::pi_coefficient(argument)
        .ok_or_else(|| invalid("AngleCoefficient"))?;
    if &expected != coefficient {
        return Err(invalid("AngleCoefficient"));
    }
    split_terms(coefficient, 0).ok_or_else(|| invalid("CoefficientTerms"))
}

fn kind(name: &str) -> Result<TrigKind, LeanCompileError> {
    match name {
        "Sin" => Ok(TrigKind::Sin),
        "Cos" => Ok(TrigKind::Cos),
        "Tan" => Ok(TrigKind::Tan),
        "Cot" => Ok(TrigKind::Cot),
        _ => Err(invalid("Operation")),
    }
}

/// Name the proved scalar bridge instead of inlining its zero-set proof into
/// every constructor WD. Native constant transport also handles q=1 uniformly.
fn rational_angle_nonzero(
    name: &str,
    coefficient: &EvalRational,
) -> Result<String, LeanCompileError> {
    let (p, q) = coefficient.parts();
    let constant = exact_rational_literal(coefficient, "ℝ")?;
    let (operation, law) = match name {
        "Sin" => ("Real.sin", "sinRationalPiNonzero"),
        "Cos" => ("Real.cos", "cosRationalPiNonzero"),
        _ => return Err(invalid("NonzeroOperation")),
    };
    Ok(format!("(Eq.mp (congrArg (fun _coefficient : ℝ => {operation} (_coefficient * Real.pi) ≠ 0) (show ((({p} : ℤ) : ℝ) / (({q} : ℤ) : ℝ)) = {constant} from (by norm_num))) (Litex.{law} ({p} : ℤ) ({q} : ℤ) (by norm_num) (by norm_num)))"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_symbolic_periodic_trig(
        &self,
        fact: &EqualFact,
        proof: &PeriodicTrigBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (object, other, reversed) = if trig_argument(&fact.left).is_some() {
            (&fact.left, &fact.right, false)
        } else {
            (&fact.right, &fact.left, true)
        };
        if !crate::rational_expression::objs_equal_by_rational_expression_evaluation(
            other,
            &proof.value,
        ) {
            return Err(invalid("Value"));
        }
        let raw = self.compile_symbolic_periodic_trig_reduction(object, proof, position)?;
        let (a, ha) = self.compile_periodic_real_value(&proof.value, position, 0)?;
        let (b, hb) = self.compile_periodic_real_value(other, position, 0)?;
        let left = self.compile_normalization_denotation(object, position)?;
        let right = self.compile_normalization_denotation(other, position)?;
        let same = format!("(({left}).trans (({raw}).trans (({ha}).trans ((congrArg M.number (show (({a} : ℝ) : ℂ) = (({b} : ℝ) : ℂ) from (by exact_mod_cast (by ring : ({a} : ℝ) = ({b} : ℝ))))).trans (({hb}).symm.trans ({right}).symm)))))");
        Ok(if reversed {
            format!("({same}).symm")
        } else {
            same
        })
    }

    pub(super) fn compile_symbolic_periodic_trig_reduction(
        &self,
        object: &Obj,
        proof: &PeriodicTrigBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, argument) = trig_argument(object).ok_or_else(|| invalid("Subject"))?;
        let terms = coefficient_terms(argument, &proof.coefficient)?;
        let (period, expected) = exact_trig_value(kind(name)?, &terms.constant)
            .ok_or_else(|| invalid("ExactAngleTable"))?;
        if expected != proof.value {
            return Err(invalid("Value"));
        }
        let (angle, denotation) = self.compile_integer_period_angle(
            argument,
            &terms,
            &proof.integer_requirements,
            period,
            position,
        )?;
        let operation = trig_native_operation(name)?;
        let (value, value_denotation) =
            self.compile_periodic_real_value(&proof.value, position, 0)?;
        let constant = exact_rational_literal(&terms.constant, "ℝ")?;
        let base = format!("({constant} * Real.pi)");
        let closed = closed_periodic_tactic(name, &terms.constant.to_obj(), &base, "ring")?;
        let law = match (name, period) {
            ("Sin", 1) => "Real.sin_add_int_mul_pi",
            ("Cos", 1) => "Real.cos_add_int_mul_pi",
            ("Sin", 2) => "Real.sin_add_int_mul_two_pi",
            ("Cos", 2) => "Real.cos_add_int_mul_two_pi",
            ("Tan", 1) => "Real.tan_add_int_mul_pi",
            ("Cot", 1) => "Real.cos_add_int_mul_pi, Real.sin_add_int_mul_pi",
            _ => return Err(invalid("Period")),
        };
        let shift = if name == "Cot" {
            format!("have _cot_shift : Litex.nativeCot {angle} = Litex.nativeCot {base} := (by simp only [Litex.nativeCot]; rw [{law}, mul_div_mul_left _ _ (zpow_ne_zero _ (by norm_num))]); rw [_cot_shift]; ")
        } else {
            format!("rw [{law}]; ")
        };
        Ok(format!("((congrArg (Litex.realUnaryValue (M := M) {operation}) {denotation}).trans ((Litex.realUnaryValue_number (M := M) {operation} {angle}).trans ((congrArg M.number (show (({operation} {angle}) : ℂ) = (({value} : ℝ) : ℂ) from (by {shift}{closed}))).trans ({value_denotation}).symm)))"))
    }

    pub(in crate::compile_to_lean) fn compile_periodic_trig_nonzero(
        &self,
        fact: &AtomicFact,
        proof: &PeriodicTrigNonzeroBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = fact else {
            return Err(invalid("NonzeroSubject"));
        };
        let (object, zero, reversed) = if trig_argument(&fact.left).is_some() {
            (&fact.left, &fact.right, false)
        } else {
            (&fact.right, &fact.left, true)
        };
        let (name, argument) = trig_argument(object).ok_or_else(|| invalid("NonzeroSubject"))?;
        if !matches!(name, "Sin" | "Cos") || !is_exact_zero(zero) {
            return Err(invalid("NonzeroSubject"));
        }
        let terms = coefficient_terms(argument, &proof.coefficient)?;
        let reduced = terms
            .constant
            .modulo_integer(1)
            .ok_or_else(|| invalid("NonzeroAngle"))?;
        if (name == "Sin" && reduced.is_zero()) || (name == "Cos" && reduced.parts() == (1, 2)) {
            return Err(invalid("NonzeroAngle"));
        }
        let (angle, denotation) = self.compile_integer_period_angle(
            argument,
            &terms,
            &proof.integer_requirements,
            1,
            position,
        )?;
        let operation = trig_native_operation(name)?;
        let object_denotation = self.compile_normalization_denotation(object, position)?;
        let numeric = format!("(({object_denotation}).trans ((congrArg (Litex.realUnaryValue (M := M) {operation}) {denotation}).trans (Litex.realUnaryValue_number (M := M) {operation} {angle})))");
        let constant = exact_rational_literal(&terms.constant, "ℝ")?;
        let base = format!("({constant} * Real.pi)");
        let nonzero = rational_angle_nonzero(name, &terms.constant)?;
        let op = name.to_lowercase();
        let tactic = format!("have _base_nonzero : {operation} {base} ≠ 0 := {nonzero}; have _shift_nonzero : {operation} {angle} ≠ 0 := (by rw [Real.{op}_add_int_mul_pi]; exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) _base_nonzero); exact_mod_cast _shift_nonzero");
        let zero_value = self.compile_numeric_observation(zero, position)?;
        let result = format!("(Litex.NativeBridge.notSameOfDenoteNumber {} {} (({operation} {angle}) : ℂ) {} {numeric} {} (by {tactic}))", self.compile_object_reference(object, position)?, self.compile_object_reference(zero, position)?, zero_value.0, zero_value.1);
        Ok(if reversed {
            format!("(fun _reversed => {result} _reversed.symm)")
        } else {
            result
        })
    }

    /// Return a real angle and a closed proof of its raw source denotation.
    /// Integer observations depend only on raw values; local evidence stays
    /// inside the proof and cannot leak into the returned angle expression.
    fn compile_integer_period_angle(
        &self,
        argument: &Obj,
        terms: &CoefficientTerms,
        requirements: &[VerifyFactResult],
        period: i128,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let active = terms
            .terms
            .iter()
            .filter(|(scale, _)| !scale.is_zero())
            .collect::<Vec<_>>();
        if active.len() != requirements.len() || !matches!(period, 1 | 2) {
            return Err(invalid("Requirements"));
        }
        let mut lines = Vec::new();
        for (i, ((scale, term), result)) in active.iter().zip(requirements).enumerate() {
            let scale = scale
                .to_i128_if_integer()
                .ok_or_else(|| invalid("IntegralScale"))?;
            if scale % period != 0
                || !matches!(&source_subject(result)?, Fact::AtomicFact(AtomicFact::InFact(f))
                    if &f.element == term && matches!(f.set, Obj::StandardSet(StandardSet::Z)))
            {
                return Err(invalid("PeriodRequirement"));
            }
            let scope = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                i,
            );
            let compiled = self.compile_verify(result, &scope)?;
            // This certificate is always a term-level proof, even when its
            // source statement is at the top level. Source ownership controls
            // citation visibility; it must not turn this local producer into
            // a nested exported theorem.
            lines.push(format!(
                "have h_{} : {} :=\n  {}",
                source_subject(result)?.fact_id().value(),
                compiled.0,
                self.share_local_proof(&compiled.1, true)
                    .replace('\n', "\n  ")
            ));
        }
        let complete = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            requirements.len(),
        );
        let mut offsets = Vec::new();
        let mut real_offsets = Vec::new();
        let mut real_terms = Vec::new();
        let mut complex_terms = Vec::new();
        let mut combination = Vec::new();
        for (i, ((scale, term), result)) in active.iter().zip(requirements).enumerate() {
            let raw = self.compile_normalization_value(term, &complete)?;
            let integer = format!("(Litex.NativeBridge.integerValue {raw})");
            let member = self.compile_period_integer_membership(term, result, &complete)?;
            let (native, denotation) =
                self.compile_periodic_complex_value(term, requirements, &complete, 0)?;
            lines.push(format!("have _period_native_{i} : ({native} : ℂ) = ({integer} : ℂ) := M.number_injective (({denotation}).symm.trans (Litex.NativeBridge.integerValue_spec {raw} {member}))"));
            let integer_scale = scale
                .to_i128_if_integer()
                .ok_or_else(|| invalid("IntegralScale"))?;
            offsets.push(format!("({} : ℤ) * {integer}", integer_scale / period));
            real_offsets.push(format!(
                "({} : ℝ) * ({integer} : ℝ)",
                integer_scale / period
            ));
            let real_scale = exact_rational_literal(scale, "ℝ")?;
            let complex_scale = exact_rational_literal(scale, "ℂ")?;
            real_terms.push(format!("{real_scale} * ({integer} : ℝ)"));
            complex_terms.push(format!("{complex_scale} * ({integer} : ℂ)"));
            combination.push(format!(
                "({complex_scale} * (Real.pi : ℂ)) * _period_native_{i}"
            ));
        }
        let sum = |parts: Vec<String>| {
            if parts.is_empty() {
                "0".into()
            } else {
                format!("({})", parts.join(" + "))
            }
        };
        let constant_r = exact_rational_literal(&terms.constant, "ℝ")?;
        let constant_c = exact_rational_literal(&terms.constant, "ℂ")?;
        let cycle = if period == 1 {
            "Real.pi"
        } else {
            "(2 * Real.pi)"
        };
        let angle = format!(
            "({constant_r} * Real.pi + (({} : ℤ) : ℝ) * {cycle})",
            sum(offsets)
        );
        let expanded_angle = format!("({constant_r} * Real.pi + {} * {cycle})", sum(real_offsets));
        let real_form = format!("({constant_r} * Real.pi + {} * Real.pi)", sum(real_terms));
        let complex_form = format!(
            "({constant_c} * (Real.pi : ℂ) + {} * (Real.pi : ℂ))",
            sum(complex_terms)
        );
        let (native, denotation) =
            self.compile_periodic_complex_value(argument, requirements, &complete, 0)?;
        let normalize = if combination.is_empty() {
            "ring".into()
        } else {
            format!("linear_combination {}", combination.join(" + "))
        };
        lines.push(format!(
            "have _period_angle : ({native} : ℂ) = {complex_form} := (by {normalize})"
        ));
        lines.push(format!("have _period_cast : {complex_form} = (({angle} : ℝ) : ℂ) := (Eq.trans (show {complex_form} = (({real_form} : ℝ) : ℂ) from (by norm_num only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_neg])) (congrArg Complex.ofReal (Eq.trans (by ring : {real_form} = {expanded_angle}) (show {expanded_angle} = {angle} from (by norm_num only [Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_one, Int.cast_zero])))))"));
        lines.push(format!(
            "exact ({denotation}).trans (congrArg M.number (_period_angle.trans _period_cast))"
        ));
        Ok((
            angle,
            format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  ")),
        ))
    }

    fn compile_period_integer_membership(
        &self,
        object: &Obj,
        result: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let subject = source_subject(result)?;
        if !matches!(&subject, Fact::AtomicFact(AtomicFact::InFact(f))
            if &f.element == object && matches!(f.set, Obj::StandardSet(StandardSet::Z)))
        {
            return Err(invalid("IntegerSubject"));
        }
        let bridge = self.compile_normalization_denotation(object, position)?;
        Ok(format!(
            "(Eq.mp (congrArg (fun x => M.mem x (M.standard .integer)) {bridge}) h_{})",
            subject.fact_id().value()
        ))
    }

    /// Arithmetic intermediates need denotation equations, not new Obj WD.
    /// Opaque leaves consume original integer premises or original numeric WD.
    fn compile_periodic_complex_value(
        &self,
        object: &Obj,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
        depth: usize,
    ) -> Result<(String, String), LeanCompileError> {
        if depth >= 64 {
            return Err(invalid("ValueDepth"));
        }
        if let Some(value) = EvalRational::from_obj(object) {
            let (_, denotation) = self.compile_eval_closed_value(object, position)?;
            return Ok((exact_rational_literal(&value, "ℂ")?, denotation));
        }
        if matches!(object, Obj::Literal(Literal::Pi(_))) {
            let raw = self.compile_normalization_value(object, position)?;
            return Ok((
                "(Real.pi : ℂ)".into(),
                format!("(rfl : {raw} = M.number (Real.pi : ℂ))"),
            ));
        }
        if let Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) = object {
            let (arg, proof) =
                self.compile_periodic_complex_value(&p.arg, requirements, position, depth + 1)?;
            return Ok((
                format!("(-{arg})"),
                format!("((congrArg M.negValue {proof}).trans (M.neg_numbers {arg}))"),
            ));
        }
        let pair = match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => {
                Some((&p.left, &p.right, "add", "+"))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => {
                Some((&p.left, &p.right, "sub", "-"))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => {
                Some((&p.left, &p.right, "mul", "*"))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => {
                Some((&p.left, &p.right, "div", "/"))
            }
            _ => None,
        };
        if let Some((left, right, op, symbol)) = pair {
            if op == "div" && !EvalRational::from_obj(right).is_some_and(|x| !x.is_zero()) {
                return Err(invalid("RationalDenominator"));
            }
            let (a, ha) =
                self.compile_periodic_complex_value(left, requirements, position, depth + 1)?;
            let (b, hb) =
                self.compile_periodic_complex_value(right, requirements, position, depth + 1)?;
            let nonzero = if op == "div" { " (by norm_num)" } else { "" };
            return Ok((
                format!("({a} {symbol} {b})"),
                format!(
                    "((congrArg₂ M.{op}Value {ha} {hb}).trans (M.{op}_numbers {a} {b}{nonzero}))"
                ),
            ));
        }
        for result in requirements {
            let subject = source_subject(result)?;
            if matches!(&subject, Fact::AtomicFact(AtomicFact::InFact(f)) if &f.element == object) {
                let raw = self.compile_normalization_value(object, position)?;
                let member = self.compile_period_integer_membership(object, result, position)?;
                return Ok((
                    format!("((Litex.NativeBridge.integerValue {raw}) : ℂ)"),
                    format!("(Litex.NativeBridge.integerValue_spec {raw} {member})"),
                ));
            }
        }
        let observed = self.compile_numeric_observation(object, position)?;
        let bridge = self.compile_normalization_denotation(object, position)?;
        Ok((
            observed.0,
            format!("(({bridge}).symm.trans {})", observed.1),
        ))
    }
}
