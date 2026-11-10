use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_quotient_order(
        &self,
        goal: &AtomicFact,
        strategy: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use AtomicExceptEqualityFactSearchProofByBuiltinStrategy as Strategy;
        let (unit, strict, facts, proofs) = match strategy {
            Strategy::QuotientUnitLess(p) => (
                true,
                true,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            Strategy::QuotientUnitLessEqual(p) => (
                true,
                false,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            Strategy::QuotientScaleLess(p) => (
                false,
                true,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            Strategy::QuotientScaleLessEqual(p) => (
                false,
                false,
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            _ => return Err(LeanCompileError::unsupported("QuotientOrder/Strategy")),
        };
        let invalid = || LeanCompileError::unsupported("QuotientOrder/Subject");
        let (low, high, goal_strict) = source_order_oriented(goal)?;
        if strict != goal_strict
            || facts.len() != if unit { 2 } else { 3 }
            || proofs.len() != facts.len()
        {
            return Err(invalid());
        }
        let (quotient, other, quotient_low) = match (low, high) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Div(q)), other) => (q, other, true),
            (other, Obj::ArithmeticOperator(ArithmeticOperator::Div(q))) => (q, other, false),
            _ => return Err(invalid()),
        };
        if unit && !is_exact_one(other) || !unit && other != quotient.left.as_ref() {
            return Err(invalid());
        }
        let mut declarations = Vec::new();
        for (index, (fact, proof)) in facts.iter().zip(proofs).enumerate() {
            if source_subject(proof)? != *fact {
                return Err(invalid());
            }
            let (ty, term) = self.compile_verify(proof, &position.atomic_search_prior(index)?)?;
            declarations.push(format!(
                "  have _quotient_requirement_{index} : {ty} := {term}"
            ));
        }
        let complete = position.atomic_search_prior(proofs.len())?;
        let quotient_obj = if quotient_low { low } else { high };
        let q = self.compile_object_reference(quotient_obj, &complete)?;
        let other_term = self.compile_object_reference(other, &complete)?;
        let numerator_real = self.compile_real_membership_certificate(&quotient.left, &complete)?;
        let Fact::AtomicFact(positive) = &facts[0] else {
            return Err(invalid());
        };
        let (zero, divisor, positive_strict) = source_order_oriented(positive)?;
        if !positive_strict || !is_exact_zero(zero) || divisor != quotient.right.as_ref() {
            return Err(invalid());
        }
        declarations.push(format!("  let _quotient := {q}\n  obtain ⟨_b, _hb, _bpos⟩ := Litex.NativeBridge.realWitnessOfPositive _quotient.val.right _quotient_requirement_0\n  obtain ⟨_a, _ha⟩ := (M.real_members _).mp ({numerator_real})\n  have _hq : Litex.denote _quotient = M.number ((_a / _b : ℝ) : ℂ) := by\n    change M.divValue (Litex.denote _quotient.val.left) (Litex.denote _quotient.val.right) = _\n    have _numerator_value : Litex.denote _quotient.val.left = M.number (_a : ℂ) := _ha\n    rw [_numerator_value, _hb, M.div_numbers _ _ (by exact_mod_cast (ne_of_gt _bpos)), Complex.ofReal_div]"));
        let real_operand = |obj: &Obj| -> Result<(&str, &str), LeanCompileError> {
            if obj == quotient.left.as_ref() {
                Ok(("_a", "_ha"))
            } else if obj == quotient.right.as_ref() {
                Ok(("_b", "_hb"))
            } else if is_exact_zero(obj) {
                Ok(("0", "rfl"))
            } else if is_exact_one(obj) {
                Ok(("1", "rfl"))
            } else {
                Err(invalid())
            }
        };
        let mut signs = Vec::new();
        for (index, fact) in facts.iter().enumerate().skip(1) {
            let Fact::AtomicFact(fact) = fact else {
                return Err(invalid());
            };
            let (left, right, premise_strict) = source_order_oriented(fact)?;
            if premise_strict != strict {
                return Err(invalid());
            }
            let (a, ha) = real_operand(left)?;
            let (b, hb) = real_operand(right)?;
            signs.push((a, b));
            let relation = if strict { "<" } else { "≤" };
            declarations.push(format!("  have _order_{index} : {a} {relation} {b} := by\n    obtain ⟨x, y, hx, hy, hxy⟩ := _quotient_requirement_{index}\n    have ex : x = {a} := Complex.ofReal_injective (M.number_injective (hx.symm.trans ({ha})))\n    have ey : y = {b} := Complex.ofReal_injective (M.number_injective (hy.symm.trans ({hb})))\n    simpa only [ex, ey] using hxy"));
        }
        if unit {
            let expected = if quotient_low {
                ("_a", "_b")
            } else {
                ("_b", "_a")
            };
            if signs[0] != expected {
                return Err(invalid());
            }
        } else {
            let numerator_positive = signs[0] == ("0", "_a");
            if !numerator_positive && signs[0] != ("_a", "0") {
                return Err(invalid());
            }
            let above = quotient_low == numerator_positive;
            if signs[1] != if above { ("1", "_b") } else { ("_b", "1") } {
                return Err(invalid());
            }
            let sign_a = if numerator_positive {
                "_order_1".to_owned()
            } else {
                format!(
                    "(neg_{}.mpr _order_1)",
                    if strict { "pos" } else { "nonneg" }
                )
            };
            let sign_b = format!(
                "(sub_{}.mpr _order_2)",
                if strict { "pos" } else { "nonneg" }
            );
            declarations.push(format!(
                "  have _product := mul_{} {sign_a} {sign_b}",
                if strict { "pos" } else { "nonneg" }
            ));
        }
        let native = if strict { "lt" } else { "le" };
        let constructor = if strict {
            "ltOfDenoteReal"
        } else {
            "leOfDenoteReal"
        };
        let (left_term, right_term, left_value, right_value, left_eq, right_eq) = if quotient_low {
            (
                "_quotient".to_owned(),
                other_term,
                "(_a / _b)",
                if unit { "1" } else { "_a" },
                "_hq",
                if unit { "rfl" } else { "_ha" },
            )
        } else {
            (
                other_term,
                "_quotient".to_owned(),
                if unit { "1" } else { "_a" },
                "(_a / _b)",
                if unit { "rfl" } else { "_ha" },
                "_hq",
            )
        };
        let inequality = if quotient_low {
            format!("div_{native}_iff₀")
        } else {
            format!("{native}_div_iff₀")
        };
        declarations.push(format!("  exact Litex.NativeBridge.{constructor} {left_term} {right_term} {left_value} {right_value} ({left_eq}) ({right_eq}) (by\n    apply ({inequality} _bpos).mpr\n    nlinarith)"));
        Ok(format!("(by\n{}\n)", declarations.join("\n")))
    }
}

fn is_exact_one(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Number(number)) if number.normalized_value == "1")
}
