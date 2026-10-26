use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_trig::trig_argument;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reciprocal_trig::ReciprocalTrigEqualityProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_trig_left_inverse(
        &self,
        fact: &EqualFact,
        outer: &str,
        inverse: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((op, inner)) = trig_argument(object) else {
                continue;
            };
            let Some((inv, argument)) = trig_argument(inner) else {
                continue;
            };
            if op != outer || inv != inverse || argument.ir() != other.ir() {
                continue;
            }
            // The exact inner constructor owns the bounds required by the selected law.
            let term = self.compile_object_reference(inner, position)?;
            let proof = format!("(Litex.{}{inverse} {term})", outer.to_lowercase());
            return Ok(if reversed {
                format!("{proof}.symm")
            } else {
                proof
            });
        }
        Err(LeanCompileError::unsupported("Trig/LeftInverseSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_inverse_trig_exact(
        &self,
        fact: &EqualFact,
        kind: &str,
        input: i128,
        pi_result: Option<(i128, i128)>,
        law: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((op, argument)) = trig_argument(object) else {
                continue;
            };
            if op != kind || EvalRational::from_obj(argument) != EvalRational::new(input, 1) {
                continue;
            }
            let matches_value = if let Some((n, d)) = pi_result {
                crate::rational_expression::pi_multiple::pi_coefficient(other)
                    .and_then(|c| EvalRational::from_obj(&c))
                    == EvalRational::new(n, d)
            } else {
                is_exact_zero(other)
            };
            if !matches_value {
                continue;
            }
            return self.compile_trig_native_identity(fact,
                &format!("{}norm_num [Litex.nativeArccot, {law}, Complex.ofReal_div, Complex.ofReal_neg, neg_div]", if reversed { "symm; " } else { "" }), position);
        }
        Err(LeanCompileError::unsupported("Trig/InverseExactSubject"))
    }

    pub(in crate::compile_to_lean) fn compile_reciprocal_trig_definition(
        &self,
        fact: &EqualFact,
        kind: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let denominator = if kind == "Sec" { "Cos" } else { "Sin" };
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((op, argument)) = trig_argument(object) else {
                continue;
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Div(d)) = other else {
                continue;
            };
            if op != kind
                || !matches!(trig_argument(&d.right), Some((op, a)) if op == denominator && a.ir() == argument.ir())
            {
                continue;
            }
            let numerator = if kind == "Cot" {
                matches!(trig_argument(&d.left), Some(("Cos", a)) if a.ir() == argument.ir())
            } else {
                EvalRational::from_obj(&d.left) == EvalRational::new(1, 1)
            };
            if !numerator {
                continue;
            }
            let one_cast = if kind == "Cot" {
                ""
            } else {
                ", Complex.ofReal_one"
            };
            return self.compile_trig_native_identity(
                fact,
                &format!(
                    "{}simp only [Litex.native{kind}, Complex.ofReal_div{one_cast}]",
                    if reversed { "symm; " } else { "" }
                ),
                position,
            );
        }
        Err(LeanCompileError::unsupported(
            "Trig/ReciprocalDefinitionSubject",
        ))
    }

    pub(in crate::compile_to_lean) fn compile_reciprocal_trig(
        &self,
        fact: &EqualFact,
        proof: &ReciprocalTrigEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use ReciprocalTrigEqualityProof::*;
        let (kind, coefficient, expected) = match proof {
            SecDefinition(_) => {
                return self.compile_reciprocal_trig_definition(fact, "Sec", position)
            }
            CscDefinition(_) => {
                return self.compile_reciprocal_trig_definition(fact, "Csc", position)
            }
            SecZero(_) => ("Sec", None, 1),
            SecPi(_) => ("Sec", Some((1, 1)), -1),
            CscHalfPi(_) => ("Csc", Some((1, 2)), 1),
            _ => return Err(LeanCompileError::unsupported("Trig/ReciprocalRule")),
        };
        for (object, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Some((op, argument)) = trig_argument(object) else {
                continue;
            };
            if op != kind || EvalRational::from_obj(other) != EvalRational::new(expected, 1) {
                continue;
            }
            let matches_angle = if let Some((n, d)) = coefficient {
                crate::rational_expression::pi_multiple::pi_coefficient(argument)
                    .and_then(|c| EvalRational::from_obj(&c))
                    == EvalRational::new(n, d)
            } else {
                is_exact_zero(argument)
            };
            if !matches_angle {
                continue;
            }
            return self.compile_trig_native_identity(
                fact,
                &format!(
                    "{}norm_num [Litex.native{kind}]",
                    if reversed { "symm; " } else { "" }
                ),
                position,
            );
        }
        Err(LeanCompileError::unsupported("Trig/ReciprocalExactSubject"))
    }
}
