use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    // Only the exact subject of a visible named inference enters here. Its
    // arithmetic constructors keep the original shape and prove their own WD.
    pub(in crate::compile_to_lean) fn compile_inferred_numeric_observation(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String, Option<EvalRational>), LeanCompileError> {
        match object {
            Obj::Literal(Literal::Number(number)) => {
                let value = number_literal(number, "ℂ")?;
                return Ok((
                    value.clone(),
                    format!("(Litex.NativeBridge.denoteNumber (M := M) {value})"),
                    format!("(Litex.numberInC (M := M) {value})"),
                    EvalRational::from_obj(object),
                ));
            }
            Obj::Identifier(IdentifierObj::Plain { id, .. })
                if position.visible_parameter(*id, &self.runtime).is_ok() =>
            {
                return self.compile_numeric_observation(object, position);
            }
            Obj::FnObj(_) => return self.compile_numeric_observation(object, position),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) => {
                let (arguments, n) = self.inferred_nat_power_arguments(power, position)?;
                let base = self.compile_inferred_numeric_observation(&power.base, position)?;
                return Ok((
                    format!("({} ^ ({n} : ℕ))", base.0),
                    format!("(Litex.NativeBridge.denotePowNat {arguments} _ {})", base.1),
                    format!("(Litex.powNatInC {arguments})"),
                    EvalRational::from_obj(object),
                ));
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(op)) => {
                let (a, member) = self.compile_inferred_numeric_obj(&op.arg, position)?;
                let child = self.compile_inferred_numeric_observation(&op.arg, position)?;
                return Ok((
                    format!("(-{})", child.0),
                    format!("(Litex.NativeBridge.denoteNeg {a} {member} _ {})", child.1),
                    format!("(Litex.negInC {a} {member})"),
                    EvalRational::from_obj(object),
                ));
            }
            _ => {}
        }
        let (operation, left, right) = match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(op)) => {
                (BinaryArithmetic::Add, &op.left, &op.right)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(op)) => {
                (BinaryArithmetic::Sub, &op.left, &op.right)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(op)) => {
                (BinaryArithmetic::Mul, &op.left, &op.right)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(op)) => {
                (BinaryArithmetic::Div, &op.left, &op.right)
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Inference/NumericObservation",
                ))
            }
        };
        let (a, ha) = self.compile_inferred_numeric_obj(left, position)?;
        let (b, hb) = self.compile_inferred_numeric_obj(right, position)?;
        let x = self.compile_inferred_numeric_observation(left, position)?;
        let y = self.compile_inferred_numeric_observation(right, position)?;
        let guard = if matches!(operation, BinaryArithmetic::Div) {
            format!(" {}", self.compile_inferred_nonzero(right, position)?)
        } else {
            String::new()
        };
        let (name, symbol, bridge) = operation.names();
        Ok((
            format!("({} {symbol} {})", x.0, y.0),
            format!(
                "(Litex.NativeBridge.denote{bridge} {a} {b} {ha} {hb}{guard} _ _ {} {})",
                x.1, y.1
            ),
            format!("(Litex.{name}InC {a} {b} {ha} {hb}{guard})"),
            EvalRational::from_obj(object),
        ))
    }

    // Called only for an object in the selected named rule's conclusion store.
    // Lean constructors establish formation; no Verify WD record is invented.
    pub(in crate::compile_to_lean) fn compile_inferred_obj(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match object {
            Obj::StandardSet(set) => standard_term(set),
            _ => self
                .compile_inferred_numeric_obj(object, position)
                .map(|p| p.0),
        }
    }

    pub(in crate::compile_to_lean) fn compile_inferred_numeric_obj(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if let Obj::Literal(Literal::Number(number)) = object {
            let value = number_literal(number, "ℂ")?;
            return Ok((
                format!("(Litex.number (M := M) {value})"),
                format!("(Litex.numberInC (M := M) {value})"),
            ));
        }
        if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = object {
            let (arguments, _) = self.inferred_nat_power_arguments(power, position)?;
            return Ok((
                format!("(Litex.powNat {arguments})"),
                format!("(Litex.powNatInC {arguments})"),
            ));
        }
        let (lemma, left, right) = match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(op)) => ("add", &op.left, &op.right),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(op)) => ("sub", &op.left, &op.right),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(op)) => ("mul", &op.left, &op.right),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(op)) => ("div", &op.left, &op.right),
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(op)) => {
                let (a, ha) = self.compile_inferred_numeric_obj(&op.arg, position)?;
                return Ok((
                    format!("(Litex.neg {a} {ha})"),
                    format!("(Litex.negInC {a} {ha})"),
                ));
            }
            Obj::Identifier(_) => {
                let term = self.compile_object_reference(object, position)?;
                let (_, _, member, _) = self.compile_numeric_observation(object, position)?;
                return Ok((term, member));
            }
            Obj::FnObj(_) => {
                let term = if let Some(term) = position.bound_object_child(object) {
                    term
                } else if let Some(term) = position.registered_wd_reference(object, None)? {
                    term
                } else if let Some(term) = position.with_visible_inferred_subject_filter(
                    object,
                    &mut |store, producer| {
                        self.compile_cart_inferred_subject(object, store, producer)
                    },
                )? {
                    term
                } else {
                    position
                        .with_visible_wd(object, &mut |wd, producer| self.compile_wd(wd, producer))?
                        .ok_or_else(|| {
                            LeanCompileError::unsupported(
                                "Inference/FunctionApplicationConstructor",
                            )
                        })?
                };
                let (_, _, member, _) = self.compile_numeric_observation(object, position)?;
                return Ok((term, member));
            }
            _ => return Err(LeanCompileError::unsupported("Inference/ObjectConstructor")),
        };
        let (a, ha) = self.compile_inferred_numeric_obj(left, position)?;
        let (b, hb) = self.compile_inferred_numeric_obj(right, position)?;
        let guard = if lemma == "div" {
            let proof = self.compile_inferred_nonzero(right, position)?;
            format!(" {proof}")
        } else {
            String::new()
        };
        Ok((
            format!("(Litex.{lemma} {a} {b} {ha} {hb}{guard})"),
            format!("(Litex.{lemma}InC {a} {b} {ha} {hb}{guard})"),
        ))
    }

    fn inferred_nat_power_arguments(
        &self,
        power: &Pow,
        position: &SourcePosition<'_>,
    ) -> Result<(String, i128), LeanCompileError> {
        let Obj::Literal(Literal::Number(number)) = power.exponent.as_ref() else {
            return Err(LeanCompileError::unsupported("Inference/PowerExponent"));
        };
        let n = closed_integer(&power.exponent)
            .filter(|n| *n >= 0)
            .ok_or_else(|| LeanCompileError::unsupported("Inference/PowerExponent"))?;
        let (base, member) = self.compile_inferred_numeric_obj(&power.base, position)?;
        let scalar = number_literal(number, "ℂ")?;
        let value = format!("(Litex.number (M := M) {scalar})");
        let h_n =
            format!("(Litex.NativeBridge.numberInNOfEq (M := M) {scalar} ({n} : ℕ) (by norm_num))");
        let h_value = format!("(Litex.NativeBridge.sameOfDenoteNumber {value} (Litex.number (M := M) (({n} : ℕ) : ℂ)) {scalar} (({n} : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) {scalar}) (Litex.NativeBridge.denoteNumber (M := M) (({n} : ℕ) : ℂ)) (by norm_num))");
        Ok((
            format!("{base} {value} ({n} : ℕ) {member} {h_n} {h_value}"),
            n,
        ))
    }

    fn compile_inferred_nonzero(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Obj::Literal(Literal::Number(number)) = object {
            if is_exact_zero(object) {
                return Err(LeanCompileError::new(
                    "Inference/ZeroDenominator",
                    "A named rule generated an undefined quotient.",
                ));
            }
            let value = number_literal(number, "ℂ")?;
            return Ok(format!(
                "(Litex.NativeBridge.numberNonzero (M := M) {value} (by norm_num))"
            ));
        }
        // Reuse an actual visible input/earlier projection, not a new proof search.
        if let Some(proof) = position
            .with_visible_nonzero(
                object,
                &mut |id, _| match self.cited_fact_reference(id, position) {
                    Ok((_, proof)) => Ok(Some(proof)),
                    Err(_) => Ok(None),
                },
            )?
            .flatten()
        {
            return Ok(proof);
        }
        Err(LeanCompileError::unsupported("Inference/NonzeroInput"))
    }
}
