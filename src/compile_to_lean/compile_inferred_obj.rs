use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
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

    fn compile_inferred_numeric_obj(
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
                let term = position
                    .with_visible_wd(object, &mut |wd, producer| self.compile_wd(wd, producer))?
                    .ok_or_else(|| {
                        LeanCompileError::unsupported("Inference/FunctionApplicationConstructor")
                    })?;
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
                "(Litex.numberNonzero (M := M) {value} (by norm_num))"
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
