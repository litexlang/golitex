use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_nonzero_product(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let goal = match fact {
            AtomicFact::NotEqualFact(x) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "Product nonzero evidence has another fact family.",
                ))
            }
        };
        let (expression, reversed) = if is_zero(&goal.right) {
            (&goal.left, false)
        } else if is_zero(&goal.left) {
            (&goal.right, true)
        } else {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Subject",
                "The product guard does not compare with zero.",
            ));
        };
        let product = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "The certified nonzero object is not a product.",
                ))
            }
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Requirements",
                "The product needs two ordered factor proofs.",
            ));
        }
        let mut compiled = Vec::new();
        for ((requirement, proof), child) in requirements
            .iter()
            .zip(proofs)
            .zip([product.left.as_ref(), product.right.as_ref()])
        {
            ensure_nonzero_subject(requirement, child)?;
            let proved = self.compile_verify(proof, position)?;
            if &source_subject(proof)? != requirement {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/RequirementSubject",
                    "A factor proof differs from its ordered requirement.",
                ));
            }
            let native = self.compile_numeric_observation(child, position)?;
            compiled.push(format!(
                "(Litex.NativeBridge.nativeNonzeroOfDenote {} {} {} {})",
                self.compile_object_reference(child, position)?,
                native.0,
                native.1,
                proved.1
            ));
        }
        let native = self.compile_numeric_observation(expression, position)?;
        let proof = format!("(Litex.NativeBridge.notSameOfDenoteNumber {} (Litex.number (M := M) (0 : ℂ)) {} (0 : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero {} {}))", self.compile_object_reference(expression, position)?, native.0, native.1, compiled[0], compiled[1]);
        Ok(if reversed {
            format!("(fun h => {proof} h.symm)")
        } else {
            proof
        })
    }
}
