use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_zero_product_cancel(
        &self,
        goal: &EqualFact,
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if requirements.len() != 2 {
            return Err(LeanCompileError::unsupported("ZeroProduct/Requirements"));
        }
        let (target, reverse) = if is_exact_zero(&goal.right) {
            (&goal.left, false)
        } else if is_exact_zero(&goal.left) {
            (&goal.right, true)
        } else {
            return Err(LeanCompileError::unsupported("ZeroProduct/Target"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(product_zero)) =
            source_subject(&requirements[0])?
        else {
            return Err(LeanCompileError::unsupported("ZeroProduct/ProductPremise"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = &product_zero.left else {
            return Err(LeanCompileError::unsupported("ZeroProduct/ProductPremise"));
        };
        if !is_exact_zero(&product_zero.right) {
            return Err(LeanCompileError::unsupported("ZeroProduct/ProductPremise"));
        }
        let nonzero = source_subject(&requirements[1])?;
        let target_left = if product.left.ir() == target.ir() {
            ensure_nonzero_subject(&nonzero, &product.right)?;
            true
        } else if product.right.ir() == target.ir() {
            ensure_nonzero_subject(&nonzero, &product.left)?;
            false
        } else {
            return Err(LeanCompileError::unsupported("ZeroProduct/Factor"));
        };
        let mut proofs = Vec::new();
        for (index, requirement) in requirements.iter().enumerate() {
            let prior = SourcePosition::new(
                Some(position),
                SourceOwner::EqualityRequirements(requirements),
                index,
            );
            proofs.push(self.compile_verify(requirement, &prior)?.1);
        }
        let complete = SourcePosition::new(
            Some(position),
            SourceOwner::EqualityRequirements(requirements),
            requirements.len(),
        );
        let product = self.compile_object_reference(&product_zero.left, &complete)?;
        let (left, right) = if target_left {
            ("_target_nonzero", proofs[1].as_str())
        } else {
            (proofs[1].as_str(), "_target_nonzero")
        };
        let proof = format!("(by\n  let _product := {product}\n  have _product_zero : Litex.Same _product (Litex.number 0) := {}\n  apply Classical.byContradiction\n  intro _target_nonzero\n  exact (Litex.mulNonzero _product.val.left _product.val.right _product.wd.1 _product.wd.2 {left} {right}) _product_zero\n)", proofs[0]);
        Ok(if reverse {
            format!("(Eq.symm {proof})")
        } else {
            proof
        })
    }
}
