//! Interpret the exact finite signature retained by a complete-domain source.
use super::compile_fact_stmt_result::validate_finite_signature;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof;
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_complete_signature(
        &self,
        proof: &FiniteFunctionSignatureProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_finite_signature(proof)?;
        let cart = match &proof.source {
            KnownTupleShapeProof::TupleEquality(value) => {
                let tuple = Obj::ProductShape(ProductShape::Tuple(value.value.clone()));
                let tuple = self.compile_object_reference(&tuple, position)?;
                format!("(Litex.tupleSingletonCart {tuple})")
            }
            source => {
                let cart = source
                    .cart()
                    .ok_or_else(|| LeanCompileError::unsupported("FiniteDomain/OriginalFactors"))?;
                self.compile_object_reference(
                    &Obj::ProductShape(ProductShape::Cart(cart.clone())),
                    position,
                )?
            }
        };
        Ok(format!("(Litex.cartCompleteSignature {cart})"))
    }

    pub(in crate::compile_to_lean) fn compile_finite_complete_member(
        &self,
        subject: &Obj,
        proof: &FiniteFunctionSignatureProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_finite_signature(proof)?;
        let (cart, member) = self.compile_cart_shape_member(subject, &proof.source, position)?;
        let subject = self.compile_object_reference(subject, position)?;
        Ok(format!(
            "(Litex.cartMemberInCompleteSignature {subject} {cart} {member})"
        ))
    }
}
