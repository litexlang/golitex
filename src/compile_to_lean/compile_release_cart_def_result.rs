use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_release_cart_def_stmt::ExecReleaseCartDefStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_release_cart_definition(
        &self,
        result: &ExecReleaseCartDefStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseCartDefStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("ReleaseCart/Failed"));
        };
        let expected = Obj::ProductShape(ProductShape::Cart(proof.statement.cart.clone()));
        if proof.verification.fact.left.ir() != expected.ir() {
            return Err(LeanCompileError::unsupported("ReleaseCart/Subject"));
        }
        super::compile_fact_stmt_result::validate_cart_definition(
            &proof.statement.cart,
            &proof.verification.fact.right,
        )?;
        let fact = Fact::AtomicFact(AtomicFact::EqualFact(proof.verification.fact.clone()));
        self.validate_store(&proof.store_and_infer.store, &fact)?;
        let compiled = self.compile_equality_success(&proof.verification, position)?;
        let before_store = SourcePosition {
            before: 3,
            ..*position
        };
        let mut declarations =
            vec![self.emit_fact(&fact, compiled.clone(), index, local, &before_store)?];
        let published = SourcePosition {
            before: 4,
            ..*position
        };
        let name = format!("h_{}", fact.fact_id().value());
        let reference = if local {
            name
        } else {
            self.context_application(&name, &published)
        };
        declarations.extend(self.compile_stored_inferences(
            &proof.store_and_infer,
            &fact,
            &(compiled.0, reference),
            &published,
        )?);
        Ok(declarations.join("\n\n"))
    }
}
