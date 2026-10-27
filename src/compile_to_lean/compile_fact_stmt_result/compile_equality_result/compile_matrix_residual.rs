//! Matrix residuals with the producer's checked beta steps on either endpoint.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    MatrixComponentDefinitionProof, MatrixResidualBeta, MatrixResidualBetaProof,
};
use crate::prelude::*;

fn beta_endpoints(beta: &MatrixResidualBeta) -> (&Obj, &Obj) {
    match beta {
        MatrixResidualBeta::Unchanged(value) => (value, value),
        MatrixResidualBeta::Expanded(p) => (p.application_well_defined.obj(), &p.body),
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_matrix_checked_residual(
        &self,
        fact: &EqualFact,
        component: &MatrixComponentDefinitionProof,
        beta: &MatrixResidualBetaProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (original_left, expanded_left) = beta_endpoints(&beta.left);
        let (original_right, expanded_right) = beta_endpoints(&beta.right);
        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) = source_subject(&beta.proof)? else {
            return Err(LeanCompileError::unsupported("Matrix/BetaResidualSubject"));
        };
        if original_left.ir() != component.reduction.value.ir()
            || expanded_left.ir() != residual.left.ir()
            || expanded_right.ir() != residual.right.ir()
        {
            return Err(LeanCompileError::unsupported(
                "Matrix/BetaResidualEndpoints",
            ));
        }
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            if !matches!(native, Obj::FnObj(_)) || original_right.ir() != other.ir() {
                continue;
            }
            let formed =
                SourcePosition::new(Some(position), SourceOwner::Verify(&beta.proof), usize::MAX);
            let original = self.compile_object_reference(native, position)?;
            let endpoint = self.compile_normalization_value(original_left, &formed)?;
            let bridge = position
                .with_visible_wd(native, &mut |wd, producer| {
                    let (value, step) = self.compile_matrix_component_step(
                        native,
                        &original,
                        &component.callable,
                        &component.body,
                        wd,
                        producer,
                    )?;
                    let reduced = self.compile_matrix_component_reduction(
                        &component.body,
                        &value,
                        &component.reduction,
                        &endpoint,
                        &formed,
                    )?;
                    Ok(format!("({step}.trans {reduced})"))
                })?
                .ok_or_else(|| LeanCompileError::unsupported("Matrix/BetaComponentProducer"))?;
            let left = self.compile_matrix_residual_beta(&beta.left, &formed)?;
            let right = self.compile_matrix_residual_beta(&beta.right, &formed)?;
            let checked = self.compile_verify(&beta.proof, position)?.1;
            let term =
                format!("({bridge}.trans ({left}.trans (({checked}).trans ({right}).symm)))");
            return Ok(if reversed {
                format!("({term}).symm")
            } else {
                term
            });
        }
        Err(LeanCompileError::unsupported("Matrix/BetaComponentSubject"))
    }

    fn compile_matrix_residual_beta(
        &self,
        beta: &MatrixResidualBeta,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match beta {
            MatrixResidualBeta::Unchanged(value) => Ok(format!(
                "(Eq.refl {})",
                self.compile_normalization_value(value, position)?
            )),
            MatrixResidualBeta::Expanded(p) => self.compile_parent_checked_function_body(
                p.application_well_defined.obj(),
                &p.application_well_defined,
                &p.source,
                &p.body,
                position,
            ),
        }
    }
}
