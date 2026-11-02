use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_let_result(
        &self,
        result: &ExecLetObjStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecLetObjStmtResult::Success(proof) => self.compile_let(proof, position, local),
            ExecLetObjStmtResult::Failed(_) => Err(LeanCompileError::new(
                "Declaration/Failed",
                "Failed declaration is not compiler evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_let(
        &self,
        proof: &ExecLetObjStmtSuccessResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let wd = success_object_wd(&proof.value_well_defined, &proof.statement.value)?;
        let value = self.compile_wd(wd, position)?;
        let Some(seed_id) = proof.stored_fact_ids.first() else {
            return Err(LeanCompileError::unsupported("Let/Inference"));
        };
        let fact = self.resolve_fact(*seed_id, position)?;
        let left = alias_equality_subject(
            &fact,
            &proof.statement.name,
            &proof.statement.value,
            position,
            &self.runtime,
        )?;
        if proof.stored_fact_ids != proof.store_and_infer_result.stored_fact_ids() {
            return Err(LeanCompileError::unsupported("Let/Inference"));
        }
        self.validate_store(&proof.store_and_infer_result.store, &fact)?;
        let declaration = self.bind_alias(
            &proof.statement.name,
            left,
            &proof.statement.value,
            &value,
            local,
            position,
        )?;
        let after_alias = SourcePosition {
            before: 1,
            ..*position
        };
        let compiled = (
            self.fact_proposition(&fact, &after_alias)?,
            format!("(Litex.sameRefl {value})"),
        );
        let emitted = self.emit_internal_fact(&fact, &compiled, &after_alias)?;
        let inferred = self.compile_stored_inferences(
            &proof.store_and_infer_result,
            &fact,
            &compiled,
            &after_alias,
        )?;
        Ok(format!("{declaration}\n{emitted}\n{}", inferred.join("\n")))
    }

    pub(in crate::compile_to_lean) fn bind_alias(
        &self,
        parameter: &BoundName,
        _object: &Obj,
        _value_object: &Obj,
        value: &str,
        local: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let name = format!("_object_i{}", parameter.id.value());
        Ok(if local {
            format!("let {name} := {value}")
        } else {
            format!(
                "noncomputable def {name}{} := {value}",
                self.context_header(position)?
            )
        })
    }
}
