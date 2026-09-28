//! Direct universal fact local proof steps.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Reuse the complete direct-Forall Result compiler inside a structured
    /// proof. Its declarations are compiler-owned syntax, so changing their
    /// leading `theorem` to `have` preserves all exact FactId publications
    /// while keeping references to enclosing local binders in scope.
    pub(in super::super) fn compile_direct_forall_fact_result_as_local_proof_steps(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<Option<Vec<String>>, String> {
        let declaration_count = self.declarations.len();
        let compiled = self.compile_direct_forall_fact_result(result)?;
        if !compiled {
            return Ok(None);
        }
        if self.declarations.len() == declaration_count {
            return Err("local direct ForallProof emitted no declaration".into());
        }
        let declarations = self.declarations.split_off(declaration_count);
        declarations
            .into_iter()
            .map(|declaration| {
                declaration
                    .strip_prefix("theorem ")
                    .map(|body| format!("have {body}"))
                    .ok_or_else(|| {
                        "local direct ForallProof generated an unexpected declaration shape"
                            .to_string()
                    })
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Some)
    }

    /// Local counterpart for a forall produced by verification rather than
    /// by executing a factual statement. The emitted `have` is temporary and
    /// the verification node itself receives no persistent FactId.
    pub(in super::super) fn compile_direct_forall_verify_result_as_local_proof_steps(
        &mut self,
        result: &VerifiedFactResult,
    ) -> Result<Option<Vec<String>>, String> {
        let declaration_count = self.declarations.len();
        let compiled = self.compile_direct_forall_verify_result(result)?;
        if !compiled {
            return Ok(None);
        }
        if self.declarations.len() == declaration_count {
            return Err("local direct ForallProof emitted no declaration".into());
        }
        let declarations = self.declarations.split_off(declaration_count);
        declarations
            .into_iter()
            .map(|declaration| {
                declaration
                    .strip_prefix("theorem ")
                    .map(|body| format!("have {body}"))
                    .ok_or_else(|| {
                        "local direct ForallProof generated an unexpected declaration shape"
                            .to_string()
                    })
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Some)
    }
}
