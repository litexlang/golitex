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
        self.compile_direct_forall_fact_result_as_local_proof_steps_with_optional_real_subset_observer(
            result, None,
        )
    }

    pub(in super::super) fn compile_direct_forall_fact_result_as_local_proof_steps_with_real_subset_observer(
        &mut self,
        result: &SuccessFactStmtResult,
        observed_set: &Obj,
        subset_proof: &str,
    ) -> Result<Option<Vec<String>>, String> {
        self.compile_direct_forall_fact_result_as_local_proof_steps_with_optional_real_subset_observer(
            result,
            Some((observed_set, subset_proof)),
        )
    }

    fn compile_direct_forall_fact_result_as_local_proof_steps_with_optional_real_subset_observer(
        &mut self,
        result: &SuccessFactStmtResult,
        real_subset_observer: Option<(&Obj, &str)>,
    ) -> Result<Option<Vec<String>>, String> {
        let declaration_count = self.declarations.len();
        let compiled = if let Some((observed_set, subset_proof)) = real_subset_observer {
            self.compile_direct_forall_fact_result_with_real_subset_observer(
                result,
                observed_set,
                subset_proof,
            )?
        } else {
            self.compile_direct_forall_fact_result(result)?
        };
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
