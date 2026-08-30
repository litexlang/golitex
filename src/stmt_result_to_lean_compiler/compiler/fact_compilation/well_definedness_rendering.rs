//! Fact well-definedness stores and result-aware rendering.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Compile a recursively checked fact under the exact WD occurrence map
    /// owned by that Result. Structured proof children do not pass through the
    /// ordinary statement dispatcher, so callers use this helper to install
    /// their intrinsic object-membership stores before replaying the proof.
    pub(in super::super) fn construct_direct_fact_proof_with_result_owned_well_definedness(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        let child_certificate = result
            .well_definedness
            .recursive
            .as_ref()
            .map(|_| {
                self.construct_well_definedness_to_lean_compilation_context(
                    &result.well_definedness,
                )
            })
            .transpose()?;
        let parent_certificate = child_certificate
            .map(|certificate| self.environment_stack.well_definedness.replace(certificate));
        let compiled = (|| {
            if let Some(recursive) = result.well_definedness.recursive.as_deref() {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    recursive,
                    &mut self.environment_stack,
                )?;
            }
            let Some(proof_expression) =
                self.construct_lean_proof_from_direct_fact_result(result)?
            else {
                return Ok(None);
            };
            let fact = result.fact();
            let proposition = render_fact(&fact, &self.environment_stack)?;
            Ok(Some(CompiledFactProofBody {
                fact,
                proposition,
                proof_expression,
            }))
        })();
        if let Some(parent_certificate) = parent_certificate {
            self.environment_stack.well_definedness = parent_certificate;
        }
        compiled
    }

    /// Some object-WD constructors intentionally store a fact for later
    /// statements. Function application is the important example: checking
    /// `f(x)` stores `f(x) $in ReturnSet` under a real FactId. These are not
    /// display-only WD details, so the compiler installs their proof bindings
    /// before compiling the enclosing fact proof.
    pub(in super::super) fn install_atomic_fact_well_definedness_store_results(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<(), String> {
        self.install_fact_well_definedness_store_results(&result.well_definedness, &result.fact())
    }

    /// Install the observable stores owned by one exact fact-WD child layer.
    /// Nested verifier Results (for example a forall conclusion) may own their
    /// WD result in the parent's named `conclusions` field while their factual
    /// execution Result intentionally carries no duplicate certificate.
    pub(in super::super) fn install_fact_well_definedness_store_results(
        &mut self,
        well_definedness: &SuccessVerifyFactWellDefinedResult,
        _source_fact: &Fact,
    ) -> Result<(), String> {
        let Some(recursive) = well_definedness.recursive.as_deref() else {
            return Ok(());
        };
        if !fact_well_definedness_result_contains_outer_intrinsic_store(recursive) {
            return Ok(());
        }
        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(well_definedness)?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let installation = install_fact_well_definedness_proof_store_results_in_active_environment(
            recursive,
            &mut self.environment_stack,
        );
        self.environment_stack.well_definedness = previous_well_definedness;
        installation
    }

    pub(in super::super) fn render_object_using_well_definedness_from_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
        object: &Obj,
    ) -> Result<String, String> {
        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(&result.well_definedness)?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let rendered = render_obj(object, &self.environment_stack);
        self.environment_stack.well_definedness = previous_well_definedness;
        rendered
    }

    pub(in super::super) fn render_fact_using_well_definedness_result(
        &mut self,
        result: &SuccessVerifyFactWellDefinedResult,
        fact: &Fact,
    ) -> Result<String, String> {
        let certificate = self.construct_well_definedness_to_lean_compilation_context(result)?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let rendered = render_fact(fact, &self.environment_stack);
        self.environment_stack.well_definedness = previous_well_definedness;
        rendered
    }
}
