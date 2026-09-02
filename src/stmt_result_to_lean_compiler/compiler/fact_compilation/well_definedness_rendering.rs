//! Fact well-definedness stores and result-aware rendering.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Run one proof-construction operation in the lexical scope owned by the
    /// exact verified fact. Object-WD stores are process-local evidence: they
    /// may be cited while this Result is compiled, but they are discarded
    /// before the enclosing source statement publishes its own FactId.
    pub(in super::super) fn with_verified_fact_well_definedness_context<T>(
        &mut self,
        verified: &VerifiedFactResult,
        compile: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(&verified.checked)?;
        self.environment_stack.push_inherited_environment();
        self.environment_stack.well_definedness = Some(certificate);
        let compilation = (|| {
            install_fact_well_definedness_proof_store_results_in_active_environment(
                &verified.checked.proof,
                &mut self.environment_stack,
            )?;
            compile(self)
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    /// Compile a recursively checked fact under the exact WD occurrence map
    /// owned by that Result. Structured proof children do not pass through the
    /// ordinary statement dispatcher, so callers use this helper to install
    /// their intrinsic object-membership stores before replaying the proof.
    pub(in super::super) fn construct_direct_fact_proof_with_result_owned_well_definedness(
        &mut self,
        verified: &VerifiedFactResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        if let SuccessFactProofResult::StoredFactCitation(citation) = verified.proof() {
            let fact = verified.fact();
            if fact.to_string() == citation.source_fact.to_string() {
                if let Some(proposition) = self
                    .environment_stack
                    .fact_lean_propositions
                    .get(&citation.source_fact_id)
                    .cloned()
                {
                    let proof_expression = resolve_fact_citation(
                        &citation.source_fact_id,
                        &fact,
                        &self.environment_stack,
                    )?;
                    return Ok(Some(CompiledFactProofBody {
                        fact,
                        proposition,
                        proof_expression,
                    }));
                }
            }
        }
        self.with_verified_fact_well_definedness_context(verified, |compiler| {
            let Some(proof_expression) =
                compiler.construct_lean_proof_from_direct_fact_result(verified)?
            else {
                return Ok(None);
            };
            let fact = verified.fact();
            let proposition = render_fact(&fact, &compiler.environment_stack)?;
            Ok(Some(CompiledFactProofBody {
                fact,
                proposition,
                proof_expression,
            }))
        })
    }

    pub(in super::super) fn render_object_using_well_definedness_from_fact_result(
        &mut self,
        result: &VerifiedFactResult,
        object: &Obj,
    ) -> Result<String, String> {
        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(&result.checked)?;
        let previous_well_definedness =
            self.environment_stack.well_definedness.replace(certificate);
        let rendered = render_obj(object, &self.environment_stack);
        self.environment_stack.well_definedness = previous_well_definedness;
        rendered
    }

    pub(in super::super) fn render_fact_using_well_definedness_result(
        &mut self,
        result: &WellDefinedFactResult,
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
