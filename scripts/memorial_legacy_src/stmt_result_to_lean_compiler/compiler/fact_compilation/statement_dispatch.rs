//! Fact statement compilation dispatch.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<(), String> {
        if result.is_trusted() {
            return Err(format!(
                "trusted fact `{}` has no reviewed Lean trust adapter",
                result.fact()
            ));
        }
        if self
            .compile_object_reflexivity_fact_result(result)
            .map_err(|error| format!("object-reflexivity route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_rational_normalization_fact_result(result)
            .map_err(|error| format!("rational-normalization route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_rational_algebraic_normalization_fact_result(result)
            .map_err(|error| format!("rational-algebraic-normalization route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_complex_algebraic_normalization_fact_result(result)
            .map_err(|error| format!("complex-algebraic-normalization route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_exact_fact_citation_result(result)
            .map_err(|error| format!("exact-citation route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_closed_standard_numeric_membership_fact_result(result)
            .map_err(|error| format!("closed-standard-numeric-membership route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_standard_numeric_membership_with_inference(result)
            .map_err(|error| format!("standard-numeric-membership inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_set_builder_membership_with_inference(result)
            .map_err(|error| format!("set-builder inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_list_set_membership_with_inference(result)
            .map_err(|error| format!("list-set inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_registered_transitive_predicate_chain_with_inference(result)
            .map_err(|error| format!("registered transitive-chain inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_defined_predicate_fact_with_inference(result)
            .map_err(|error| format!("defined-predicate inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_conjunction_fact_with_component_inference(result)
            .map_err(|error| format!("conjunction-component inference route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_forall_fact_result(result)
            .map_err(|error| format!("forall route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_fact_with_typed_inference(result)
            .map_err(|error| format!("generic typed-inference fact route: {error}"))?
        {
            return Ok(());
        }
        if self
            .compile_direct_fact_without_inference(result)
            .map_err(|error| format!("direct fact route: {error}"))?
        {
            return Ok(());
        }
        Err(format!(
            "StmtResult-to-Lean compiler has no direct fact consumer for `{}` ({})",
            result.fact(),
            describe_success_fact_result_for_direct_compilation_audit(result),
        ))
    }
}
