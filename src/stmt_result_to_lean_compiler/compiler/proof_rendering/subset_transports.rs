//! Lexical subset evidence used by representation lowering.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Publish one already-compiled verifier child as a lexical subset
    /// transport. Non-subset facts intentionally have no effect.
    pub(in super::super) fn install_result_owned_subset_transport(
        &mut self,
        result: &SuccessFactStmtResult,
        proof_expression: &str,
    ) -> Result<(), String> {
        let fact = result.fact();
        if result.store.fact.to_string() != fact.to_string() {
            return Err("subset transport changed between verification and store".into());
        }
        install_subset_transport_from_fact(&fact, proof_expression, &mut self.environment_stack)
    }
}

pub(in super::super) fn install_subset_transport_from_fact(
    fact: &Fact,
    proof_expression: &str,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let Ok((source_set, target_set)) = subset_parts(fact) else {
        return Ok(());
    };
    context
        .subset_membership_transports
        .push(SubsetMembershipTransportBinding::new(
            source_set.clone(),
            target_set.clone(),
            proof_expression.to_string(),
        ));
    Ok(())
}

pub(in super::super) fn install_visible_subset_transports_for_parameter(
    symbol_id: SymbolId,
    parameter_name: &str,
    parameter_membership: &str,
    source_set: &Obj,
    context: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let transports = context.subset_membership_transports.clone();
    for transport in transports {
        if !matches_directly_or_after_one_transparent_definition_pass(
            &transport.source_set,
            source_set,
            context,
        )? {
            continue;
        }
        let lowered_target = LeanTargetObjectRepresentation::lower(&transport.target_set)?;
        let target_membership = format!(
            "(({}) {} ({}))",
            transport.proof_expression, parameter_name, parameter_membership
        );
        install_numeric_representations_from_membership(
            symbol_id,
            &lowered_target,
            parameter_name,
            &target_membership,
            context,
        );
    }
    Ok(())
}
