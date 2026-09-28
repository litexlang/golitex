//! Compiled and generated fact publication effects.

use super::super::*;

pub(in super::super) fn validate_compiled_fact_proof_effects(
    infer_result: &SuccessInferResult,
    proofs: &[CompiledFactProofBody],
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
    result_layer: &str,
) -> Result<Vec<Option<FactId>>, String> {
    if !infer_result.rule_applications.is_empty() {
        return Err(format!(
            "{result_layer} unexpectedly retained typed inference rules"
        ));
    }
    for output in &infer_result.store_fact_outputs {
        if !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty() {
            return Err(format!(
                "{result_layer} retained inferred children beside its direct outputs"
            ));
        }
    }

    let mut output_index = 0;
    let mut fact_ids = Vec::with_capacity(proofs.len());
    for proof in proofs {
        let next_output = infer_result.store_fact_outputs.get(output_index);
        if next_output.is_some_and(|output| {
            output.itself_and_why_itself_is_stored.0.to_string() == proof.fact.to_string()
        }) {
            let output = next_output.expect("checked as present");
            fact_ids.push(Some(output.fact_id.ok_or_else(|| {
                format!("{result_layer} store {output_index} has no FactId")
            })?));
            output_index += 1;
            continue;
        }

        let fact_was_already_visible = environment_stack
            .fact_propositions
            .values()
            .any(|visible| visible.to_string() == proof.fact.to_string());
        if !fact_was_already_visible {
            return Err(format!(
                "{result_layer} neither stored `{}` nor reused it from the current compiler environment",
                proof.fact
            ));
        }
        fact_ids.push(None);
    }
    if output_index != infer_result.store_fact_outputs.len() {
        return Err(format!(
            "{result_layer} retained a store output that does not match its ordered facts"
        ));
    }
    Ok(fact_ids)
}

pub(in super::super) fn validate_generated_fact_publication_effects(
    infers: &SuccessInferResult,
    expected: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if !infers.rule_applications.is_empty() || infers.store_fact_outputs.is_empty() {
        return Err(format!(
            "{result_layer} must retain only its generated-fact stores"
        ));
    }
    let mut exact_fact_id = None;
    for (store_index, store) in infers.store_fact_outputs.iter().enumerate() {
        if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string()
            || !store.inferred_facts.is_empty()
            || !store.inferred_fact_ids.is_empty()
        {
            return Err(format!(
                "{result_layer} store {store_index} changed its generated fact or retained inferred children"
            ));
        }
        let fact_id = store
            .fact_id
            .ok_or_else(|| format!("{result_layer} store {store_index} has no FactId"))?;
        if exact_fact_id.is_some_and(|retained| retained != fact_id) {
            return Err(format!(
                "{result_layer} assigned multiple FactIds to one generated fact"
            ));
        }
        exact_fact_id = Some(fact_id);
    }
    exact_fact_id.ok_or_else(|| format!("{result_layer} retained no FactId"))
}

pub(in super::super) fn validate_defined_predicate_fact_publication_effects(
    infers: &SuccessInferResult,
    expected: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    let [store] = infers.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} must retain exactly one predicate-fact store"
        ));
    };
    if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string()
        || store.inferred_facts.len() != store.inferred_fact_ids.len()
        || infers
            .rule_applications
            .iter()
            .any(|application| !defined_predicate_infer_rule(&application.rule))
    {
        return Err(format!(
            "{result_layer} changed its predicate fact or typed projection effects"
        ));
    }
    store
        .fact_id
        .ok_or_else(|| format!("{result_layer} predicate-fact store has no FactId"))
}
