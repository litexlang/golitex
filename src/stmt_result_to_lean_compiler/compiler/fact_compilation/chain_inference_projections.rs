//! Equality and numeric-order chain adjacent projections.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Validate one equality-chain closure Result against its exact source,
    /// then expose the adjacent edge FactIds as projections of the already
    /// published source proof. The returned allowlist roots later inference
    /// compilation in this Result rather than in ambient proposition lookup.
    pub(in super::super) fn install_equality_chain_adjacent_projections_for_typed_inference(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        source_lean_reference: &str,
        infers: &SuccessInferResult,
        result_layer: &str,
    ) -> Result<Vec<(FactId, Fact)>, String> {
        let equality_applications = infers
            .rule_applications
            .iter()
            .filter(|application| matches!(application.rule, InferRule::EqualityChainClosure(_)))
            .collect::<Vec<_>>();
        if equality_applications.is_empty() {
            return Ok(vec![(source_fact_id, source_fact.clone())]);
        }
        let Fact::ChainFact(chain) = source_fact else {
            return Err(format!(
                "{result_layer} retained equality-chain closure for a non-chain source"
            ));
        };
        if chain
            .prop_names
            .iter()
            .any(|predicate| predicate.to_string() != EQUAL)
        {
            return Err(format!(
                "{result_layer} retained equality closure for a mixed relation chain"
            ));
        }
        let adjacent_facts = chain
            .facts(&self.runtime)
            .map_err(|error| format!("{result_layer} retained an invalid chain: {error:?}"))?
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>();
        if adjacent_facts.len() < 2 {
            return Err(format!(
                "{result_layer} equality closure has fewer than two adjacent edges"
            ));
        }
        let expected_application_count = adjacent_facts
            .len()
            .saturating_sub(1)
            .saturating_mul(adjacent_facts.len())
            / 2;
        if equality_applications.len() != expected_application_count {
            return Err(format!(
                "{result_layer} expected {expected_application_count} equality closure applications, retained {}",
                equality_applications.len()
            ));
        }

        let mut adjacent_fact_ids = vec![None; adjacent_facts.len()];
        let mut application_index = 0;
        for start_object_index in 0..chain.objs.len() {
            for end_object_index in start_object_index + 2..chain.objs.len() {
                let application = equality_applications[application_index];
                let InferRule::EqualityChainClosure(rule) = &application.rule else {
                    unreachable!("filtered equality-chain application")
                };
                if rule.start_object_index != start_object_index
                    || rule.end_object_index != end_object_index
                {
                    return Err(format!(
                        "{result_layer} equality application {application_index} changed its object interval"
                    ));
                }
                let expected_premises = &adjacent_facts[start_object_index..end_object_index];
                if application.premises.len() != expected_premises.len() {
                    return Err(format!(
                        "{result_layer} equality application {application_index} changed its premise arity"
                    ));
                }
                for (offset, (premise, expected)) in application
                    .premises
                    .iter()
                    .zip(expected_premises.iter())
                    .enumerate()
                {
                    if premise.fact.to_string() != expected.to_string() {
                        return Err(format!(
                            "{result_layer} equality application {application_index} changed premise {offset}"
                        ));
                    }
                    let fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "{result_layer} equality application {application_index} premise {offset} has no FactId"
                        )
                    })?;
                    let adjacent_index = start_object_index + offset;
                    match adjacent_fact_ids[adjacent_index] {
                        Some(existing) if existing != fact_id => {
                            return Err(format!(
                                "{result_layer} assigned two FactIds to adjacent equality {adjacent_index}"
                            ));
                        }
                        _ => adjacent_fact_ids[adjacent_index] = Some(fact_id),
                    }
                }
                let [conclusion] = application.conclusions.as_slice() else {
                    return Err(format!(
                        "{result_layer} equality application {application_index} must retain one conclusion"
                    ));
                };
                let expected_conclusion: Fact = self
                    .runtime
                    .new_equal_fact(
                        chain.objs[start_object_index].clone(),
                        chain.objs[end_object_index].clone(),
                        chain.line_file.clone(),
                    )
                    .into();
                validate_success_store_fact_result(
                    conclusion,
                    &expected_conclusion,
                    &format!("{result_layer} equality application {application_index}"),
                )?;
                application_index += 1;
            }
        }

        let mut allowed_sources = vec![(source_fact_id, source_fact.clone())];
        for (adjacent_index, (fact, fact_id)) in adjacent_facts
            .into_iter()
            .zip(adjacent_fact_ids.into_iter())
            .enumerate()
        {
            let fact_id = fact_id.ok_or_else(|| {
                format!("{result_layer} lost adjacent equality {adjacent_index} FactId")
            })?;
            let projection = conjunction_projection(
                &format!("({source_lean_reference})"),
                adjacent_index,
                chain.prop_names.len(),
            )?;
            self.environment_stack
                .fact_names
                .insert(fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            allowed_sources.push((fact_id, fact));
        }
        Ok(allowed_sources)
    }

    /// Expose the exact adjacent premises used by retained mixed strict/weak
    /// numeric-order closure applications as projections of the source chain.
    pub(in super::super) fn install_numeric_order_chain_adjacent_projections_for_typed_inference(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        source_lean_reference: &str,
        infers: &SuccessInferResult,
        result_layer: &str,
    ) -> Result<Vec<(FactId, Fact)>, String> {
        let applications = infers
            .rule_applications
            .iter()
            .filter(|application| {
                matches!(application.rule, InferRule::NumericOrderChainClosure(_))
            })
            .collect::<Vec<_>>();
        if applications.is_empty() {
            return Ok(vec![(source_fact_id, source_fact.clone())]);
        }
        let Fact::ChainFact(chain) = source_fact else {
            return Err(format!(
                "{result_layer} retained numeric-order closure for a non-chain source"
            ));
        };
        let expected_steps = chain
            .numeric_order_chain_closure_steps_with_runtime(&self.runtime)
            .map_err(|error| {
                format!("{result_layer} retained an invalid order chain: {error:?}")
            })?;
        if applications.len() != expected_steps.len() {
            return Err(format!(
                "{result_layer} expected {} numeric-order closure applications, retained {}",
                expected_steps.len(),
                applications.len()
            ));
        }
        let adjacent_facts = chain
            .facts(&self.runtime)
            .map_err(|error| format!("{result_layer} retained an invalid chain: {error:?}"))?
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>();
        let mut adjacent_fact_ids = vec![None; adjacent_facts.len()];
        for (application_index, (application, expected)) in
            applications.iter().zip(expected_steps.iter()).enumerate()
        {
            let InferRule::NumericOrderChainClosure(rule) = &application.rule else {
                unreachable!("filtered numeric-order application")
            };
            if rule.start_object_index != expected.start_object_index
                || rule.end_object_index != expected.end_object_index
                || application.premises.len() != expected.premises.len()
                || application.conclusions.len() != 1
            {
                return Err(format!(
                    "{result_layer} numeric-order application {application_index} changed its interval or arity"
                ));
            }
            for (offset, (premise, expected_premise)) in application
                .premises
                .iter()
                .zip(expected.premises.iter())
                .enumerate()
            {
                if premise.fact.to_string() != expected_premise.to_string() {
                    return Err(format!(
                        "{result_layer} numeric-order application {application_index} changed premise {offset}"
                    ));
                }
                let fact_id = premise.fact_id.ok_or_else(|| {
                    format!(
                        "{result_layer} numeric-order application {application_index} premise {offset} has no FactId"
                    )
                })?;
                let adjacent_index = expected.start_object_index + offset;
                match adjacent_fact_ids[adjacent_index] {
                    Some(existing) if existing != fact_id => {
                        return Err(format!(
                            "{result_layer} assigned two FactIds to order edge {adjacent_index}"
                        ));
                    }
                    _ => adjacent_fact_ids[adjacent_index] = Some(fact_id),
                }
            }
            if application.conclusions[0].fact.to_string()
                != Fact::from(expected.conclusion.clone()).to_string()
            {
                return Err(format!(
                    "{result_layer} numeric-order application {application_index} changed its conclusion"
                ));
            }
        }

        let mut allowed_sources = vec![(source_fact_id, source_fact.clone())];
        for (adjacent_index, (fact, fact_id)) in adjacent_facts
            .into_iter()
            .zip(adjacent_fact_ids.into_iter())
            .enumerate()
        {
            let Some(fact_id) = fact_id else {
                continue;
            };
            let projection = conjunction_projection(
                &format!("({source_lean_reference})"),
                adjacent_index,
                chain.prop_names.len(),
            )?;
            self.environment_stack
                .fact_names
                .insert(fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            allowed_sources.push((fact_id, fact));
        }
        Ok(allowed_sources)
    }
}
