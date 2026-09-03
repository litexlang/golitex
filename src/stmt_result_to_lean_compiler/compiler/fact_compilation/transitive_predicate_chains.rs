//! Registered transitive predicate-chain inference.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: publish the proved source chain, expose each retained chain
    /// component FactId as a projection from that theorem in the current
    /// compiler environment, then fold the visible registered transitivity
    /// theorem over every typed inference application's ordered premises.
    pub(in super::super) fn compile_registered_transitive_predicate_chain_with_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        let has_registered_transitive_application = result
            .store
            .infers
            .rule_applications
            .iter()
            .any(|application| {
                matches!(
                    application.rule,
                    InferRule::RegisteredTransitivePredicateChainClosure(_)
                )
            });
        if !has_registered_transitive_application {
            return Ok(false);
        }
        let source_fact = result.fact();
        let Fact::ChainFact(chain) = &source_fact else {
            return Err(
                "registered transitive-chain inference retained a non-chain source fact".into(),
            );
        };
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err(
                "registered transitive chain changed between verification and store".into(),
            );
        }
        let adjacent_facts = chain
            .facts()
            .map_err(|error| format!("invalid registered transitive chain: {error:?}"))?
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>();
        if adjacent_facts.len() < 2 {
            return Err(
                "registered transitive inference retained a chain with fewer than two edges".into(),
            );
        }
        validate_chain_fact_well_definedness_result(&verified.checked, chain, &adjacent_facts)?;

        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "registered transitive chain store has no FactId".to_string())?;
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(verified)?
        else {
            return Ok(false);
        };
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        let expected_application_count = (1..adjacent_facts.len())
            .map(|distance| distance)
            .sum::<usize>();
        let mut closure_applications = Vec::with_capacity(expected_application_count);
        let mut component_applications = Vec::with_capacity(adjacent_facts.len());
        for application in &result.store.infers.rule_applications {
            match &application.rule {
                InferRule::RegisteredTransitivePredicateChainClosure(_) => {
                    closure_applications.push(application)
                }
                InferRule::ChainImpliesComponent(_) => component_applications.push(application),
                _ => {
                    return Err(
                        "registered transitive chain retained an unrelated inference application"
                            .into(),
                    );
                }
            }
        }
        if closure_applications.len() != expected_application_count {
            return Err(format!(
                "registered transitive chain expected {expected_application_count} closure applications, retained {}",
                closure_applications.len()
            ));
        }
        let mut adjacent_fact_ids = vec![None; adjacent_facts.len()];
        if component_applications.len() != adjacent_facts.len() {
            return Err(format!(
                "registered transitive chain expected {} component projections, retained {}",
                adjacent_facts.len(),
                component_applications.len()
            ));
        }
        for (component_index, (application, expected_fact)) in component_applications
            .iter()
            .zip(adjacent_facts.iter())
            .enumerate()
        {
            let InferRule::ChainImpliesComponent(rule) = &application.rule else {
                unreachable!("component applications were filtered by rule kind")
            };
            if rule.component_index != component_index
                || rule.component_count != adjacent_facts.len()
            {
                return Err(format!(
                    "registered transitive chain component projection {component_index} changed its position"
                ));
            }
            let [premise] = application.premises.as_slice() else {
                return Err(format!(
                    "registered transitive chain component projection {component_index} must retain one premise"
                ));
            };
            if premise.fact.to_string() != source_fact.to_string()
                || premise.fact_id != Some(source_fact_id)
            {
                return Err(format!(
                    "registered transitive chain component projection {component_index} changed its source"
                ));
            }
            let [conclusion] = application.conclusions.as_slice() else {
                return Err(format!(
                    "registered transitive chain component projection {component_index} must retain one conclusion"
                ));
            };
            validate_chain_component_inference_target(rule, &source_fact, &conclusion.fact)?;
            if conclusion.fact.to_string() != expected_fact.to_string() {
                return Err(format!(
                    "registered transitive chain component projection {component_index} changed its fact"
                ));
            }
            adjacent_fact_ids[component_index] = Some(conclusion.fact_id.ok_or_else(|| {
                format!(
                    "registered transitive chain component projection {component_index} has no FactId"
                )
            })?);
        }
        let mut expected_conclusions = Vec::with_capacity(expected_application_count);
        let mut expected_application_index = 0;
        for start_object_index in 0..chain.objs.len() {
            for end_object_index in start_object_index + 2..chain.objs.len() {
                let application = closure_applications[expected_application_index];
                expected_application_index += 1;
                let InferRule::RegisteredTransitivePredicateChainClosure(rule) = &application.rule
                else {
                    return Err(
                        "registered transitive chain mixed another typed inference rule into its closure"
                            .into(),
                    );
                };
                let predicate_name = chain.prop_names[0].to_string();
                if rule.predicate_name != predicate_name
                    || rule.start_object_index != start_object_index
                    || rule.end_object_index != end_object_index
                {
                    return Err(format!(
                        "registered transitive-chain application {} changed its predicate or object interval",
                        expected_application_index - 1
                    ));
                }
                let expected_premises = &adjacent_facts[start_object_index..end_object_index];
                if application.premises.len() != expected_premises.len() {
                    return Err(format!(
                        "registered transitive-chain application {} changed its premise arity",
                        expected_application_index - 1
                    ));
                }
                for (offset, (premise, expected_fact)) in application
                    .premises
                    .iter()
                    .zip(expected_premises.iter())
                    .enumerate()
                {
                    if premise.fact.to_string() != expected_fact.to_string() {
                        return Err(format!(
                            "registered transitive-chain application {} changed premise {offset}",
                            expected_application_index - 1
                        ));
                    }
                    let fact_id = premise.fact_id.ok_or_else(|| {
                        format!(
                            "registered transitive-chain application {} premise {offset} has no FactId",
                            expected_application_index - 1
                        )
                    })?;
                    let adjacent_index = start_object_index + offset;
                    match adjacent_fact_ids[adjacent_index] {
                        Some(existing) if existing == fact_id => {}
                        Some(_) => {
                            return Err(format!(
                                "registered transitive chain closure changed component FactId {adjacent_index}"
                            ));
                        }
                        None => unreachable!("all component applications were validated"),
                    }
                }
                let [conclusion] = application.conclusions.as_slice() else {
                    return Err(format!(
                        "registered transitive-chain application {} must retain one conclusion",
                        expected_application_index - 1
                    ));
                };
                let expected_conclusion: Fact = NormalAtomicFact::new(
                    chain.prop_names[0].clone(),
                    vec![
                        chain.objs[start_object_index].clone(),
                        chain.objs[end_object_index].clone(),
                    ],
                    chain.line_file.clone(),
                )
                .into();
                if conclusion.fact.to_string() != expected_conclusion.to_string() {
                    return Err(format!(
                        "registered transitive-chain application {} changed its conclusion",
                        expected_application_index - 1
                    ));
                }
                let conclusion_fact_id = validate_success_store_fact_result(
                    conclusion,
                    &expected_conclusion,
                    &format!(
                        "registered transitive-chain application {} conclusion",
                        expected_application_index - 1
                    ),
                )?;
                expected_conclusions.push((expected_conclusion, conclusion_fact_id));
            }
        }
        for (index, (fact, fact_id)) in adjacent_facts
            .iter()
            .zip(adjacent_fact_ids.into_iter())
            .enumerate()
        {
            let fact_id = fact_id.ok_or_else(|| {
                format!("registered transitive chain lost adjacent edge {index} FactId")
            })?;
            let projection = conjunction_projection(
                &format!("({source_theorem_name})"),
                index,
                adjacent_facts.len(),
            )?;
            self.environment_stack
                .fact_names
                .insert(fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
        }

        let mut seen_flattened_conclusions = HashSet::new();
        let unique_expected_conclusions = expected_conclusions
            .iter()
            .filter(|(fact, _)| seen_flattened_conclusions.insert(fact.to_string()))
            .collect::<Vec<_>>();
        let [source_store_output] = result.store.infers.store_fact_outputs.as_slice() else {
            return Err(
                "registered transitive chain must retain one flattened source store output".into(),
            );
        };
        if source_store_output.fact_id != Some(source_fact_id)
            || source_store_output
                .itself_and_why_itself_is_stored
                .0
                .to_string()
                != source_fact.to_string()
            || source_store_output.inferred_facts.len() != unique_expected_conclusions.len()
            || source_store_output.inferred_fact_ids.len() != unique_expected_conclusions.len()
        {
            return Err(
                "registered transitive chain source store disagrees with its typed closure".into(),
            );
        }
        for (index, ((stored_fact, stored_fact_id), (expected_fact, expected_fact_id))) in
            source_store_output
                .inferred_facts
                .iter()
                .zip(source_store_output.inferred_fact_ids.iter())
                .zip(unique_expected_conclusions.iter())
                .enumerate()
        {
            if stored_fact.to_string() != expected_fact.to_string()
                || *stored_fact_id != Some(*expected_fact_id)
            {
                return Err(format!(
                    "registered transitive chain flattened closure output {index} changed its fact or FactId"
                ));
            }
        }
        for (application, (expected_fact, expected_fact_id)) in closure_applications
            .into_iter()
            .zip(expected_conclusions.iter())
        {
            self.compile_registered_transitive_predicate_chain_inference_application(
                application,
                expected_fact,
                *expected_fact_id,
            )?;
        }
        Ok(true)
    }

    pub(in super::super) fn compile_registered_transitive_predicate_chain_inference_application(
        &mut self,
        application: &SuccessInferRuleApplicationResult,
        expected_conclusion: &Fact,
        expected_conclusion_fact_id: FactId,
    ) -> Result<(), String> {
        let InferRule::RegisteredTransitivePredicateChainClosure(rule) = &application.rule else {
            return Err("registered transitive compiler received another inference rule".into());
        };
        let binding = self
            .environment_stack
            .registered_transitive_predicate_theorem_bindings
            .get(&rule.predicate_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "registered transitivity theorem for `{}` is not visible in this compiler environment",
                    rule.predicate_name
                )
            })?;
        let Some(first_premise) = application.premises.first() else {
            return Err("registered transitive application retained no premises".into());
        };
        let first_fact_id = first_premise.fact_id.ok_or_else(|| {
            "registered transitive application first premise has no FactId".to_string()
        })?;
        let mut current_fact = first_premise.fact.clone();
        let mut current_proof =
            resolve_fact_citation(&first_fact_id, &current_fact, &self.environment_stack)?;
        for (index, next_premise) in application.premises.iter().enumerate().skip(1) {
            let next_fact_id = next_premise.fact_id.ok_or_else(|| {
                format!("registered transitive application premise {index} has no FactId")
            })?;
            let next_proof =
                resolve_fact_citation(&next_fact_id, &next_premise.fact, &self.environment_stack)?;
            let (next_conclusion, parameter_arguments) =
                instantiate_registered_transitive_predicate_application(
                    &binding.forall_fact,
                    &rule.predicate_name,
                    &current_fact,
                    &next_premise.fact,
                )?;
            let mut theorem_application = binding.theorem_name.clone();
            for argument in parameter_arguments {
                theorem_application.push(' ');
                theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
            }
            theorem_application.push_str(&format!(" ({current_proof}) ({next_proof})"));
            current_fact = next_conclusion;
            current_proof = theorem_application;
        }
        if current_fact.to_string() != expected_conclusion.to_string() {
            return Err(
                "registered transitive theorem fold changed its retained conclusion".into(),
            );
        }
        let proposition = render_fact(expected_conclusion, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {current_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(expected_conclusion_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(expected_conclusion_fact_id, expected_conclusion.clone());
        self.next_fact_name_index += 1;
        Ok(())
    }
}
