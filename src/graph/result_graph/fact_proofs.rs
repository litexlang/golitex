//! Fact proof, builtin, universal, shared, and storage nodes.

use super::*;

impl ResultGraph {
    pub(super) fn add_verify_fact_outcome(&mut self, result: &VerifyFactResult, id: String) {
        match result {
            VerifyFactResult::Verified(verified) => {
                self.ensure_node(
                    id.clone(),
                    "fact_verification",
                    "Verified",
                    verified.fact().to_string(),
                    None,
                );
                if !self.expanded_nodes.insert(id.clone()) {
                    return;
                }
                let wd_id = format!("{id}/well-definedness");
                self.add_fact_well_definedness(
                    &verified.checked,
                    wd_id.clone(),
                    verified.fact().to_string(),
                );
                self.add_edge(&id, &wd_id, "well_definedness", 0);
                let proof_id = format!("{id}/truth");
                self.add_verify_fact_result(
                    verified.verification.as_ref(),
                    proof_id.clone(),
                );
                self.add_edge(&id, &proof_id, "truth", 0);
            }
            VerifyFactResult::Unknown(unknown) => {
                self.ensure_node(
                    id.clone(),
                    "fact_verification",
                    "UnknownAfterWellDefinedness",
                    unknown.checked.fact.to_string(),
                    None,
                );
                if !self.expanded_nodes.insert(id.clone()) {
                    return;
                }
                let wd_id = format!("{id}/well-definedness");
                self.add_fact_well_definedness(
                    &unknown.checked,
                    wd_id.clone(),
                    unknown.checked.fact.to_string(),
                );
                self.add_edge(&id, &wd_id, "well_definedness", 0);
            }
        }
    }

    pub(super) fn add_verify_fact_result(&mut self, result: &SuccessFactProofNode, id: String) {
        self.ensure_node(
            id.clone(),
            "verification",
            verify_fact_role(result),
            result.fact().to_string(),
            None,
        );
        if !self.expanded_nodes.insert(id.clone()) {
            return;
        }
        let proof_id = format!("{id}/proof");
        self.add_fact_proof(result.proof(), proof_id.clone());
        self.add_edge(&id, &proof_id, "proof", 0);
    }

    pub(super) fn add_fact_proof(&mut self, proof: &SuccessFactProofResult, id: String) {
        match proof {
            SuccessFactProofResult::BuiltinRule(result) => {
                self.add_builtin_proof(result, id, "BuiltinRule");
            }
            SuccessFactProofResult::BuiltinStrategy(result) => {
                self.add_builtin_proof(result, id, "BuiltinStrategy");
            }
            SuccessFactProofResult::StoredFactCitation(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "StoredFactCitation",
                    result.source_fact.to_string(),
                    None,
                );
                self.add_cited_fact(
                    &id,
                    Some(result.source_fact_id),
                    result.source_fact.to_string(),
                    "citation",
                    0,
                );
            }
            SuccessFactProofResult::DefinitionReduction(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "DefinitionReduction",
                    result.definition.to_string(),
                    None,
                );
                for (index, child) in result
                    .verification
                    .argument_verification
                    .checks
                    .iter()
                    .enumerate()
                {
                    let child_id = format!("{id}/parameter:{index}");
                    self.add_verify_fact_outcome(child, child_id.clone());
                    self.add_edge(&id, &child_id, "parameter_check", index);
                }
                for (index, child) in result.verification.clause_checks.iter().enumerate() {
                    let child_id = format!("{id}/clause:{index}");
                    self.add_verify_fact_outcome(child, child_id.clone());
                    self.add_edge(&id, &child_id, "clause_check", index);
                }
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "CheckedFunctionDefinitionReduction",
                    result.verification.defining_equality.to_string(),
                    None,
                );
                self.add_cited_fact(
                    &id,
                    Some(result.verification.defining_equality_fact_id),
                    result.verification.defining_equality.to_string(),
                    "definition",
                    0,
                );
            }
            SuccessFactProofResult::DiagnosticOnly(result) => {
                self.ensure_node(id, "proof", "DiagnosticOnly", result.detail.clone(), None);
            }
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                self.add_known_forall_proof(result, id, "KnownForallInstantiation");
            }
            SuccessFactProofResult::CombinedProofs(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "CombinedProofs",
                    "combined proof",
                    None,
                );
                if let Some(primary) = result.primary.as_ref() {
                    let primary_id = format!("{id}/primary");
                    self.add_verify_fact_result(primary, primary_id.clone());
                    self.add_edge(&id, &primary_id, "primary", 0);
                }
                for (index, step) in result.steps.iter().enumerate() {
                    let step_id = format!("{id}/step:{index}");
                    self.add_verify_fact_outcome(step, step_id.clone());
                    self.add_edge(&id, &step_id, "step", index);
                }
            }
            SuccessFactProofResult::ForallProof(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "ForallProof",
                    result.forall_fact.to_string(),
                    None,
                );
                for (index, assumption) in result.parameter_assumptions.iter().enumerate() {
                    let fact_id =
                        self.ensure_fact_node(assumption.fact_id, assumption.fact.to_string());
                    self.add_edge(&id, &fact_id, "parameter_assumption", index);
                }
                for (index, assumption) in result.domain_assumptions.iter().enumerate() {
                    let fact_id =
                        self.ensure_fact_node(assumption.fact_id, assumption.fact.to_string());
                    self.add_edge(&id, &fact_id, "domain_assumption", index);
                }
                self.add_infers(&id, &result.assumption_infers, format!("{id}/assumption"));
                for (index, proved) in result.proves.iter().enumerate() {
                    let child_id = format!("{id}/prove:{index}");
                    self.add_verify_fact_outcome(&proved.result, child_id.clone());
                    self.add_edge(&id, &child_id, "proves", index);
                }
            }
            SuccessFactProofResult::Transform(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    transform_role(&result.rule),
                    "fact transformation",
                    None,
                );
                let source_id = format!("{id}/source");
                self.add_verify_fact_result(&result.source, source_id.clone());
                self.add_edge(&id, &source_id, "source", 0);
                if let FactTransformationRule::EqualityRewrite(transport) = &result.rule {
                    for (index, step) in transport.steps.iter().enumerate() {
                        self.add_cited_fact(
                            &id,
                            Some(step.equality_fact_id),
                            step.equality.to_string(),
                            "equality",
                            index,
                        );
                    }
                }
                if let FactTransformationRule::TransparentDefinitionReduction(evidence) =
                    &result.rule
                {
                    for (index, definition) in evidence.definitions.iter().enumerate() {
                        self.add_cited_fact(
                            &id,
                            Some(definition.defining_equality_fact_id),
                            definition.defining_equality.to_string(),
                            "defining_equality",
                            index,
                        );
                    }
                }
            }
            SuccessFactProofResult::Reuse(result) => {
                self.ensure_node(id.clone(), "proof", "Reuse", "shared proof", None);
                let source_id = self.add_shared_fact_result(&result.source);
                self.add_edge(&id, &source_id, "reuses", 0);
            }
        }
    }

    pub(super) fn add_builtin_proof(
        &mut self,
        result: &SuccessBuiltinFactProofResult,
        id: String,
        role: &str,
    ) {
        self.ensure_node(id.clone(), "proof", role, result.msg.clone(), None);
        for (index, subgoal) in result.subgoals.iter().enumerate() {
            let child_id = format!("{id}/subgoal:{index}");
            self.add_verify_fact_outcome(subgoal, child_id.clone());
            self.add_edge(&id, &child_id, "subgoal", index);
        }
    }

    pub(super) fn add_known_forall_proof(
        &mut self,
        result: &SuccessInstantiateKnownForallResult,
        id: String,
        role: &str,
    ) {
        self.ensure_node(
            id.clone(),
            "proof",
            role,
            format!(
                "{} @ {:?}",
                result.source_fact, result.source_conclusion_location
            ),
            None,
        );
        let citation_role = format!("citation:{:?}", result.source_conclusion_location);
        self.add_cited_fact(
            &id,
            Some(result.source_fact_id),
            result.source_fact.to_string(),
            &citation_role,
            0,
        );
        for (index, requirement) in result.requirements.iter().enumerate() {
            let child_id = format!("{id}/requirement:{index}");
            self.add_verify_fact_outcome(&requirement.result, child_id.clone());
            self.add_edge(&id, &child_id, "requirement", index);
        }
    }

    pub(super) fn add_shared_fact_result(
        &mut self,
        source: &Rc<SuccessFactProofNode>,
    ) -> String {
        let key = Rc::as_ptr(source) as usize;
        if let Some(id) = self.shared_fact_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("shared-fact:{}", self.shared_fact_nodes.len());
        self.shared_fact_nodes.insert(key, id.clone());
        self.ensure_node(
            id.clone(),
            "verification",
            "SharedFactProof",
            source.fact().to_string(),
            None,
        );
        self.add_verify_fact_result(source, id.clone());
        id
    }

    pub(super) fn add_store_fact_result(&mut self, result: &SuccessStoreFactResult, id: String) {
        self.ensure_node(
            id.clone(),
            "store",
            "SuccessStoreFactResult",
            result.fact.to_string(),
            result.fact_id,
        );
        if let Some(fact_id) = result.fact_id {
            let fact_node = self.ensure_fact_node(fact_id, result.fact.to_string());
            self.add_edge(&id, &fact_node, "stored_fact", 0);
        }
        self.add_infers(&id, &result.infers, format!("{id}/infer"));
    }
}
