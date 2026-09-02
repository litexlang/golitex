//! Fact well-definedness traversal.

use super::*;

impl ResultGraph {
    pub(super) fn add_fact_well_definedness(
        &mut self,
        result: &WellDefinedFactResult,
        id: String,
        label: String,
    ) {
        self.ensure_node(
            id.clone(),
            "well_definedness",
            "WellDefinedFactResult",
            label,
            None,
        );
        if !self.expanded_nodes.insert(id.clone()) {
            return;
        }
        let proof_id = format!("{id}/proof");
        self.add_fact_well_definedness_proof(&result.proof, proof_id.clone());
        self.add_edge(&id, &proof_id, "proof", 0);
    }

    pub(super) fn add_fact_well_definedness_proof(
        &mut self,
        result: &SuccessVerifyFactWellDefinedProofResult,
        id: String,
    ) {
        match result {
            SuccessVerifyFactWellDefinedProofResult::AtomicFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "AtomicFact",
                    result.statement.to_string(),
                    None,
                );
                for (index, argument) in result.arguments.iter().enumerate() {
                    let child_id = self.add_shared_wd_obj(&argument.result);
                    self.add_edge(&id, &child_id, "argument", index);
                }
                let predicate_id = format!("{id}/predicate");
                self.ensure_node(
                    predicate_id.clone(),
                    "well_definedness",
                    "AtomicPredicate",
                    format!(
                        "{} / arity {}",
                        result.predicate.name, result.predicate.expected_arity
                    ),
                    None,
                );
                self.add_edge(&id, &predicate_id, "predicate", 0);
                for (index, check) in result.predicate.domain_checks.iter().enumerate() {
                    let child_id = format!("{predicate_id}/domain_check:{index}");
                    self.add_verify_fact_outcome(&check.result, child_id.clone());
                    self.add_edge(
                        &predicate_id,
                        &child_id,
                        atomic_predicate_domain_check_role(check.role),
                        index,
                    );
                }
            }
            SuccessVerifyFactWellDefinedProofResult::AndFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "AndFact",
                    result.statement.to_string(),
                    None,
                );
                self.add_fact_wd_children(&id, "conjunct", &result.conjuncts);
            }
            SuccessVerifyFactWellDefinedProofResult::ChainFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "ChainFact",
                    result.statement.to_string(),
                    None,
                );
                self.add_fact_wd_children(&id, "comparison", &result.comparisons);
            }
            SuccessVerifyFactWellDefinedProofResult::OrFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "OrFact",
                    result.statement.to_string(),
                    None,
                );
                self.add_fact_wd_children(&id, "branch", &result.branches);
            }
            SuccessVerifyFactWellDefinedProofResult::ExistFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "ExistFact",
                    result.statement.to_string(),
                    None,
                );
                self.add_fact_binder(&id, &result.binder);
                for (index, body) in result.body.iter().enumerate() {
                    self.add_local_fact_wd(&id, "body", index, body);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ForallFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "ForallFact",
                    result.statement.to_string(),
                    None,
                );
                self.add_fact_binder(&id, &result.binder);
                for (index, premise) in result.premises.iter().enumerate() {
                    self.add_local_fact_wd(&id, "premise", index, premise);
                }
                for (index, conclusion) in result.conclusions.iter().enumerate() {
                    self.add_local_fact_wd(&id, "conclusion", index, conclusion);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "ForallFactWithIff",
                    result.statement.to_string(),
                    None,
                );
                for (index, (kind, child)) in
                    [("forward", &*result.forward), ("reverse", &*result.reverse)]
                        .into_iter()
                        .enumerate()
                {
                    let child_id = format!("{id}/{kind}");
                    self.add_fact_well_definedness_proof(child, child_id.clone());
                    self.add_edge(&id, &child_id, kind, index);
                }
            }
            SuccessVerifyFactWellDefinedProofResult::NotForallFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "NotForallFact",
                    result.statement.to_string(),
                    None,
                );
                let child_id = format!("{id}/inner");
                self.add_fact_well_definedness_proof(&result.inner, child_id.clone());
                self.add_edge(&id, &child_id, "inner", 0);
            }
        }
    }

    pub(super) fn add_fact_wd_children(
        &mut self,
        parent: &str,
        role: &str,
        children: &[SuccessVerifyFactWellDefinedProofResult],
    ) {
        for (index, child) in children.iter().enumerate() {
            let child_id = format!("{parent}/{role}:{index}");
            self.add_fact_well_definedness_proof(child, child_id.clone());
            self.add_edge(parent, &child_id, role, index);
        }
    }

    pub(super) fn add_fact_binder(&mut self, parent: &str, binder: &SuccessVerifyFactBinderResult) {
        let binder_id = format!("{parent}/binder");
        self.ensure_node(
            binder_id.clone(),
            "well_definedness",
            "FactBinder",
            "fact binder",
            None,
        );
        self.add_edge(parent, &binder_id, "binder", 0);
        self.add_fact_parameter_groups(&binder_id, &binder.parameter_groups);
    }

    pub(super) fn add_fact_parameter_groups(
        &mut self,
        parent: &str,
        parameter_groups: &[SuccessVerifyFactParameterGroupResult],
    ) {
        for (index, group) in parameter_groups.iter().enumerate() {
            let group_id = format!("{parent}/group:{index}");
            self.ensure_node(
                group_id.clone(),
                "well_definedness",
                "FactParameterGroup",
                group.parameter_type.to_string(),
                None,
            );
            self.add_edge(parent, &group_id, "parameter_group", index);
            if let Some(carrier) = group.carrier.as_ref() {
                self.add_wd_child(&group_id, "carrier", 0, carrier);
            }
            for (parameter_index, parameter) in group.parameters.iter().enumerate() {
                self.add_wd_binder_premise(&group_id, "parameter", parameter_index, parameter);
            }
        }
    }

    pub(super) fn add_local_fact_wd(
        &mut self,
        parent: &str,
        role: &str,
        index: usize,
        result: &SuccessVerifyLocalFactWellDefinedResult,
    ) {
        let id = format!("{parent}/{role}:{index}");
        self.ensure_node(
            id.clone(),
            "well_definedness",
            "LocalFact",
            result.proposition.to_string(),
            None,
        );
        self.add_edge(parent, &id, role, index);
        let proof_id = format!("{id}/recursive");
        self.add_fact_well_definedness_proof(&result.well_definedness, proof_id.clone());
        self.add_edge(&id, &proof_id, "recursive", 0);
        let store_id = format!("{id}/store");
        self.add_store_fact_result(&result.store, store_id.clone());
        self.add_edge(&id, &store_id, "store", 0);
    }
}
