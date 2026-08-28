//! Inference citations, node identity, and graph edges.

use super::*;

impl ResultGraph {
    pub(super) fn add_infers(&mut self, parent: &str, result: &SuccessInferResult, prefix: String) {
        for (index, output) in result.store_fact_outputs.iter().enumerate() {
            let output_id = format!("{prefix}/store-effect:{index}");
            let (fact, reason) = &output.itself_and_why_itself_is_stored;
            self.ensure_node(
                output_id.clone(),
                "store_effect",
                "SuccessStoreFactOutput",
                reason.clone(),
                output.fact_id,
            );
            self.add_edge(parent, &output_id, "effect", index);

            let source_fact_node = self.ensure_fact_node_or_local(
                output.fact_id,
                fact.to_string(),
                format!("{output_id}/fact"),
            );
            self.add_edge(&output_id, &source_fact_node, "stored_fact", 0);

            for (inferred_index, inferred_fact) in output.inferred_facts.iter().enumerate() {
                let inferred_id = output
                    .inferred_fact_ids
                    .get(inferred_index)
                    .copied()
                    .flatten();
                let inferred_node = self.ensure_fact_node_or_local(
                    inferred_id,
                    inferred_fact.to_string(),
                    format!("{output_id}/inferred:{inferred_index}"),
                );
                self.add_edge(&output_id, &inferred_node, "inferred_fact", inferred_index);
            }
        }

        for (index, application) in result.rule_applications.iter().enumerate() {
            let application_id = format!("{prefix}/rule:{index}");
            self.ensure_node(
                application_id.clone(),
                "inference",
                infer_rule_role(&application.rule),
                "inference rule",
                None,
            );
            self.add_edge(parent, &application_id, "inference", index);

            for (premise_index, premise) in application.premises.iter().enumerate() {
                let premise_node = self.ensure_fact_node_or_local(
                    premise.fact_id,
                    premise.fact.to_string(),
                    format!("{application_id}/premise:{premise_index}"),
                );
                self.add_edge(&premise_node, &application_id, "premise", premise_index);
            }

            for (conclusion_index, conclusion) in application.conclusions.iter().enumerate() {
                let conclusion_id = format!("{application_id}/conclusion:{conclusion_index}");
                self.add_store_fact_result(conclusion, conclusion_id.clone());
                self.add_edge(
                    &application_id,
                    &conclusion_id,
                    "conclusion",
                    conclusion_index,
                );
            }
        }
    }

    pub(super) fn add_cited_fact(
        &mut self,
        proof: &str,
        fact_id: Option<FactId>,
        label: String,
        edge_kind: &str,
        order: usize,
    ) {
        let fact_node =
            self.ensure_fact_node_or_local(fact_id, label, format!("{proof}/{edge_kind}:{order}"));
        self.add_edge(&fact_node, proof, edge_kind, order);
    }

    pub(super) fn ensure_fact_node_or_local(
        &mut self,
        fact_id: Option<FactId>,
        label: String,
        local_id: String,
    ) -> String {
        match fact_id {
            Some(fact_id) => self.ensure_fact_node(fact_id, label),
            None => {
                self.ensure_node(local_id.clone(), "fact", "TransientFact", label, None);
                local_id
            }
        }
    }

    pub(super) fn ensure_fact_node(&mut self, fact_id: FactId, label: String) -> String {
        let id = format!("fact:{fact_id}");
        self.ensure_node(id.clone(), "fact", "StoredFact", label, Some(fact_id));
        id
    }

    pub(super) fn ensure_node(
        &mut self,
        id: String,
        kind: &str,
        role: &str,
        label: impl Into<String>,
        fact_id: Option<FactId>,
    ) {
        let label = label.into();
        if let Some(index) = self.node_index.get(&id).copied() {
            let node = &mut self.nodes[index];
            if node.label.is_empty() && !label.is_empty() {
                node.label = label;
            }
            if node.fact_id.is_none() {
                node.fact_id = fact_id;
            }
            return;
        }
        self.node_index.insert(id.clone(), self.nodes.len());
        self.nodes.push(ResultGraphNode {
            id,
            kind: kind.to_string(),
            role: role.to_string(),
            label,
            fact_id,
        });
    }

    pub(super) fn add_edge(&mut self, from: &str, to: &str, kind: &str, order: usize) {
        self.edges.push(ResultGraphEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind: kind.to_string(),
            order,
        });
    }
}
