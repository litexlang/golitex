use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Clone, Debug)]
struct ResultGraphNode {
    id: String,
    kind: String,
    role: String,
    label: String,
    fact_id: Option<FactId>,
}

#[derive(Clone, Debug)]
struct ResultGraphEdge {
    from: String,
    to: String,
    kind: String,
    order: usize,
}

/// A pure projection of the recursive statement result tree.
///
/// This graph never looks facts or proof routes up in `Runtime`. Statement
/// nesting comes from result fields, and cross-statement proof dependencies
/// use `FactId` or the exact shared memo node.
pub(crate) struct ResultGraph {
    nodes: Vec<ResultGraphNode>,
    node_index: HashMap<String, usize>,
    edges: Vec<ResultGraphEdge>,
    shared_fact_nodes: HashMap<usize, String>,
    shared_wd_obj_nodes: HashMap<usize, String>,
    expanded_nodes: HashSet<String>,
}

impl ResultGraph {
    pub(crate) fn from_stmt_results(stmt_results: &[StmtResult]) -> Self {
        let mut graph = Self {
            nodes: Vec::new(),
            node_index: HashMap::new(),
            edges: Vec::new(),
            shared_fact_nodes: HashMap::new(),
            shared_wd_obj_nodes: HashMap::new(),
            expanded_nodes: HashSet::new(),
        };

        for (index, result) in stmt_results.iter().enumerate() {
            graph.add_stmt_result(result, format!("stmt:{index}"));
        }
        graph
    }

    fn add_stmt_result(&mut self, result: &StmtResult, id: String) {
        match result {
            StmtResult::Success(success) => self.add_success_stmt(success, id),
            StmtResult::Unknown(UnknownStmtResult::Fact(unknown)) => {
                self.ensure_node(id, "unknown", "Fact", unknown.goal().to_string(), None);
            }
            StmtResult::Unknown(UnknownStmtResult::Generic(_)) => {
                self.ensure_node(id, "unknown", "Generic", "unknown statement", None);
            }
        }
    }

    fn add_success_stmt(&mut self, success: &SuccessStmtResult, id: String) {
        let statement = success.statement();
        let role = success_stmt_role(success);
        self.ensure_node(id.clone(), "statement", role, statement.to_string(), None);
        if !self.expanded_nodes.insert(id.clone()) {
            return;
        }

        if let Some(fact) = success.fact() {
            self.add_fact_stmt_result(fact, id);
            return;
        }

        if let Some(common) = success.common() {
            let execution_id = format!("{id}/execution");
            self.ensure_node(
                execution_id.clone(),
                "execution",
                "SuccessStmtCommonResult",
                "statement execution",
                None,
            );
            self.add_edge(&id, &execution_id, "execution", 0);
            self.add_infers(
                &execution_id,
                &common.infers,
                format!("{execution_id}/infer"),
            );
            self.add_non_fact_well_definedness(success, &execution_id);
            let mut index = 0;
            success.visit_child_results(&mut |child| {
                let child_id = format!("{execution_id}/child:{index}");
                self.add_stmt_result(child, child_id.clone());
                self.add_edge(&execution_id, &child_id, "child", index);
                index += 1;
            });
        }
    }

    fn add_fact_stmt_result(&mut self, result: &SuccessFactStmtResult, statement_id: String) {
        let well_definedness_id = format!("{statement_id}/well-definedness");
        self.add_fact_well_definedness(
            &result.well_definedness,
            well_definedness_id.clone(),
            result.fact().to_string(),
        );
        self.add_edge(&statement_id, &well_definedness_id, "well_definedness", 0);
        let verification_id = format!("{statement_id}/verification");
        self.add_verify_fact_result(&result.verification, verification_id.clone());
        self.add_edge(&statement_id, &verification_id, "verification", 0);

        let store_id = format!("{statement_id}/store");
        self.add_store_fact_result(&result.store, store_id.clone());
        self.add_edge(&statement_id, &store_id, "store", 0);
    }

    fn add_non_fact_well_definedness(&mut self, success: &SuccessStmtResult, parent: &str) {
        match success {
            SuccessStmtResult::DefThmStmt(result) => {
                if let Some(verification) = result.verification.as_ref() {
                    self.add_attached_fact_well_definedness(
                        parent,
                        &verification.well_definedness,
                        verification.forall_fact.to_string(),
                        "well_definedness",
                        0,
                    );
                }
            }
            SuccessStmtResult::AxiomStmt(result) => {
                if let Some(well_definedness) = result.well_definedness.as_ref() {
                    self.add_attached_fact_well_definedness(
                        parent,
                        well_definedness,
                        result.statement.to_string(),
                        "well_definedness",
                        0,
                    );
                }
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(result)) => {
                if let Some(verification) = result.verification.as_ref() {
                    self.add_claim_well_definedness(parent, verification);
                }
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ExampleStmt(result)) => {
                if let Some(verification) = result.verification.as_ref() {
                    self.add_claim_well_definedness(parent, verification);
                }
            }
            SuccessStmtResult::By(SuccessByStmtResult::ByCasesStmt(result)) => {
                if let Some(verification) = result.verification.as_ref() {
                    for (index, well_definedness) in
                        verification.goal_well_definedness.iter().enumerate()
                    {
                        self.add_attached_fact_well_definedness(
                            parent,
                            well_definedness,
                            format!("case goal {}", index + 1),
                            "goal_well_definedness",
                            index,
                        );
                    }
                }
            }
            _ => {}
        }
    }

    fn add_claim_well_definedness(
        &mut self,
        parent: &str,
        verification: &SuccessVerifyClaimResult,
    ) {
        match verification {
            SuccessVerifyClaimResult::Forall(result) => self.add_attached_fact_well_definedness(
                parent,
                &result.well_definedness,
                result.forall_fact.to_string(),
                "well_definedness",
                0,
            ),
            SuccessVerifyClaimResult::Fact(result) => self.add_attached_fact_well_definedness(
                parent,
                &result.well_definedness,
                result.fact.to_string(),
                "well_definedness",
                0,
            ),
        }
    }

    fn add_attached_fact_well_definedness(
        &mut self,
        parent: &str,
        result: &SuccessVerifyFactWellDefinedResult,
        label: String,
        edge_kind: &str,
        order: usize,
    ) {
        let id = format!("{parent}/{edge_kind}:{order}");
        self.add_fact_well_definedness(result, id.clone(), label);
        self.add_edge(parent, &id, edge_kind, order);
    }

    fn add_fact_well_definedness(
        &mut self,
        result: &SuccessVerifyFactWellDefinedResult,
        id: String,
        label: String,
    ) {
        self.ensure_node(
            id.clone(),
            "well_definedness",
            "SuccessVerifyFactWellDefinedResult",
            label,
            None,
        );
        if !self.expanded_nodes.insert(id.clone()) {
            return;
        }
        if let Some(recursive) = result.recursive.as_ref() {
            let proof_id = format!("{id}/recursive");
            self.add_fact_well_definedness_proof(recursive, proof_id.clone());
            self.add_edge(&id, &proof_id, "recursive", 0);
        }
    }

    fn add_fact_well_definedness_proof(
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
                    self.add_stmt_result(&check.result, child_id.clone());
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

    fn add_fact_wd_children(
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

    fn add_fact_binder(&mut self, parent: &str, binder: &SuccessVerifyFactBinderResult) {
        let binder_id = format!("{parent}/binder");
        self.ensure_node(
            binder_id.clone(),
            "well_definedness",
            "FactBinder",
            "fact binder",
            None,
        );
        self.add_edge(parent, &binder_id, "binder", 0);
        for (index, group) in binder.parameter_groups.iter().enumerate() {
            let group_id = format!("{binder_id}/group:{index}");
            self.ensure_node(
                group_id.clone(),
                "well_definedness",
                "FactParameterGroup",
                group.parameter_type.to_string(),
                None,
            );
            self.add_edge(&binder_id, &group_id, "parameter_group", index);
            if let Some(carrier) = group.carrier.as_ref() {
                self.add_wd_child(&group_id, "carrier", 0, carrier);
            }
            for (parameter_index, parameter) in group.parameters.iter().enumerate() {
                self.add_wd_binder_premise(&group_id, "parameter", parameter_index, parameter);
            }
        }
    }

    fn add_local_fact_wd(
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

    fn add_shared_wd_obj(&mut self, result: &Rc<SuccessVerifyObjWellDefinedResult>) -> String {
        let key = Rc::as_ptr(result) as usize;
        if let Some(id) = self.shared_wd_obj_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("shared-wd-object:{}", self.shared_wd_obj_nodes.len());
        self.shared_wd_obj_nodes.insert(key, id.clone());
        self.add_wd_obj(result, id.clone());
        id
    }

    fn add_wd_obj(&mut self, result: &SuccessVerifyObjWellDefinedResult, id: String) {
        match result {
            SuccessVerifyObjWellDefinedResult::Direct(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "DirectObject",
                    result.object.to_string(),
                    None,
                );
                if !self.expanded_nodes.insert(id.clone()) {
                    return;
                }
                self.add_wd_obj_steps(&id, &result.steps);
            }
            SuccessVerifyObjWellDefinedResult::Reuse(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "ReuseObject",
                    result.object.to_string(),
                    None,
                );
                let source_id = self.add_shared_wd_obj(&result.source);
                self.add_edge(&id, &source_id, "reuses", 0);
            }
            SuccessVerifyObjWellDefinedResult::RecursiveReference(result) => {
                self.ensure_node(
                    id,
                    "well_definedness",
                    "RecursiveObjectReference",
                    result.object.to_string(),
                    None,
                );
            }
        }
    }

    fn add_wd_obj_steps(&mut self, parent: &str, steps: &SuccessVerifyObjWellDefinedStepsResult) {
        for (index, child) in steps.children.iter().enumerate() {
            self.add_wd_child(parent, "child", index, child);
        }
        for (index, check) in steps.fact_checks.iter().enumerate() {
            self.add_wd_fact_check(parent, "fact_check", index, check);
        }
        for (index, requirement) in steps.target_requirements.iter().enumerate() {
            let id = format!("{parent}/target_requirement:{index}");
            self.ensure_node(
                id.clone(),
                "well_definedness",
                "ObjectTargetRequirement",
                requirement.expected_proposition.to_string(),
                None,
            );
            self.add_edge(parent, &id, "target_requirement", index);
            let verification_id = format!("{id}/verification");
            self.add_verify_fact_result(&requirement.verification, verification_id.clone());
            self.add_edge(&id, &verification_id, "verification", 0);
        }
        for (index, store) in steps.stores.iter().enumerate() {
            let id = format!("{parent}/store:{index}");
            self.add_store_fact_result(store, id.clone());
            self.add_edge(parent, &id, "store", index);
        }
        if let Some(binder) = steps.binder.as_ref() {
            self.add_wd_object_binder(parent, binder);
        }
        if let Some(materialization) = steps.template_materialization.as_ref() {
            self.add_wd_template_materialization(parent, materialization);
        }
    }

    fn add_wd_child(
        &mut self,
        parent: &str,
        role: &str,
        order: usize,
        child: &SuccessVerifyChildObjWellDefinedResult,
    ) {
        let child_id = self.add_shared_wd_obj(&child.result);
        self.add_edge(parent, &child_id, role, order);
    }

    fn add_wd_fact_check(
        &mut self,
        parent: &str,
        role: &str,
        order: usize,
        check: &SuccessVerifyFactForObjWellDefinedResult,
    ) {
        let id = format!("{parent}/{role}:{order}");
        self.ensure_node(
            id.clone(),
            "well_definedness",
            "FactRequirement",
            check.expected_proposition.to_string(),
            None,
        );
        self.add_edge(parent, &id, role, order);
        let verification_id = format!("{id}/verification");
        self.add_verify_fact_result(&check.verification, verification_id.clone());
        self.add_edge(&id, &verification_id, "verification", 0);
    }

    fn add_wd_binder_premise(
        &mut self,
        parent: &str,
        role: &str,
        order: usize,
        premise: &SuccessVerifyBinderPremiseResult,
    ) {
        let id = format!("{parent}/{role}:{order}");
        self.ensure_node(
            id.clone(),
            "well_definedness",
            "BinderPremise",
            premise.proposition.to_string(),
            None,
        );
        self.add_edge(parent, &id, role, order);
        let wd_id = format!("{id}/well-definedness");
        self.add_fact_well_definedness(
            &premise.well_definedness,
            wd_id.clone(),
            premise.proposition.to_string(),
        );
        self.add_edge(&id, &wd_id, "well_definedness", 0);
        self.add_infers(&id, &premise.infers, format!("{id}/infer"));
    }

    fn add_wd_object_binder(
        &mut self,
        parent: &str,
        binder: &SuccessVerifyBinderObjectWellDefinedResult,
    ) {
        let id = format!("{parent}/binder");
        let role = match binder {
            SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(_) => "SetBuilder",
            SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(_) => "FunctionSet",
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(_) => "AnonymousFunction",
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(_) => "Iteration",
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(_) => "FiniteAggregate",
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(_) => "Reduce",
            SuccessVerifyBinderObjectWellDefinedResult::Structure(_) => "Structure",
        };
        self.ensure_node(id.clone(), "well_definedness", role, "object binder", None);
        self.add_edge(parent, &id, "binder", 0);
        match binder {
            SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result) => {
                self.add_wd_child(&id, "parameter_carrier", 0, &result.parameter_carrier);
                self.add_wd_binder_premise(&id, "parameter", 0, &result.parameter);
                for (index, condition) in result.conditions.iter().enumerate() {
                    let condition_id = format!("{id}/condition:{index}");
                    self.ensure_node(
                        condition_id.clone(),
                        "well_definedness",
                        "SetBuilderCondition",
                        condition.store.fact.to_string(),
                        None,
                    );
                    self.add_edge(&id, &condition_id, "condition", index);
                    let wd_id = format!("{condition_id}/well-definedness");
                    self.add_fact_well_definedness(
                        &condition.well_definedness,
                        wd_id.clone(),
                        condition.store.fact.to_string(),
                    );
                    self.add_edge(&condition_id, &wd_id, "well_definedness", 0);
                    let store_id = format!("{condition_id}/store");
                    self.add_store_fact_result(&condition.store, store_id.clone());
                    self.add_edge(&condition_id, &store_id, "store", 0);
                }
            }
            SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result) => {
                self.add_wd_signature_parts(
                    &id,
                    &result.parameter_carriers,
                    &result.parameters,
                    &result.domains,
                    &result.return_carrier,
                );
            }
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result) => {
                self.add_wd_signature_parts(
                    &id,
                    &result.parameter_carriers,
                    &result.parameters,
                    &result.domains,
                    &result.return_carrier,
                );
                self.add_wd_child(&id, "body", 0, &result.body);
                self.add_wd_target_requirement(&id, "body_membership", 0, &result.body_membership);
            }
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(result) => {
                self.add_wd_iteration(&id, result);
            }
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(result) => {
                self.add_wd_finite_aggregate(&id, result);
            }
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(result) => {
                self.add_wd_reduce(&id, result);
            }
            SuccessVerifyBinderObjectWellDefinedResult::Structure(result) => {
                self.add_wd_structure(&id, result);
            }
        }
    }

    fn add_wd_signature_parts(
        &mut self,
        parent: &str,
        parameter_carriers: &[SuccessVerifyChildObjWellDefinedResult],
        parameters: &[SuccessVerifyBinderPremiseResult],
        domains: &[SuccessVerifyBinderPremiseResult],
        return_carrier: &SuccessVerifyChildObjWellDefinedResult,
    ) {
        for (index, child) in parameter_carriers.iter().enumerate() {
            self.add_wd_child(parent, "parameter_carrier", index, child);
        }
        for (index, premise) in parameters.iter().enumerate() {
            self.add_wd_binder_premise(parent, "parameter", index, premise);
        }
        for (index, premise) in domains.iter().enumerate() {
            self.add_wd_binder_premise(parent, "domain", index, premise);
        }
        self.add_wd_child(parent, "return_carrier", 0, return_carrier);
    }

    fn add_wd_target_requirement(
        &mut self,
        parent: &str,
        role: &str,
        order: usize,
        requirement: &SuccessVerifyObjTargetRequirementResult,
    ) {
        let id = format!("{parent}/{role}:{order}");
        self.ensure_node(
            id.clone(),
            "well_definedness",
            "ObjectTargetRequirement",
            requirement.expected_proposition.to_string(),
            None,
        );
        self.add_edge(parent, &id, role, order);
        let verification_id = format!("{id}/verification");
        self.add_verify_fact_result(&requirement.verification, verification_id.clone());
        self.add_edge(&id, &verification_id, "verification", 0);
    }

    fn add_wd_iteration(&mut self, parent: &str, result: &SuccessVerifyIterationWellDefinedResult) {
        if let Some(scalar_return) = result.scalar_return.as_ref() {
            let id = format!("{parent}/scalar_return");
            self.ensure_node(
                id.clone(),
                "well_definedness",
                "IterationScalarReturn",
                result.operation.clone(),
                None,
            );
            self.add_edge(parent, &id, "scalar_return", 0);
            self.add_wd_signature_parts(
                &id,
                &scalar_return.parameter_carriers,
                &scalar_return.parameters,
                &scalar_return.domains,
                &scalar_return.return_carrier,
            );
            self.add_wd_fact_check(&id, "return_subset", 0, &scalar_return.return_subset);
        }
        self.add_wd_iteration_interval(parent, &result.interval);
    }

    fn add_wd_iteration_interval(
        &mut self,
        parent: &str,
        result: &SuccessVerifyIterationIntervalResult,
    ) {
        let id = format!("{parent}/interval");
        self.ensure_node(
            id.clone(),
            "well_definedness",
            "IterationInterval",
            result.parameter_set.to_string(),
            None,
        );
        self.add_edge(parent, &id, "interval", 0);
        match &result.coverage {
            SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(result) => {
                let coverage_id = format!("{id}/coverage");
                self.ensure_node(
                    coverage_id.clone(),
                    "well_definedness",
                    "UniversalIntegerCarrier",
                    result.parameter_set.to_string(),
                    None,
                );
                self.add_edge(&id, &coverage_id, "coverage", 0);
            }
            SuccessVerifyIterationCoverageResult::Enumerated(result) => {
                for (index, check) in result.checks.iter().enumerate() {
                    self.add_wd_fact_check(&id, "coverage", index, check);
                }
            }
            SuccessVerifyIterationCoverageResult::Endpoint(result) => {
                self.add_wd_fact_check(&id, "coverage", 0, &result.check);
            }
            SuccessVerifyIterationCoverageResult::IntervalSubset(result) => {
                self.add_wd_fact_check(&id, "coverage", 0, &result.check);
            }
        }
        for (index, child) in result.parameter_carriers.iter().enumerate() {
            self.add_wd_child(&id, "parameter_carrier", index, child);
        }
        for (index, premise) in result.parameters.iter().enumerate() {
            self.add_wd_binder_premise(&id, "parameter", index, premise);
        }
        for (index, (role, store)) in [
            ("lower_bound", &result.lower_bound),
            ("upper_bound", &result.upper_bound),
        ]
        .into_iter()
        .enumerate()
        {
            let store_id = format!("{id}/{role}");
            self.add_store_fact_result(store, store_id.clone());
            self.add_edge(&id, &store_id, role, index);
        }
        for (index, domain) in result.domains.iter().enumerate() {
            let domain_id = format!("{id}/domain:{index}");
            self.ensure_node(
                domain_id.clone(),
                "well_definedness",
                "IterationDomain",
                domain.proposition.to_string(),
                None,
            );
            self.add_edge(&id, &domain_id, "domain", index);
            let verification_id = format!("{domain_id}/verification");
            self.add_verify_fact_result(&domain.verification, verification_id.clone());
            self.add_edge(&domain_id, &verification_id, "verification", 0);
            let store_id = format!("{domain_id}/store");
            self.add_store_fact_result(&domain.store, store_id.clone());
            self.add_edge(&domain_id, &store_id, "store", 0);
        }
        self.add_wd_child(&id, "return_carrier", 0, &result.return_carrier);
        if let Some(body) = result.body.as_ref() {
            self.add_wd_child(&id, "body", 0, body);
        }
        if let Some(membership) = result.body_membership.as_ref() {
            self.add_wd_target_requirement(&id, "body_membership", 0, membership);
        }
    }

    fn add_wd_finite_aggregate(
        &mut self,
        parent: &str,
        result: &SuccessVerifyFiniteAggregateWellDefinedResult,
    ) {
        if let Some(scalar_return) = result.scalar_return.as_ref() {
            let id = format!("{parent}/scalar_return");
            self.ensure_node(
                id.clone(),
                "well_definedness",
                "IterationScalarReturn",
                result.operation.clone(),
                None,
            );
            self.add_edge(parent, &id, "scalar_return", 0);
            self.add_wd_signature_parts(
                &id,
                &scalar_return.parameter_carriers,
                &scalar_return.parameters,
                &scalar_return.domains,
                &scalar_return.return_carrier,
            );
            self.add_wd_fact_check(&id, "return_subset", 0, &scalar_return.return_subset);
        }
        match &result.mode {
            SuccessVerifyFiniteAggregateModeResult::Empty(result) => {
                self.add_wd_fact_check(parent, "empty_set", 0, &result.empty_set);
            }
            SuccessVerifyFiniteAggregateModeResult::Elements(result) => {
                for (index, check) in result.body_memberships.iter().enumerate() {
                    self.add_wd_fact_check(parent, "body_membership", index, check);
                }
                for (index, child) in result.applications.iter().enumerate() {
                    self.add_wd_child(parent, "application", index, child);
                }
            }
            SuccessVerifyFiniteAggregateModeResult::ClosedRange(result) => {
                self.add_wd_child(
                    parent,
                    "aggregate_dependency",
                    0,
                    &result.aggregate_dependency,
                );
            }
            SuccessVerifyFiniteAggregateModeResult::Symbolic(result) => {
                let id = format!("{parent}/symbolic");
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "SymbolicFiniteAggregate",
                    result.exact_domain.to_string(),
                    None,
                );
                self.add_edge(parent, &id, "symbolic", 0);
            }
        }
    }

    fn add_wd_reduce(&mut self, parent: &str, result: &SuccessVerifyReduceWellDefinedResult) {
        self.add_wd_fact_check(parent, "seed_membership", 0, &result.seed_membership);
        if let Some(laws) = result.operation_laws.as_ref() {
            let id = format!("{parent}/operation_laws");
            self.ensure_node(
                id.clone(),
                "well_definedness",
                "FiniteReduceOperationLaws",
                result.operation.clone(),
                None,
            );
            self.add_edge(parent, &id, "operation_laws", 0);
            self.add_wd_child(&id, "parameter_carrier", 0, &laws.parameter_carrier);
            for (index, premise) in laws.parameters.iter().enumerate() {
                self.add_wd_binder_premise(&id, "parameter", index, premise);
            }
            self.add_wd_fact_check(&id, "associativity", 0, &laws.associativity);
            self.add_wd_fact_check(&id, "commutativity", 0, &laws.commutativity);
        }
        match &result.mode {
            SuccessVerifyReduceModeResult::Empty(result) => {
                self.add_wd_fact_check(parent, "empty", 0, &result.empty_range_or_set);
            }
            SuccessVerifyReduceModeResult::Interval(result) => {
                self.add_wd_iteration_interval(parent, &result.interval);
            }
            SuccessVerifyReduceModeResult::Elements(result) => {
                for (index, check) in result.body_memberships.iter().enumerate() {
                    self.add_wd_fact_check(parent, "body_membership", index, check);
                }
                for (index, child) in result.applications.iter().enumerate() {
                    self.add_wd_child(parent, "application", index, child);
                }
            }
            SuccessVerifyReduceModeResult::Symbolic(result) => match &result.coverage {
                SuccessVerifyFiniteReduceDomainCoverageResult::Exact(result) => {
                    let id = format!("{parent}/exact_domain");
                    self.ensure_node(
                        id.clone(),
                        "well_definedness",
                        "ExactReduceDomain",
                        format!("{} = {}", result.aggregate_set, result.iterand_domain),
                        None,
                    );
                    self.add_edge(parent, &id, "coverage", 0);
                }
                SuccessVerifyFiniteReduceDomainCoverageResult::Subset(result) => {
                    self.add_wd_fact_check(parent, "coverage", 0, &result.subset);
                }
            },
        }
    }

    fn add_wd_structure(&mut self, parent: &str, result: &SuccessVerifyStructureWellDefinedResult) {
        for (index, argument) in result.header_arguments.iter().enumerate() {
            self.add_wd_fact_check(parent, "header_argument", index, &argument.verification);
        }
        for (index, domain) in result.header_domains.iter().enumerate() {
            self.add_wd_fact_check(parent, "header_domain", index, domain);
        }
        for (index, field) in result.fields.iter().enumerate() {
            let id = format!("{parent}/field:{index}");
            self.ensure_node(
                id.clone(),
                "well_definedness",
                "StructureField",
                field.field_name.clone(),
                None,
            );
            self.add_edge(parent, &id, "field", index);
            self.add_wd_child(&id, "carrier", 0, &field.carrier);
            self.add_wd_binder_premise(&id, "premise", 0, &field.premise);
        }
        for (index, fact) in result.equivalent_facts.iter().enumerate() {
            let id = format!("{parent}/equivalent_fact:{index}");
            self.ensure_node(
                id.clone(),
                "well_definedness",
                "StructureEquivalentFact",
                fact.proposition.to_string(),
                None,
            );
            self.add_edge(parent, &id, "equivalent_fact", index);
            let wd_id = format!("{id}/well-definedness");
            self.add_fact_well_definedness(
                &fact.well_definedness,
                wd_id.clone(),
                fact.proposition.to_string(),
            );
            self.add_edge(&id, &wd_id, "well_definedness", 0);
            let store_id = format!("{id}/store");
            self.add_store_fact_result(&fact.store, store_id.clone());
            self.add_edge(&id, &store_id, "store", 0);
        }
    }

    fn add_wd_template_materialization(
        &mut self,
        parent: &str,
        materialization: &SuccessVerifyTemplateMaterializationResult,
    ) {
        let id = format!("{parent}/template_materialization");
        match materialization {
            SuccessVerifyTemplateMaterializationResult::Reuse(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "ReuseTemplateMaterialization",
                    result.instance_name.clone(),
                    None,
                );
            }
            SuccessVerifyTemplateMaterializationResult::Materialized(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "MaterializedTemplate",
                    result.instance_name.clone(),
                    None,
                );
                for (index, argument) in result.header_arguments.iter().enumerate() {
                    self.add_wd_fact_check(&id, "header_argument", index, &argument.verification);
                }
                for (index, domain) in result.header_domains.iter().enumerate() {
                    self.add_wd_fact_check(&id, "header_domain", index, &domain.proof);
                    let store_id = format!("{id}/header_domain_store:{index}");
                    self.add_store_fact_result(&domain.store, store_id.clone());
                    self.add_edge(&id, &store_id, "header_domain_store", index);
                }
                let equality_id = format!("{id}/surface_equality");
                self.add_store_fact_result(&result.surface_equality, equality_id.clone());
                self.add_edge(&id, &equality_id, "surface_equality", 0);
                let body_id = format!("{id}/body_execution");
                self.add_stmt_result(&result.body_execution, body_id.clone());
                self.add_edge(&id, &body_id, "body_execution", 0);
                for (index, store) in result.public_value_equalities.iter().enumerate() {
                    let store_id = format!("{id}/public_value_equality:{index}");
                    self.add_store_fact_result(store, store_id.clone());
                    self.add_edge(&id, &store_id, "public_value_equality", index);
                }
                for (index, store) in result.supplemental_stores.iter().enumerate() {
                    let store_id = format!("{id}/supplemental_store:{index}");
                    self.add_store_fact_result(store, store_id.clone());
                    self.add_edge(&id, &store_id, "supplemental_store", index);
                }
            }
        }
        self.add_edge(parent, &id, "template_materialization", 0);
    }

    fn add_verify_fact_result(&mut self, result: &SuccessVerifyFactResult, id: String) {
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

    fn add_fact_proof(&mut self, proof: &SuccessFactProofResult, id: String) {
        match proof {
            SuccessFactProofResult::BuiltinRule(result) => {
                self.add_builtin_proof(result, id, "BuiltinRule");
            }
            SuccessFactProofResult::BuiltinStrategy(result) => {
                self.add_builtin_proof(result, id, "BuiltinStrategy");
            }
            SuccessFactProofResult::Fact(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "FactCitation",
                    result.cite_what.to_string(),
                    None,
                );
                self.add_cited_fact(
                    &id,
                    result.source_fact_id,
                    result.cite_what.to_string(),
                    "citation",
                    0,
                );
                if let Some(transport) = result.equality_transport.as_ref() {
                    for (index, step) in transport.steps.iter().enumerate() {
                        self.add_cited_fact(
                            &id,
                            step.equality_fact_id,
                            step.equality.to_string(),
                            "equality",
                            index,
                        );
                    }
                }
                if let Some(reduction) = result.definition_reduction.as_ref() {
                    for (index, child) in reduction.argument_verification.checks.iter().enumerate()
                    {
                        let child_id = format!("{id}/parameter:{index}");
                        self.add_stmt_result(child, child_id.clone());
                        self.add_edge(&id, &child_id, "parameter_check", index);
                    }
                    for (index, child) in reduction.clause_checks.iter().enumerate() {
                        let child_id = format!("{id}/clause:{index}");
                        self.add_stmt_result(child, child_id.clone());
                        self.add_edge(&id, &child_id, "clause_check", index);
                    }
                }
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
                for (index, item) in result.cite_what.iter().enumerate() {
                    let item_id = format!("{id}/item:{index}");
                    self.add_combined_proof_item(item, item_id.clone());
                    self.add_edge(&id, &item_id, "proof_part", index);
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
                    self.add_stmt_result(&proved.result, child_id.clone());
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
            }
            SuccessFactProofResult::Reuse(result) => {
                self.ensure_node(id.clone(), "proof", "Reuse", "shared proof", None);
                let source_id = self.add_shared_fact_result(&result.source);
                self.add_edge(&id, &source_id, "reuses", 0);
            }
        }
    }

    fn add_builtin_proof(
        &mut self,
        result: &SuccessBuiltinFactProofResult,
        id: String,
        role: &str,
    ) {
        self.ensure_node(id.clone(), "proof", role, result.msg.clone(), None);
        for (index, subgoal) in result.subgoals.iter().enumerate() {
            let child_id = format!("{id}/subgoal:{index}");
            self.add_stmt_result(subgoal, child_id.clone());
            self.add_edge(&id, &child_id, "subgoal", index);
        }
    }

    fn add_known_forall_proof(
        &mut self,
        result: &SuccessInstantiateKnownForallResult,
        id: String,
        role: &str,
    ) {
        self.ensure_node(
            id.clone(),
            "proof",
            role,
            result.cite_what.to_string(),
            None,
        );
        self.add_cited_fact(
            &id,
            result.source_fact_id,
            result.cite_what.to_string(),
            "citation",
            0,
        );
        for (index, requirement) in result.requirements.iter().enumerate() {
            let child_id = format!("{id}/requirement:{index}");
            self.add_stmt_result(&requirement.result, child_id.clone());
            self.add_edge(&id, &child_id, "requirement", index);
        }
    }

    fn add_combined_proof_item(&mut self, item: &SuccessCombinedFactProofItemResult, id: String) {
        match item {
            SuccessCombinedFactProofItemResult::ByBuiltinRule(result) => {
                self.ensure_node(id.clone(), "proof", "BuiltinRule", result.msg.clone(), None);
                for (index, subgoal) in result.subgoals.iter().enumerate() {
                    let child_id = format!("{id}/subgoal:{index}");
                    self.add_stmt_result(subgoal, child_id.clone());
                    self.add_edge(&id, &child_id, "subgoal", index);
                }
            }
            SuccessCombinedFactProofItemResult::ByBuiltinStrategy(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "BuiltinStrategy",
                    result.msg.clone(),
                    None,
                );
                for (index, subgoal) in result.subgoals.iter().enumerate() {
                    let child_id = format!("{id}/subgoal:{index}");
                    self.add_stmt_result(subgoal, child_id.clone());
                    self.add_edge(&id, &child_id, "subgoal", index);
                }
            }
            SuccessCombinedFactProofItemResult::ByFact(result) => {
                self.ensure_node(
                    id.clone(),
                    "proof",
                    "FactCitation",
                    result.cite_what.to_string(),
                    None,
                );
                self.add_cited_fact(
                    &id,
                    result.source_fact_id,
                    result.cite_what.to_string(),
                    "citation",
                    0,
                );
            }
            SuccessCombinedFactProofItemResult::ByKnownForall(result) => {
                self.add_known_forall_proof(&result.result, id, "KnownForallInstantiation");
            }
            SuccessCombinedFactProofItemResult::Reuse(result) => {
                self.ensure_node(id.clone(), "proof", "Reuse", "shared proof", None);
                let source_id = self.add_shared_fact_result(&result.source);
                self.add_edge(&id, &source_id, "reuses", 0);
            }
        }
    }

    fn add_shared_fact_result(&mut self, source: &Rc<SuccessVerifyFactResult>) -> String {
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
        if self.expanded_nodes.insert(id.clone()) {
            self.add_verify_fact_result(source, id.clone());
        }
        id
    }

    fn add_store_fact_result(&mut self, result: &SuccessStoreFactResult, id: String) {
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

    fn add_infers(&mut self, parent: &str, result: &SuccessInferResult, prefix: String) {
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

    fn add_cited_fact(
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

    fn ensure_fact_node_or_local(
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

    fn ensure_fact_node(&mut self, fact_id: FactId, label: String) -> String {
        let id = format!("fact:{fact_id}");
        self.ensure_node(id.clone(), "fact", "StoredFact", label, Some(fact_id));
        id
    }

    fn ensure_node(
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

    fn add_edge(&mut self, from: &str, to: &str, kind: &str, order: usize) {
        self.edges.push(ResultGraphEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind: kind.to_string(),
            order,
        });
    }

    pub(crate) fn summary_json(&self) -> JsonValue {
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(self.nodes.len())),
            ("edges".to_string(), JsonValue::Number(self.edges.len())),
            (
                "statements".to_string(),
                JsonValue::Number(self.count_kind("statement")),
            ),
            (
                "verifications".to_string(),
                JsonValue::Number(self.count_kind("verification")),
            ),
            (
                "well_definedness".to_string(),
                JsonValue::Number(self.count_kind("well_definedness")),
            ),
            (
                "proofs".to_string(),
                JsonValue::Number(self.count_kind("proof")),
            ),
            (
                "stores".to_string(),
                JsonValue::Number(self.count_kind("store") + self.count_kind("store_effect")),
            ),
            (
                "facts".to_string(),
                JsonValue::Number(self.count_kind("fact")),
            ),
            (
                "inferences".to_string(),
                JsonValue::Number(self.count_kind("inference")),
            ),
            (
                "unknowns".to_string(),
                JsonValue::Number(self.count_kind("unknown")),
            ),
        ])
    }

    fn count_kind(&self, kind: &str) -> usize {
        self.nodes.iter().filter(|node| node.kind == kind).count()
    }

    pub(crate) fn nodes_json(&self) -> JsonValue {
        JsonValue::Array(
            self.nodes
                .iter()
                .map(|node| {
                    JsonValue::Object(vec![
                        ("id".to_string(), JsonValue::JsonString(node.id.clone())),
                        ("kind".to_string(), JsonValue::JsonString(node.kind.clone())),
                        ("role".to_string(), JsonValue::JsonString(node.role.clone())),
                        (
                            "label".to_string(),
                            JsonValue::JsonString(node.label.clone()),
                        ),
                        (
                            "fact_id".to_string(),
                            node.fact_id
                                .map(|id| JsonValue::JsonString(id.to_string()))
                                .unwrap_or(JsonValue::Null),
                        ),
                    ])
                })
                .collect(),
        )
    }

    pub(crate) fn edges_json(&self) -> JsonValue {
        JsonValue::Array(
            self.edges
                .iter()
                .map(|edge| {
                    JsonValue::Object(vec![
                        ("from".to_string(), JsonValue::JsonString(edge.from.clone())),
                        ("to".to_string(), JsonValue::JsonString(edge.to.clone())),
                        ("kind".to_string(), JsonValue::JsonString(edge.kind.clone())),
                        ("order".to_string(), JsonValue::Number(edge.order)),
                    ])
                })
                .collect(),
        )
    }

    pub(crate) fn mermaid(&self) -> String {
        let mut lines = vec!["flowchart LR".to_string()];
        for (index, node) in self.nodes.iter().enumerate() {
            lines.push(format!(
                "  n{index}[\"{}: {}\"]",
                mermaid_label(&node.role),
                mermaid_label(&node.label)
            ));
        }
        for edge in self.edges.iter() {
            let Some(from) = self.node_index.get(&edge.from) else {
                continue;
            };
            let Some(to) = self.node_index.get(&edge.to) else {
                continue;
            };
            lines.push(format!(
                "  n{from} -->|{}| n{to}",
                mermaid_label(&edge.kind)
            ));
        }
        lines.join("\n")
    }
}

fn success_stmt_role(success: &SuccessStmtResult) -> &'static str {
    match success {
        SuccessStmtResult::Fact(_) => "Fact",
        SuccessStmtResult::UnsafeStmt(_) => "UnsafeStmt",
        SuccessStmtResult::DefObjStmt(_) => "DefObjStmt",
        SuccessStmtResult::DefPredicateStmt(_) => "DefPredicateStmt",
        SuccessStmtResult::DefInterfaceStmt(_) => "DefInterfaceStmt",
        SuccessStmtResult::DefAlgoStmt(_) => "DefAlgoStmt",
        SuccessStmtResult::DefThmStmt(_) => "DefThmStmt",
        SuccessStmtResult::AxiomStmt(_) => "AxiomStmt",
        SuccessStmtResult::DefStrategyStmt(_) => "DefStrategyStmt",
        SuccessStmtResult::By(_) => "ByStmt",
        SuccessStmtResult::Witness(_) => "WitnessStmt",
        SuccessStmtResult::ProofBlock(_) => "ProofBlockStmt",
        SuccessStmtResult::Command(_) => "CommandStmt",
    }
}

fn verify_fact_role(result: &SuccessVerifyFactResult) -> &'static str {
    match result {
        SuccessVerifyFactResult::AtomicFact(_) => "AtomicFact",
        SuccessVerifyFactResult::ExistFact(_) => "ExistFact",
        SuccessVerifyFactResult::OrFact(_) => "OrFact",
        SuccessVerifyFactResult::AndFact(_) => "AndFact",
        SuccessVerifyFactResult::ChainFact(_) => "ChainFact",
        SuccessVerifyFactResult::ForallFact(_) => "ForallFact",
        SuccessVerifyFactResult::ForallFactWithIff(_) => "ForallFactWithIff",
        SuccessVerifyFactResult::NotForallFact(_) => "NotForallFact",
    }
}

fn transform_role(rule: &FactTransformationRule) -> &'static str {
    match rule {
        FactTransformationRule::EqualityRewrite(_) => "EqualityRewrite",
        FactTransformationRule::RationalNormalization => "RationalNormalization",
    }
}

fn infer_rule_role(rule: &InferRule) -> &'static str {
    match rule {
        InferRule::NaturalMembershipImpliesNonnegative => "NaturalMembershipImpliesNonnegative",
        InferRule::PositiveStandardSetMembershipImpliesPositive(_) => {
            "PositiveStandardSetMembershipImpliesPositive"
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(_) => {
            "NegativeStandardSetMembershipImpliesNegative"
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(_) => {
            "NonzeroStandardSetMembershipImpliesNonzero"
        }
        InferRule::SetBuilderBaseMembershipProjection => "SetBuilderBaseMembershipProjection",
        InferRule::SetBuilderPredicateProjection { .. } => "SetBuilderPredicateProjection",
        InferRule::DefinedPredicateParameterRequirementProjection(_) => {
            "DefinedPredicateParameterRequirementProjection"
        }
        InferRule::DefinedPredicateDefinitionClauseProjection(_) => {
            "DefinedPredicateDefinitionClauseProjection"
        }
        InferRule::RegisteredTransitivePredicateChainClosure(_) => {
            "RegisteredTransitivePredicateChainClosure"
        }
        InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(_) => {
            "TupleEqualityWithKnownTupleImpliesTupleShape"
        }
        InferRule::ListSetMembershipImpliesEqualityAlternatives(_) => {
            "ListSetMembershipImpliesEqualityAlternatives"
        }
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
            "MultiplicationByNegativeOneReversesOrderAgainstZero"
        }
        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
            "StrictOrderComparedToZeroImpliesWeakOrder"
        }
        InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => {
            "MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet"
        }
        InferRule::SubsetImpliesElementwiseMembershipForall(_) => {
            "SubsetImpliesElementwiseMembershipForall"
        }
        InferRule::SupersetImpliesElementwiseMembershipForall(_) => {
            "SupersetImpliesElementwiseMembershipForall"
        }
        InferRule::ConjunctionImpliesComponent(_) => "ConjunctionImpliesComponent",
    }
}

fn atomic_predicate_domain_check_role(role: AtomicPredicateDomainCheckRole) -> &'static str {
    match role {
        AtomicPredicateDomainCheckRole::ChoiceFunctionIndexSet => "choice_index_set",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamilySet => "choice_family_set",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamily => "choice_family",
        AtomicPredicateDomainCheckRole::ChoiceFunctionMember => "choice_member",
        AtomicPredicateDomainCheckRole::PrimeNaturalArgument => "prime_natural_argument",
        AtomicPredicateDomainCheckRole::CoprimeNaturalArgument => "coprime_natural_argument",
        AtomicPredicateDomainCheckRole::DivisibilityIntegerArgument => {
            "divisibility_integer_argument"
        }
        AtomicPredicateDomainCheckRole::DivisibilityNonzeroIntegerArgument => {
            "divisibility_nonzero_integer_argument"
        }
        AtomicPredicateDomainCheckRole::OrderedRealCarrierEvidence => {
            "ordered_real_carrier_evidence"
        }
        AtomicPredicateDomainCheckRole::FunctionPropertySignature => "function_property_signature",
    }
}

fn mermaid_label(label: &str) -> String {
    label
        .replace('"', "'")
        .replace('\n', " ")
        .replace('\r', " ")
}
