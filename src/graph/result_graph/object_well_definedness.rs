//! Object, binder, iteration, structure, and template well-definedness traversal.

use super::*;

impl ResultGraph {
    pub(super) fn add_shared_wd_obj(
        &mut self,
        result: &Rc<SuccessVerifyObjWellDefinedResult>,
    ) -> String {
        let key = Rc::as_ptr(result) as usize;
        if let Some(id) = self.shared_wd_obj_nodes.get(&key) {
            return id.clone();
        }
        let id = format!("shared-wd-object:{}", self.shared_wd_obj_nodes.len());
        self.shared_wd_obj_nodes.insert(key, id.clone());
        self.add_wd_obj(result, id.clone());
        id
    }

    pub(super) fn add_wd_obj(&mut self, result: &SuccessVerifyObjWellDefinedResult, id: String) {
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

    pub(super) fn add_wd_obj_steps(
        &mut self,
        parent: &str,
        steps: &SuccessVerifyObjWellDefinedStepsResult,
    ) {
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
        if let Some(instantiation) = steps.template_instantiation.as_ref() {
            self.add_wd_template_instantiation(parent, instantiation);
        }
    }

    pub(super) fn add_wd_child(
        &mut self,
        parent: &str,
        role: &str,
        order: usize,
        child: &SuccessVerifyChildObjWellDefinedResult,
    ) {
        let child_id = self.add_shared_wd_obj(&child.result);
        self.add_edge(parent, &child_id, role, order);
    }

    pub(super) fn add_wd_fact_check(
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

    pub(super) fn add_wd_binder_premise(
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

    pub(super) fn add_wd_object_binder(
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

    pub(super) fn add_wd_signature_parts(
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

    pub(super) fn add_wd_target_requirement(
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

    pub(super) fn add_wd_iteration(
        &mut self,
        parent: &str,
        result: &SuccessVerifyIterationWellDefinedResult,
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
        self.add_wd_iteration_interval(parent, &result.interval);
    }

    pub(super) fn add_wd_iteration_interval(
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

    pub(super) fn add_wd_finite_aggregate(
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

    pub(super) fn add_wd_reduce(
        &mut self,
        parent: &str,
        result: &SuccessVerifyReduceWellDefinedResult,
    ) {
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

    pub(super) fn add_wd_structure(
        &mut self,
        parent: &str,
        result: &SuccessVerifyStructureWellDefinedResult,
    ) {
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

    pub(super) fn add_wd_template_instantiation(
        &mut self,
        parent: &str,
        instantiation: &SuccessTemplateInstantiationResult,
    ) {
        let id = format!("{parent}/template_instantiation");
        match instantiation {
            SuccessTemplateInstantiationResult::Reused(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "ReusedTemplateInstance",
                    result.application.to_string(),
                    None,
                );
            }
            SuccessTemplateInstantiationResult::Created(result) => {
                self.ensure_node(
                    id.clone(),
                    "well_definedness",
                    "CreatedTemplateInstance",
                    result.application.to_string(),
                    None,
                );
                for (index, argument) in result.template_argument_results.iter().enumerate() {
                    self.add_wd_fact_check(&id, "template_argument", index, &argument.verification);
                }
                for (index, domain) in result.template_domain_results.iter().enumerate() {
                    self.add_wd_fact_check(&id, "template_domain", index, &domain.proof);
                    let store_id = format!("{id}/template_domain_store:{index}");
                    self.add_store_fact_result(&domain.store, store_id.clone());
                    self.add_edge(&id, &store_id, "template_domain_store", index);
                }
                let equality_id = format!("{id}/surface_equality");
                self.add_store_fact_result(&result.surface_equality, equality_id.clone());
                self.add_edge(&id, &equality_id, "surface_equality", 0);
                let body_id = format!("{id}/body_statement_result");
                self.add_success_stmt(&result.body_statement_result, body_id.clone());
                self.add_edge(&id, &body_id, "body_statement_result", 0);
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
        self.add_edge(parent, &id, "template_instantiation", 0);
    }
}
