//! Statement-specific result traversal.

use super::*;

impl ResultGraph {
    pub(super) fn add_stmt_result(&mut self, result: &StmtResult, id: String) {
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

    pub(super) fn add_success_stmt(&mut self, success: &SuccessStmtResult, id: String) {
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

        if let SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(result)) =
            success
        {
            self.add_non_fact_well_definedness(success, &id);

            let domain_id = format!("{id}/domain");
            self.ensure_node(
                domain_id.clone(),
                "verification_scope",
                "SuccessVerifyLocalProofScopeResult",
                "claim domain",
                None,
            );
            self.add_edge(&id, &domain_id, "domain", 0);
            self.add_infers(
                &domain_id,
                &result.domain.assumption_infers,
                format!("{domain_id}/assumption"),
            );

            for (index, step) in result.proof_steps.iter().enumerate() {
                let step_id = format!("{id}/proof-step:{index}");
                self.add_stmt_result(step, step_id.clone());
                self.add_edge(&id, &step_id, "proof_step", index);
            }
            for (index, check) in result.conclusion_checks.iter().enumerate() {
                let check_id = format!("{id}/conclusion-check:{index}");
                self.add_verify_fact_outcome(check, check_id.clone());
                self.add_edge(&id, &check_id, "conclusion_check", index);
            }
            self.add_infers(
                &id,
                &result.environment_effects,
                format!("{id}/environment-effect"),
            );
            return;
        }

        let child_parent = if let Some(common) = success.common() {
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
            self.add_statement_specific_result_fields(success, &execution_id);
            execution_id
        } else {
            id.clone()
        };
        let mut index = 0;
        success.visit_child_results(&mut |child| {
            let child_id = format!("{child_parent}/child:{index}");
            self.add_stmt_result(child, child_id.clone());
            self.add_edge(&child_parent, &child_id, "child", index);
            index += 1;
        });
        success.visit_fact_verification_children(&mut |child| {
            let child_id = format!("{child_parent}/verification-child:{index}");
            self.add_verify_fact_outcome(child, child_id.clone());
            self.add_edge(&child_parent, &child_id, "verification_child", index);
            index += 1;
        });
        success.visit_success_child_results(&mut |child| {
            let child_id = format!("{child_parent}/success_child:{index}");
            self.add_success_stmt(child, child_id.clone());
            self.add_edge(&child_parent, &child_id, "body_statement_result", index);
            index += 1;
        });
        if let SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefTemplateStmt(result)) =
            success
        {
            self.add_fact_parameter_groups(&id, &result.template_parameter_groups);
            for (domain_index, domain) in result.template_domain_results.iter().enumerate() {
                self.add_local_fact_wd(&id, "template_domain", domain_index, domain);
            }
        }
    }

    pub(super) fn add_fact_stmt_result(
        &mut self,
        result: &SuccessFactStmtResult,
        statement_id: String,
    ) {
        match &result.evidence {
            FactStatementEvidence::Verified(verified) => {
                let verification_id = format!("{statement_id}/verification");
                let verification = VerifyFactResult::Verified(verified.clone());
                self.add_verify_fact_outcome(&verification, verification_id.clone());
                self.add_edge(&statement_id, &verification_id, "verification", 0);
            }
            FactStatementEvidence::Trusted(_) => {
                let trust_id = format!("{statement_id}/trusted");
                self.ensure_node(
                    trust_id.clone(),
                    "trust",
                    "TrustedFact",
                    result.fact().to_string(),
                    None,
                );
                self.add_edge(&statement_id, &trust_id, "trusted", 0);
            }
        }

        let store_id = format!("{statement_id}/store");
        self.add_store_fact_result(&result.store, store_id.clone());
        self.add_edge(&statement_id, &store_id, "store", 0);
    }

    pub(super) fn add_non_fact_well_definedness(
        &mut self,
        success: &SuccessStmtResult,
        parent: &str,
    ) {
        match success {
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefThmStmt(result)) => {
                if let Some(verification) = result.verification.as_ref() {
                    self.add_attached_fact_well_definedness(
                        parent,
                        &verification.well_definedness,
                        verification.fact.to_string(),
                        "well_definedness",
                        0,
                    );
                }
            }
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::AxiomStmt(result)) => {
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
                if let Some(well_definedness) = result.well_definedness.as_ref() {
                    self.add_attached_fact_well_definedness(
                        parent,
                        well_definedness,
                        result.statement.fact.to_string(),
                        "well_definedness",
                        0,
                    );
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

    pub(super) fn add_statement_specific_result_fields(
        &mut self,
        success: &SuccessStmtResult,
        parent: &str,
    ) {
        match success {
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefStructStmt(result)) => {
                self.add_def_struct_result_fields(parent, result)
            }
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::HaveFnByInducStmt(
                result,
            )) => self.add_have_fn_by_induc_result_fields(parent, result),
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefAlgoStmt(result)) => {
                if let Some(local) = result.run_in_local_env.as_ref() {
                    let id = format!("{parent}/def-algo-local");
                    self.ensure_node(
                        id.clone(),
                        "verification_scope",
                        "DefAlgoLocalEnv",
                        format!(
                            "{} in {}",
                            local.function_call, local.definition_function_set
                        ),
                        None,
                    );
                    self.add_edge(parent, &id, "run_in_local_env", 0);
                    for parameter in &local.parameter_retagging {
                        let parameter_id = format!("{id}/parameter:{}", parameter.parameter_index);
                        self.ensure_node(
                            parameter_id.clone(),
                            "scope_binding",
                            "DefAlgoParameterRetag",
                            format!(
                                "{} -> {}",
                                parameter.source_binding.name(),
                                parameter.verification_object
                            ),
                            None,
                        );
                        self.add_edge(
                            &id,
                            &parameter_id,
                            "parameter_retagging",
                            parameter.parameter_index,
                        );
                    }
                }
            }
            _ => {}
        }
    }

    pub(super) fn add_def_struct_result_fields(
        &mut self,
        parent: &str,
        result: &SuccessDefStructStmtResult,
    ) {
        let Some(local) = result.run_in_local_env.as_ref() else {
            return;
        };
        let local_id = format!("{parent}/def-struct-local");
        self.ensure_node(
            local_id.clone(),
            "verification_scope",
            "DefStructLocalEnv",
            result.statement.to_string(),
            None,
        );
        self.add_edge(parent, &local_id, "run_in_local_env", 0);

        if let Some(infers) = local.structure_parameter_definition.as_ref() {
            let id = format!("{local_id}/structure-parameters");
            self.ensure_node(
                id.clone(),
                "scope_binding",
                "StructureParameterDefinition",
                "structure parameters",
                None,
            );
            self.add_edge(&local_id, &id, "structure_parameter_definition", 0);
            self.add_infers(&id, infers, format!("{id}/infer"));
        }
        for domain in &local.structure_domains {
            self.add_attached_fact_well_definedness(
                &local_id,
                &domain.well_definedness,
                domain.proposition.to_string(),
                "structure_domain",
                domain.domain_index,
            );
        }
        for field in &local.field_types {
            let wd_id = self.add_shared_wd_obj(&field.well_definedness);
            self.add_edge(&local_id, &wd_id, "field_type", field.field_index);
        }

        let field_scope_id = format!("{local_id}/field-scope");
        self.ensure_node(
            field_scope_id.clone(),
            "verification_scope",
            "DefStructFieldLocalEnv",
            "structure fields and equivalent facts",
            None,
        );
        self.add_edge(
            &local_id,
            &field_scope_id,
            "field_scope_run_in_local_env",
            0,
        );
        for field in &local.field_scope_run_in_local_env.field_definitions {
            let id = format!("{field_scope_id}/field:{}", field.field_index);
            self.ensure_node(
                id.clone(),
                "scope_binding",
                "DefStructFieldDefinition",
                format!("{} : {}", field.binding.name(), field.field_type),
                None,
            );
            self.add_edge(&field_scope_id, &id, "field_definition", field.field_index);
            self.add_infers(&id, &field.infers, format!("{id}/infer"));
        }
        for (index, fact) in local
            .field_scope_run_in_local_env
            .equivalent_facts
            .iter()
            .enumerate()
        {
            self.add_local_fact_wd(&field_scope_id, "equivalent_fact", index, fact);
        }
    }

    pub(super) fn add_have_fn_by_induc_result_fields(
        &mut self,
        parent: &str,
        result: &SuccessHaveFnByInducStmtResult,
    ) {
        let Some(result) = result.verification.as_ref() else {
            return;
        };
        let wd = &result.well_definedness_run_in_local_env;
        let wd_id = format!("{parent}/have-fn-by-induc-wd-local");
        self.ensure_node(
            wd_id.clone(),
            "verification_scope",
            "HaveFnByInducWellDefinednessLocalEnv",
            wd.function_binding.name(),
            None,
        );
        self.add_edge(parent, &wd_id, "well_definedness_run_in_local_env", 0);
        self.add_shared_wd_obj_edge(
            &wd_id,
            "function_set_well_definedness",
            0,
            &wd.function_set_well_definedness,
        );
        self.add_shared_wd_obj_edge(
            &wd_id,
            "measure_well_definedness",
            0,
            &wd.measure_well_definedness,
        );
        self.add_shared_wd_obj_edge(
            &wd_id,
            "lower_bound_well_definedness",
            0,
            &wd.lower_bound_well_definedness,
        );
        self.add_have_fn_by_induc_parameters_and_domain(
            &wd_id,
            "parameters_and_domain",
            &wd.parameters_and_domain,
        );

        let verification = &result.verification_run_in_local_env;
        let verification_id = format!("{parent}/have-fn-by-induc-verification-local");
        self.ensure_node(
            verification_id.clone(),
            "verification_scope",
            "HaveFnByInducVerificationLocalEnv",
            "measure, recursive function, and cases",
            None,
        );
        self.add_edge(parent, &verification_id, "verification_run_in_local_env", 0);
        self.add_have_fn_by_induc_parameters_and_domain(
            &verification_id,
            "parameters_and_domain",
            &verification.parameters_and_domain,
        );
        self.add_shared_wd_obj_edge(
            &verification_id,
            "measure_well_definedness",
            0,
            &verification.measure.measure_well_definedness,
        );
        self.add_shared_wd_obj_edge(
            &verification_id,
            "lower_bound_well_definedness",
            0,
            &verification.measure.lower_bound_well_definedness,
        );
        let recursive_store_id = format!("{verification_id}/recursive-function-store");
        self.add_store_fact_result(
            &verification.recursive_function.membership_store,
            recursive_store_id.clone(),
        );
        self.add_edge(
            &verification_id,
            &recursive_store_id,
            "recursive_function",
            0,
        );
        self.add_have_fn_by_induc_case_list(&verification_id, "cases", &verification.cases);
    }

    pub(super) fn add_shared_wd_obj_edge(
        &mut self,
        parent: &str,
        role: &str,
        index: usize,
        result: &Rc<SuccessVerifyObjWellDefinedResult>,
    ) {
        let id = self.add_shared_wd_obj(result);
        self.add_edge(parent, &id, role, index);
    }

    pub(super) fn add_have_fn_by_induc_parameters_and_domain(
        &mut self,
        parent: &str,
        role: &str,
        result: &SuccessVerifyHaveFnByInducParametersAndDomainResult,
    ) {
        let id = format!("{parent}/{role}");
        self.ensure_node(
            id.clone(),
            "verification_scope",
            "HaveFnByInducParametersAndDomain",
            "function parameters and domain",
            None,
        );
        self.add_edge(parent, &id, role, 0);
        for group in &result.parameter_groups {
            let group_id = format!("{id}/parameter-group:{}", group.group_index);
            self.ensure_node(
                group_id.clone(),
                "scope_binding",
                "HaveFnByInducParameterGroup",
                group.definition.to_string(),
                None,
            );
            self.add_edge(&id, &group_id, "parameter_group", group.group_index);
            self.add_infers(&group_id, &group.infers, format!("{group_id}/infer"));
        }
        for domain in &result.domain_facts {
            let store_id = format!("{id}/domain-store:{}", domain.domain_index);
            self.add_store_fact_result(&domain.store, store_id.clone());
            self.add_edge(&id, &store_id, "domain_fact", domain.domain_index);
        }
    }

    pub(super) fn add_have_fn_by_induc_case_list(
        &mut self,
        parent: &str,
        role: &str,
        result: &SuccessVerifyHaveFnByInducCaseListResult,
    ) {
        let id = format!("{parent}/{role}");
        self.ensure_node(
            id.clone(),
            "verification_scope",
            "HaveFnByInducCaseList",
            result.coverage_fact.to_string(),
            None,
        );
        self.add_edge(parent, &id, role, 0);
        for (index, proof) in result.mutual_exclusions.iter().enumerate() {
            let proof_id = format!("{id}/mutual-exclusion:{index}");
            self.ensure_node(
                proof_id.clone(),
                "verification_scope",
                "HaveFnByInducCaseDisjointness",
                format!(
                    "{} vs {} / {:?}",
                    proof.left_case_index, proof.right_case_index, proof.orientation
                ),
                None,
            );
            self.add_edge(&id, &proof_id, "mutual_exclusion", index);
            let store_id = format!("{proof_id}/assumption-store");
            self.add_store_fact_result(&proof.assumption_store, store_id.clone());
            self.add_edge(&proof_id, &store_id, "assumption_store", 0);
        }
        for case in &result.cases {
            let case_id = format!("{id}/case:{}", case.case_index);
            self.ensure_node(
                case_id.clone(),
                "verification_scope",
                "HaveFnByInducCase",
                case.case_fact.to_string(),
                None,
            );
            self.add_edge(&id, &case_id, "case", case.case_index);
            let store_id = format!("{case_id}/assumption-store");
            self.add_store_fact_result(&case.assumption_store, store_id.clone());
            self.add_edge(&case_id, &store_id, "assumption_store", 0);
            match &case.body {
                SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) => {
                    self.add_shared_wd_obj_edge(
                        &case_id,
                        "return_value_well_definedness",
                        0,
                        &body.well_definedness,
                    );
                }
                SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(nested) => {
                    self.add_have_fn_by_induc_case_list(&case_id, "nested_cases", nested);
                }
            }
        }
    }

    pub(super) fn add_claim_well_definedness(
        &mut self,
        parent: &str,
        verification: &SuccessCheckedGoalBlockResult,
    ) {
        self.add_attached_fact_well_definedness(
            parent,
            &verification.well_definedness,
            verification.fact.to_string(),
            "well_definedness",
            0,
        );
    }

    pub(super) fn add_attached_fact_well_definedness(
        &mut self,
        parent: &str,
        result: &WellDefinedFactResult,
        label: String,
        edge_kind: &str,
        order: usize,
    ) {
        let id = format!("{parent}/{edge_kind}:{order}");
        self.add_fact_well_definedness(result, id.clone(), label);
        self.add_edge(parent, &id, edge_kind, order);
    }
}
