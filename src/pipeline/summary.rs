use crate::output::json_value::{render_json_value, JsonValue};
use crate::prelude::*;
use std::collections::{BTreeMap, HashSet};

#[derive(Clone, Debug, Default)]
pub struct RunSummary {
    pub statements: usize,
    pub top_level_statements: usize,
    pub statements_with_verification: usize,
    pub fact_statements: usize,
    pub prop_definitions: usize,
    pub abstract_prop_definitions: usize,
    pub theorem_statements: usize,
    pub by_statements: usize,
    pub proof_blocks: usize,
    pub object_definitions: usize,
    pub function_definitions: usize,
    pub direct_trust: usize,
    pub axioms: usize,
    pub trusted_object_assumptions: usize,
    pub abstract_interfaces: usize,
    pub stack_runner_warnings: usize,
    pub top_level_fact_statements: usize,
    pub nested_statements: usize,
    pub nested_fact_statements: usize,
    pub stored_fact_outputs: usize,
    pub inferred_fact_outputs: usize,
    statement_type_counts: BTreeMap<String, usize>,
    output_type_counts: BTreeMap<String, usize>,
    proof_method_counts: BTreeMap<String, usize>,
    by_theorem_counts: BTreeMap<String, usize>,
    builtin_rule_counts: BTreeMap<String, usize>,
    stored_fact_reason_counts: BTreeMap<String, usize>,
    inferred_builtin_rule_counts: BTreeMap<String, usize>,
    inferred_infer_rule_counts: BTreeMap<String, usize>,
    unverified_imports: Vec<UnverifiedImportSummary>,
    main_environment: Option<EnvironmentSummary>,
}

#[derive(Clone, Debug)]
struct UnverifiedImportSummary {
    kind: UnverifiedImportKind,
    name: String,
    line: usize,
    file: String,
}

#[derive(Clone, Debug, Default)]
struct EnvironmentSummary {
    field_key_counts: BTreeMap<String, usize>,
    field_item_counts: BTreeMap<String, usize>,
    category_counts: BTreeMap<String, usize>,
    fact_index_counts: BTreeMap<String, usize>,
}

impl RunSummary {
    pub fn from_run(
        stmt_results: &[StmtResult],
        runtime_error: &Option<RuntimeError>,
    ) -> RunSummary {
        let mut summary = RunSummary::default();
        summary.top_level_statements = stmt_results.len();
        for result in stmt_results {
            summary.visit_result(result, 0);
        }
        if let Some(error) = runtime_error {
            summary.visit_runtime_error(error);
        }
        summary
    }

    pub fn from_run_with_runtime(
        runtime: &Runtime,
        stmt_results: &[StmtResult],
        runtime_error: &Option<RuntimeError>,
    ) -> RunSummary {
        let mut summary = Self::from_run(stmt_results, runtime_error);
        summary.unverified_imports = runtime
            .unverified_imports()
            .iter()
            .map(|entry| UnverifiedImportSummary {
                kind: entry.kind,
                name: entry.name.clone(),
                line: entry.line_file.0,
                file: entry.line_file.1.to_string(),
            })
            .collect();
        if let Some(module) = runtime.module_manager.module(ModuleId::ROOT) {
            summary.main_environment = Some(EnvironmentSummary::from_environment(
                module.main_environment.as_ref(),
            ));
        }
        summary
    }

    fn visit_result(&mut self, result: &StmtResult, depth: usize) {
        if result.is_success() {
            self.statements_with_verification += 1;
        }
        if let Some(success) = result.factual_success() {
            self.visit_fact_stmt(&success.fact(), depth);
            self.visit_infer_result(&success.infers);
            if let Some(proof) = success.proof() {
                self.visit_verified_by(proof, depth);
            }
        }
        if let Some(success) = result.non_factual_success() {
            self.visit_stmt(&success.statement(), depth);
            if let Some(environment_effects) = success.environment_effects() {
                self.visit_infer_result(environment_effects);
            }
            self.visit_non_factual_verification(success);
            success.visit_child_results(&mut |child| self.visit_result(child, depth + 1));
            success.visit_fact_verification_children(&mut |child| {
                self.visit_verify_result(child, depth + 1)
            });
            success.visit_success_child_results(&mut |child| {
                self.visit_success_result(child, depth + 1)
            });
        }
    }

    fn visit_success_result(&mut self, success: &SuccessStmtResult, depth: usize) {
        if let Some(fact) = success.fact() {
            self.visit_fact_stmt(&fact.fact(), depth);
            self.visit_infer_result(&fact.infers);
            if let Some(proof) = fact.proof() {
                self.visit_verified_by(proof, depth);
            }
        } else {
            self.visit_stmt(&success.statement(), depth);
            if let Some(environment_effects) = success.environment_effects() {
                self.visit_infer_result(environment_effects);
            }
            self.visit_non_factual_verification(success);
            success.visit_child_results(&mut |child| self.visit_result(child, depth + 1));
            success.visit_fact_verification_children(&mut |child| {
                self.visit_verify_result(child, depth + 1)
            });
            success.visit_success_child_results(&mut |child| {
                self.visit_success_result(child, depth + 1)
            });
        }
    }

    fn visit_verify_result(&mut self, result: &VerifyFactResult, depth: usize) {
        if let Some(verified) = result.verified() {
            self.visit_verified_by(verified.proof(), depth);
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt, depth: usize) {
        self.record_stmt(stmt, depth);
        match stmt {
            Stmt::Fact(_) => {
                self.fact_statements += 1;
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustStmt(_)) => {
                self.direct_trust += 1;
            }
            Stmt::UnsafeStmt(UnsafeStmt::TrustHaveStmt(_)) => {
                self.trusted_object_assumptions += 1;
            }
            Stmt::Definition(definition) => match definition {
                DefinitionStmt::DefPropStmt(_) => self.prop_definitions += 1,
                DefinitionStmt::DefAbstractPropStmt(_) => {
                    self.abstract_prop_definitions += 1;
                    self.abstract_interfaces += 1;
                }
                DefinitionStmt::DefTemplateStmt(_) | DefinitionStmt::DefStructStmt(_) => {
                    self.abstract_interfaces += 1;
                }
                DefinitionStmt::DefThmStmt(_) => self.theorem_statements += 1,
                DefinitionStmt::AxiomStmt(_) => self.axioms += 1,
                DefinitionStmt::DefSettingStmt(_)
                | DefinitionStmt::DefAlgoStmt(_)
                | DefinitionStmt::DefStrategyStmt(_) => {}
                object_definition => {
                    self.object_definitions += 1;
                    if is_function_definition(object_definition) {
                        self.function_definitions += 1;
                    }
                }
            },
            Stmt::By(_) => {
                self.by_statements += 1;
            }
            Stmt::Witness(_) => {
                self.record_witness_stmt();
            }
            Stmt::ProofBlock(_) => {
                self.proof_blocks += 1;
            }
            _ => {}
        }
    }

    fn visit_fact_stmt(&mut self, fact: &Fact, depth: usize) {
        self.record_fact(fact, depth);
        self.fact_statements += 1;
        if depth == 0 {
            self.top_level_fact_statements += 1;
        } else {
            self.nested_fact_statements += 1;
        }
    }

    fn record_stmt(&mut self, stmt: &Stmt, depth: usize) {
        self.statements += 1;
        if depth > 0 {
            self.nested_statements += 1;
        }
        let statement_type = stmt.stmt_type_name();
        let output_type = stmt.output_type_string();
        self.bump_statement_type(statement_type.as_str());
        self.bump_output_type(output_type.as_str());
    }

    fn record_fact(&mut self, fact: &Fact, depth: usize) {
        self.statements += 1;
        if depth > 0 {
            self.nested_statements += 1;
        }
        let statement_type = fact.fact_type_string();
        let output_type = fact.output_type_string();
        self.bump_statement_type(statement_type.as_str());
        self.bump_output_type(output_type.as_str());
    }

    fn bump_statement_type(&mut self, statement_type: &str) {
        *self
            .statement_type_counts
            .entry(statement_type.to_string())
            .or_insert(0) += 1;
    }

    fn bump_output_type(&mut self, output_type: &str) {
        *self
            .output_type_counts
            .entry(output_type.to_string())
            .or_insert(0) += 1;
    }

    fn record_witness_stmt(&mut self) {
        bump_count(&mut self.proof_method_counts, "witness");
    }

    fn bump_by_method(&mut self, method: &str) {
        let label = format!("by {}", method);
        bump_count(&mut self.proof_method_counts, label.as_str());
    }

    fn visit_infer_result(&mut self, infer_result: &SuccessInferResult) {
        for output in infer_result.store_fact_outputs() {
            self.stored_fact_outputs += 1;
            self.inferred_fact_outputs += output.inferred_facts.len();
            let reason = &output.itself_and_why_itself_is_stored.1;
            bump_count(&mut self.stored_fact_reason_counts, reason);
            if let Some(rule) = reason_rule_name(reason, "inferred by builtin rule `") {
                bump_count(&mut self.inferred_builtin_rule_counts, rule.as_str());
            }
            if let Some(rule) = reason_rule_name(reason, "inferred by infer rule `") {
                bump_count(&mut self.inferred_infer_rule_counts, rule.as_str());
            }
        }
    }

    fn visit_verified_by(&mut self, verified_by: &SuccessFactProofResult, depth: usize) {
        match verified_by {
            SuccessFactProofResult::BuiltinRule(result) => {
                bump_count(&mut self.proof_method_counts, "builtin rule");
                bump_count(&mut self.builtin_rule_counts, result.msg.as_str());
                for subgoal in result.subgoals.iter() {
                    self.visit_verify_result(subgoal, depth + 1);
                }
            }
            SuccessFactProofResult::BuiltinStrategy(result) => {
                bump_count(&mut self.proof_method_counts, "builtin strategy");
                for subgoal in result.subgoals.iter() {
                    self.visit_verify_result(subgoal, depth + 1);
                }
            }
            SuccessFactProofResult::KnownForallInstantiation(result) => {
                bump_count(&mut self.proof_method_counts, "known forall instantiation");
                self.visit_known_forall_instantiation(result, depth);
            }
            SuccessFactProofResult::CombinedProofs(result) => {
                bump_count(&mut self.proof_method_counts, "combined proof");
                if let Some(primary) = result.primary.as_ref() {
                    self.visit_verified_by(primary.proof(), depth + 1);
                }
                for step in result.steps.iter() {
                    self.visit_verify_result(step, depth + 1);
                }
            }
            SuccessFactProofResult::ForallProof(result) => {
                bump_count(&mut self.proof_method_counts, "forall proof");
                self.visit_infer_result(&result.assumption_infers);
                for proved in result.proves.iter() {
                    self.visit_verify_result(&proved.result, depth + 1);
                    self.visit_infer_result(&proved.store.infers);
                }
            }
            SuccessFactProofResult::StoredFactCitation(_) => {
                bump_count(&mut self.proof_method_counts, "known fact");
            }
            SuccessFactProofResult::DefinitionReduction(_) => {
                bump_count(&mut self.proof_method_counts, "definition reduction");
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(_) => {
                bump_count(
                    &mut self.proof_method_counts,
                    "checked function definition reduction",
                );
            }
            SuccessFactProofResult::DiagnosticOnly(_) => {
                bump_count(&mut self.proof_method_counts, "diagnostic-only proof");
            }
            SuccessFactProofResult::Transform(result) => {
                bump_count(&mut self.proof_method_counts, "fact transform");
                self.visit_verified_by(result.source.proof(), depth + 1);
            }
            SuccessFactProofResult::Reuse(result) => {
                self.visit_verified_by(result.source.proof(), depth);
            }
        }
    }

    fn visit_known_forall_instantiation(
        &mut self,
        result: &SuccessInstantiateKnownForallResult,
        depth: usize,
    ) {
        for requirement in result.requirements.iter() {
            self.visit_verify_result(&requirement.result, depth + 1);
        }
    }

    fn visit_non_factual_verification(&mut self, success: &SuccessStmtResult) {
        match success {
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefThmStmt(result))
                if result.verification.is_some() =>
            {
                let theorem = result.verification.as_ref().unwrap();
                bump_count(&mut self.proof_method_counts, "theorem proof");
                self.visit_infer_result(&theorem.proof_scope.assumption_infers);
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ClaimStmt(result))
                if result.well_definedness.is_some() =>
            {
                bump_count(&mut self.proof_method_counts, "claim");
                self.visit_infer_result(&result.domain.assumption_infers);
            }
            SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::ExampleStmt(result))
                if result.verification.is_some() =>
            {
                let claim = result.verification.as_ref().unwrap();
                bump_count(&mut self.proof_method_counts, "claim");
                self.visit_infer_result(&claim.domain.assumption_infers);
            }
            SuccessStmtResult::ReleaseThmStmt(result) => {
                bump_count(&mut self.proof_method_counts, "theorem release");
                if let Some(verification) = &result.verification {
                    bump_count(&mut self.by_theorem_counts, verification.theorem.as_str());
                }
            }
            SuccessStmtResult::By(by) => self.visit_by_ir(by),
            _ => {}
        }
    }

    fn visit_by_ir(&mut self, by: &SuccessByStmtResult) {
        match by {
            SuccessByStmtResult::ByCasesStmt(_) => self.bump_by_method("cases"),
            SuccessByStmtResult::ByContraStmt(_) => self.bump_by_method("contra"),
            SuccessByStmtResult::ByEnumerateFiniteSetStmt(_) => {
                self.bump_by_method("enumerate finite set")
            }
            SuccessByStmtResult::ByEnumerateRangeStmt(_)
            | SuccessByStmtResult::ByClosedRangeAsCasesStmt(_) => {
                self.bump_by_method("enumerate range")
            }
            SuccessByStmtResult::ByFiniteSetInducStmt(_) | SuccessByStmtResult::ByInducStmt(_) => {
                self.bump_by_method("induc")
            }
            SuccessByStmtResult::ByForStmt(_) => self.bump_by_method("for"),
            SuccessByStmtResult::ByExtensionStmt(_) => self.bump_by_method("extension"),
            SuccessByStmtResult::ByTransitivePropStmt(result) => {
                self.visit_prop_registration_result(result.verification.as_ref())
            }
            SuccessByStmtResult::BySymmetricPropStmt(result) => {
                self.visit_prop_registration_result(result.verification.as_ref())
            }
            SuccessByStmtResult::ByReflexivePropStmt(result) => {
                self.visit_prop_registration_result(result.verification.as_ref())
            }
            SuccessByStmtResult::ByAntisymmetricPropStmt(result) => {
                self.visit_prop_registration_result(result.verification.as_ref())
            }
            SuccessByStmtResult::ByAxiomOfChoiceStmt(_) => self.bump_by_method("axiom of choice"),
            SuccessByStmtResult::ByZornLemmaStmt(_) => self.bump_by_method("zorn lemma"),
            SuccessByStmtResult::ByRegularityAxiomStmt(_) => {
                self.bump_by_method("regularity axiom")
            }
            SuccessByStmtResult::ByDefStmt(_) => self.bump_by_method("def"),
            SuccessByStmtResult::ByStructDefStmt(_) => self.bump_by_method("struct def"),
            SuccessByStmtResult::ByThmStmt(result) => {
                self.bump_by_method("theorem selection");
                if result.verification.is_some() {
                    let theorem_name = result.statement.name().to_string();
                    bump_count(&mut self.by_theorem_counts, theorem_name.as_str());
                }
            }
        }
    }

    fn visit_prop_registration_result(
        &mut self,
        result: Option<&SuccessVerifyByPropRegistrationResult>,
    ) {
        if let Some(result) = result {
            self.bump_by_method(result.registration_type.as_str());
        }
    }

    fn visit_runtime_error(&mut self, error: &RuntimeError) {
        let text = error.to_string().to_ascii_lowercase();
        if text.contains("stack") || text.contains("runner warning") {
            self.stack_runner_warnings += 1;
        }
    }

    fn to_json_value(&self, ok: bool) -> JsonValue {
        let result_label = if ok { "success" } else { "error" };
        JsonValue::Object(vec![
            (
                "result".to_string(),
                JsonValue::JsonString(result_label.to_string()),
            ),
            (
                "output_type".to_string(),
                JsonValue::JsonString("run summary".to_string()),
            ),
            (
                "proof_method_counts".to_string(),
                count_map_json_value(&self.proof_method_counts),
            ),
            (
                "direct_trust".to_string(),
                JsonValue::Number(self.direct_trust),
            ),
            ("axioms".to_string(), JsonValue::Number(self.axioms)),
            (
                "trusted_object_assumptions".to_string(),
                JsonValue::Number(self.trusted_object_assumptions),
            ),
            (
                "unverified_imports".to_string(),
                JsonValue::Array(
                    self.unverified_imports
                        .iter()
                        .map(UnverifiedImportSummary::json_value)
                        .collect(),
                ),
            ),
            (
                "main_environment".to_string(),
                self.main_environment_json_value(),
            ),
        ])
    }

    fn main_environment_json_value(&self) -> JsonValue {
        match &self.main_environment {
            Some(summary) => summary.json_value(),
            None => JsonValue::Null,
        }
    }
}

impl UnverifiedImportSummary {
    fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            (
                "kind".to_string(),
                JsonValue::JsonString(self.kind.as_str().to_string()),
            ),
            ("name".to_string(), JsonValue::JsonString(self.name.clone())),
            ("line".to_string(), JsonValue::Number(self.line)),
            ("file".to_string(), JsonValue::JsonString(self.file.clone())),
        ])
    }
}

impl EnvironmentSummary {
    fn from_environment(environment: &ExecEnv) -> Self {
        let mut summary = Self::default();

        summary.add_field_counts(
            "symbols",
            environment.definitions.symbols.len(),
            environment.definitions.symbols.len(),
        );
        summary.add_field_counts(
            "predicate_definitions",
            environment.definitions.predicate_definitions.len(),
            environment.definitions.predicate_definitions.len(),
        );
        summary.add_field_counts(
            "abstract_predicate_definitions",
            environment.definitions.abstract_predicate_definitions.len(),
            environment.definitions.abstract_predicate_definitions.len(),
        );
        summary.add_field_counts(
            "algorithm_definitions",
            environment.definitions.algorithm_definitions.len(),
            environment.definitions.algorithm_definitions.len(),
        );
        summary.add_field_counts(
            "structure_definitions",
            environment.definitions.structure_definitions.len(),
            environment.definitions.structure_definitions.len(),
        );
        summary.add_field_counts(
            "template_definitions",
            environment.definitions.template_definitions.len(),
            environment.definitions.template_definitions.len(),
        );
        summary.add_field_counts(
            "setting_definitions",
            environment.definitions.setting_definitions.len(),
            environment.definitions.setting_definitions.len(),
        );
        summary.add_field_counts(
            "theorem_definitions",
            environment.definitions.theorem_definitions.len(),
            environment.definitions.theorem_definitions.len(),
        );
        summary.add_field_counts(
            "axiom_definitions",
            environment.definitions.axiom_definitions.len(),
            environment.definitions.axiom_definitions.len(),
        );
        summary.add_field_counts(
            "strategy_definitions",
            environment.definitions.strategy_definitions.len(),
            environment.definitions.strategy_definitions.len(),
        );

        let equality_fact_count = unique_known_equality_count(environment);
        summary.add_field_counts(
            "known_equality",
            environment.facts.known_equality.len(),
            equality_fact_count,
        );

        let atomic_0_count = environment
            .facts
            .atomic
            .by_other_arg_count
            .values()
            .map(Vec::len)
            .sum::<usize>();
        summary.add_field_counts(
            "known_atomic_facts_with_0_or_more_than_2_args",
            environment.facts.atomic.by_other_arg_count.len(),
            atomic_0_count,
        );

        let atomic_1_count = environment
            .facts
            .atomic
            .by_one_arg
            .values()
            .map(|facts| facts.len())
            .sum::<usize>();
        summary.add_field_counts(
            "known_atomic_facts_with_1_arg",
            environment.facts.atomic.by_one_arg.len(),
            atomic_1_count,
        );

        let atomic_2_count = environment
            .facts
            .atomic
            .by_two_args
            .values()
            .map(|facts| facts.len())
            .sum::<usize>();
        summary.add_field_counts(
            "known_atomic_facts_with_2_args",
            environment.facts.atomic.by_two_args.len(),
            atomic_2_count,
        );

        let exist_count = environment
            .facts
            .quantified
            .existential
            .values()
            .map(Vec::len)
            .sum::<usize>();
        summary.add_field_counts(
            "known_exist_facts",
            environment.facts.quantified.existential.len(),
            exist_count,
        );

        let or_count = environment
            .facts
            .quantified
            .disjunctions
            .values()
            .map(Vec::len)
            .sum::<usize>();
        summary.add_field_counts(
            "known_or_facts",
            environment.facts.quantified.disjunctions.len(),
            or_count,
        );

        let forall_atomic_count = environment
            .facts
            .forall_conclusions
            .atomic_with_parameterized_head
            .values()
            .map(Vec::len)
            .sum::<usize>();
        summary.add_field_counts(
            "known_atomic_facts_in_forall_facts",
            environment
                .facts
                .forall_conclusions
                .atomic_with_parameterized_head
                .len(),
            forall_atomic_count,
        );

        let forall_atomic_by_shape_count = environment
            .facts
            .forall_conclusions
            .atomic_by_argument_shape
            .values()
            .map(|shape_map| shape_map.values().map(Vec::len).sum::<usize>())
            .sum::<usize>();
        summary.add_field_counts(
            "known_atomic_facts_in_forall_facts_by_arg_shape",
            environment
                .facts
                .forall_conclusions
                .atomic_by_argument_shape
                .len(),
            forall_atomic_by_shape_count,
        );

        let forall_exist_count = environment
            .facts
            .forall_conclusions
            .existential
            .values()
            .map(Vec::len)
            .sum::<usize>();
        summary.add_field_counts(
            "known_exist_facts_in_forall_facts",
            environment.facts.forall_conclusions.existential.len(),
            forall_exist_count,
        );

        let forall_and_count = environment
            .facts
            .forall_conclusions
            .conjunction
            .values()
            .map(Vec::len)
            .sum::<usize>();
        summary.add_field_counts(
            "known_and_facts_in_forall_facts",
            environment.facts.forall_conclusions.conjunction.len(),
            forall_and_count,
        );

        let forall_or_count = environment
            .facts
            .forall_conclusions
            .disjunction
            .values()
            .map(Vec::len)
            .sum::<usize>();
        summary.add_field_counts(
            "known_or_facts_in_forall_facts",
            environment.facts.forall_conclusions.disjunction.len(),
            forall_or_count,
        );

        summary.add_field_counts(
            "known_objs_equal_to_tuple",
            environment.object_properties.tuple_equality_count(),
            environment.object_properties.tuple_equality_count(),
        );
        summary.add_field_counts(
            "known_objs_equal_to_cart",
            environment.object_properties.cart_equality_count(),
            environment.object_properties.cart_equality_count(),
        );
        summary.add_field_counts(
            "known_objs_equal_to_finite_seq_list",
            environment
                .object_properties
                .finite_sequence_list_equality_count(),
            environment
                .object_properties
                .finite_sequence_list_equality_count(),
        );
        summary.add_field_counts(
            "known_objs_equal_to_matrix_list",
            environment.object_properties.matrix_list_equality_count(),
            environment.object_properties.matrix_list_equality_count(),
        );
        summary.add_field_counts(
            "known_obj_values",
            environment.object_properties.simplified_value_count(),
            environment.object_properties.simplified_value_count(),
        );
        summary.add_field_counts(
            "known_objs_equal_to_set_builder",
            environment.object_properties.set_builder_equality_count(),
            environment.object_properties.set_builder_equality_count(),
        );
        summary.add_field_counts(
            "known_objs_in_fn_sets",
            environment.object_properties.function_set_count(),
            environment.object_properties.function_set_count(),
        );
        summary.add_field_counts(
            "known_transitive_props",
            environment
                .prop_algebraic_properties
                .transitive_predicate_count(),
            environment
                .prop_algebraic_properties
                .transitive_predicate_count(),
        );

        let symmetric_permutation_count = environment
            .prop_algebraic_properties
            .symmetric_permutation_count();
        summary.add_field_counts(
            "known_symmetric_props",
            environment
                .prop_algebraic_properties
                .symmetric_predicate_count(),
            symmetric_permutation_count,
        );

        summary.add_field_counts(
            "known_reflexive_props",
            environment
                .prop_algebraic_properties
                .reflexive_predicate_count(),
            environment
                .prop_algebraic_properties
                .reflexive_predicate_count(),
        );
        summary.add_field_counts(
            "known_antisymmetric_props",
            environment
                .prop_algebraic_properties
                .antisymmetric_predicate_count(),
            environment
                .prop_algebraic_properties
                .antisymmetric_predicate_count(),
        );
        summary.add_field_counts(
            "stored_fact_lookup_keys",
            environment.facts.stored_facts.lookup_key_count(),
            environment.facts.stored_facts.lookup_key_count(),
        );
        summary.add_category_counts(environment);
        summary.add_fact_index_counts(environment);

        summary
    }

    fn add_field_counts(&mut self, name: &str, key_count: usize, item_count: usize) {
        self.field_key_counts.insert(name.to_string(), key_count);
        self.field_item_counts.insert(name.to_string(), item_count);
    }

    fn add_category_counts(&mut self, environment: &ExecEnv) {
        self.category_counts.insert(
            "objects".to_string(),
            environment.definitions.object_symbol_count(),
        );
        self.category_counts.insert(
            "props".to_string(),
            environment.definitions.predicate_definitions.len(),
        );
        self.category_counts.insert(
            "abstract_props".to_string(),
            environment.definitions.abstract_predicate_definitions.len(),
        );
        self.category_counts.insert(
            "algorithms".to_string(),
            environment.definitions.algorithm_definitions.len(),
        );
        self.category_counts.insert(
            "structs".to_string(),
            environment.definitions.structure_definitions.len(),
        );
        self.category_counts.insert(
            "templates".to_string(),
            environment.definitions.template_definitions.len(),
        );
        self.category_counts.insert(
            "settings".to_string(),
            environment.definitions.setting_definitions.len(),
        );
        self.category_counts.insert(
            "theorems".to_string(),
            environment.definitions.theorem_definitions.len(),
        );
        self.category_counts.insert(
            "axioms".to_string(),
            environment.definitions.axiom_definitions.len(),
        );
        self.category_counts.insert(
            "strategies".to_string(),
            environment.definitions.strategy_definitions.len(),
        );
        self.category_counts.insert(
            "known_facts".to_string(),
            environment.facts.stored_facts.lookup_key_count(),
        );
        self.category_counts.insert(
            "object_cache_entries".to_string(),
            environment
                .object_properties
                .old_summary_object_knowledge_count(),
        );
        self.category_counts.insert(
            "property_registrations".to_string(),
            environment
                .prop_algebraic_properties
                .property_registration_count(),
        );
    }

    fn add_fact_index_counts(&mut self, environment: &ExecEnv) {
        self.fact_index_counts.insert(
            "known_facts".to_string(),
            environment.facts.stored_facts.lookup_key_count(),
        );
    }

    fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            (
                "overview_counts".to_string(),
                count_map_json_value(&self.category_counts),
            ),
            (
                "known_fact_counts".to_string(),
                count_map_json_value(&self.fact_index_counts),
            ),
            (
                "environment_field_counts".to_string(),
                field_counts_json_value(&self.field_key_counts, &self.field_item_counts),
            ),
        ])
    }
}

pub struct RunSummaryRequest<'a> {
    pub runtime: &'a Runtime,
    pub stmt_results: &'a [StmtResult],
    pub runtime_error: &'a Option<RuntimeError>,
}

pub fn render_run_summary(request: RunSummaryRequest<'_>) -> String {
    let success = request.runtime_error.is_none();
    let summary = RunSummary::from_run_with_runtime(
        request.runtime,
        request.stmt_results,
        request.runtime_error,
    );
    let json = summary.to_json_value(success);
    render_json_value(&json, 0)
}

fn count_map_json_value(counts: &BTreeMap<String, usize>) -> JsonValue {
    JsonValue::Object(
        counts
            .iter()
            .map(|(name, count)| (name.clone(), JsonValue::Number(*count)))
            .collect(),
    )
}

fn field_counts_json_value(
    key_counts: &BTreeMap<String, usize>,
    item_counts: &BTreeMap<String, usize>,
) -> JsonValue {
    JsonValue::Object(
        key_counts
            .iter()
            .map(|(field_name, key_count)| {
                let item_count = item_counts.get(field_name).copied().unwrap_or(*key_count);
                (
                    field_name.clone(),
                    JsonValue::Object(vec![
                        ("map_keys".to_string(), JsonValue::Number(*key_count)),
                        ("stored_items".to_string(), JsonValue::Number(item_count)),
                    ]),
                )
            })
            .collect(),
    )
}

fn bump_count(counts: &mut BTreeMap<String, usize>, name: &str) {
    *counts.entry(name.to_string()).or_insert(0) += 1;
}

fn reason_rule_name(reason: &str, prefix: &str) -> Option<String> {
    let rest = reason.strip_prefix(prefix)?;
    let rule = rest.strip_suffix('`')?;
    Some(rule.to_string())
}

fn unique_known_equality_count(environment: &ExecEnv) -> usize {
    let mut seen = HashSet::new();
    for (direct_proof_map, _) in environment.facts.known_equality.values() {
        for fact in direct_proof_map.values() {
            seen.insert(fact.to_string());
        }
    }
    seen.len()
}

fn is_function_definition(stmt: &DefinitionStmt) -> bool {
    match stmt {
        DefinitionStmt::HaveFnEqualStmt(_)
        | DefinitionStmt::HaveFnEqualCaseByCaseStmt(_)
        | DefinitionStmt::HaveFnByInducStmt(_)
        | DefinitionStmt::HaveFnByForallExistUniqueStmt(_) => true,
        _ => false,
    }
}
