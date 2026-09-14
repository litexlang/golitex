use std::fs;
use std::path::{Path, PathBuf};

fn rust_files_below(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();
    while let Some(path) = pending.pop() {
        for entry in fs::read_dir(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
        {
            let path = entry.expect("directory entry should be readable").path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

#[test]
fn output_graph_and_repository_concepts_do_not_collapse_back_into_monoliths() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for (directory, responsibilities) in [
        (
            "src/output/statement_result/renderer",
            &[
                "algorithm_definitions.rs",
                "binder_well_definedness.rs",
                "builtin_proofs.rs",
                "by_statements.rs",
                "cases_and_contradiction.rs",
                "claims_and_theorems.rs",
                "commands.rs",
                "definitions.rs",
                "fact_statements.rs",
                "fact_storage.rs",
                "fact_verification.rs",
                "fact_well_definedness.rs",
                "inductive_functions.rs",
                "iteration_well_definedness.rs",
                "known_forall.rs",
                "object_well_definedness.rs",
                "proof_blocks.rs",
                "shared_facts.rs",
                "state.rs",
                "statement_dispatch.rs",
                "structure_definitions.rs",
                "template_instantiation.rs",
                "tuple_functions.rs",
                "witnesses.rs",
            ][..],
        ),
        (
            "src/output/runtime_error",
            &[
                "fields.rs",
                "rendering.rs",
                "source_references.rs",
                "unknown.rs",
            ][..],
        ),
        (
            "src/output/messages",
            &[
                "rendering.rs",
                "catalogs/mod.rs",
                "catalogs/arabic.rs",
                "catalogs/chinese_simplified.rs",
                "catalogs/chinese_traditional.rs",
                "catalogs/french.rs",
                "catalogs/german.rs",
                "catalogs/hindi.rs",
                "catalogs/indonesian.rs",
                "catalogs/japanese.rs",
                "catalogs/korean.rs",
                "catalogs/portuguese.rs",
                "catalogs/russian.rs",
                "catalogs/spanish.rs",
                "catalogs/vietnamese.rs",
            ][..],
        ),
        (
            "src/graph/result_graph",
            &[
                "construction.rs",
                "fact_proofs.rs",
                "fact_well_definedness.rs",
                "inference_edges.rs",
                "model.rs",
                "object_well_definedness.rs",
                "rendering.rs",
                "roles.rs",
                "statement_results.rs",
            ][..],
        ),
        (
            "src/graph/fact_graph",
            &[
                "analysis.rs",
                "edge_collection.rs",
                "edge_rendering.rs",
                "entrypoints.rs",
                "graph_mutation.rs",
                "model.rs",
                "node_collection.rs",
                "node_rendering.rs",
                "rendering.rs",
                "source_resolution.rs",
            ][..],
        ),
        (
            "src/graph/definition_graph",
            &[
                "analysis.rs",
                "construction.rs",
                "definition_inventory.rs",
                "dependency_edges.rs",
                "edge_rendering.rs",
                "entrypoints.rs",
                "model.rs",
                "node_metadata.rs",
                "node_rendering.rs",
                "rendering.rs",
                "result_provenance.rs",
            ][..],
        ),
        (
            "src/module_system/repository_discovery",
            &[
                "config_exports.rs",
                "config_imports.rs",
                "filesystem_paths.rs",
                "import_cycles.rs",
                "model.rs",
                "module_config.rs",
                "project_authorization.rs",
                "project_config_files.rs",
                "requested_target.rs",
                "standard_library.rs",
                "terminal_imports.rs",
            ][..],
        ),
    ] {
        let concept = root.join(directory);
        assert!(concept.join("mod.rs").is_file());
        for responsibility in responsibilities {
            assert!(
                concept.join(responsibility).is_file(),
                "{directory} is missing concept responsibility {responsibility}"
            );
        }
        assert!(
            !root.join(format!("{directory}.rs")).exists(),
            "{directory} must remain a concept directory rather than a monolith"
        );
    }
}

#[test]
fn root_module_and_target_metadata_use_structured_state() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let registry = fs::read_to_string(root.join("src/module_system/registry.rs"))
        .expect("module registry should be readable");
    let runtime = fs::read_to_string(root.join("src/runtime/runtime.rs"))
        .expect("runtime state should be readable");
    let source_references =
        fs::read_to_string(root.join("src/output/runtime_error/source_references.rs"))
            .expect("source-reference renderer should be readable");
    let target_json = fs::read_to_string(root.join("src/output/json_value.rs"))
        .expect("target JSON renderer should be readable");
    let runner = fs::read_to_string(root.join("src/runner/target_execution.rs"))
        .expect("runner renderer should be readable");
    let result_graph = fs::read_to_string(root.join("src/graph/result_graph_execution.rs"))
        .expect("result-graph renderer should be readable");

    let retired_module_field = ["entry", "_module_id"].concat();
    let retired_path_field = ["entry", "_path_rc"].concat();
    let retired_module_constructor = ["create_", "entry", "_module"].concat();
    let retired_source_kind = ["SOURCE_KIND_", "ENTRY"].concat();

    for source in [&registry, &runtime] {
        assert!(!source.contains(&retired_module_field));
        assert!(!source.contains(&retired_path_field));
        assert!(!source.contains(&retired_module_constructor));
    }
    assert!(registry.contains("pub fn create_root_module("));
    assert!(registry.contains("pub fn create_repository_root_module("));
    assert!(!registry.contains("is_virtual_source"));
    assert!(!source_references.contains(&retired_source_kind));
    assert!(source_references.contains("SourcePath::VirtualSource"));
    assert!(target_json.contains("pub fn run_target_json_value("));
    assert!(target_json.contains("\"path\".to_string()"));
    for target_renderer in [&runner, &result_graph] {
        assert!(target_renderer.contains("run_target_json_value(target_kind.json_name()"));
        assert!(!target_renderer.contains("\"label\".to_string()"));
    }
}

#[test]
fn atomic_and_equality_route_controls_use_semantic_names() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let atomic = fs::read_to_string(root.join("src/verification/atomic/atomic_except_equality.rs"))
        .expect("atomic-except-equality verifier should be readable");
    let equality = fs::read_to_string(root.join("src/verification/equality/core.rs"))
        .expect("equality verifier should be readable");
    let old_equal_route = ["verify_equal_fact_with_", "direct_routes"].concat();
    let old_atomic_route = ["verify_atomic_except_equality_with_", "direct_routes"].concat();

    assert!(atomic.contains("enum AlternateFactSearch"));
    assert!(!atomic.contains("post_process: bool"));
    assert!(equality.contains("enum EqualitySide"));
    assert!(!equality.contains("application_is_left: bool"));
    for path in [root.join("src"), root.join("tests")] {
        for source_file in rust_files_below(&path) {
            let source = fs::read_to_string(&source_file).expect("Rust source should be readable");
            assert!(
                !source.contains(&old_equal_route),
                "{}",
                source_file.display()
            );
            assert!(
                !source.contains(&old_atomic_route),
                "{}",
                source_file.display()
            );
        }
    }
}

#[test]
fn source_execution_is_owned_by_runtime_without_a_secondary_context() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let statement_execution = fs::read_to_string(root.join("src/execution/statement_execution.rs"))
        .expect("statement execution source should be readable");
    let trusted_execution =
        fs::read_to_string(root.join("src/execution/statement_with_trust_execution.rs"))
            .expect("statement-with-trust execution source should be readable");
    let source_execution = fs::read_to_string(root.join("src/pipeline/source_execution.rs"))
        .expect("source execution source should be readable");

    assert!(!statement_execution.contains("StatementExecutionContext"));
    assert!(!trusted_execution.contains("StatementExecutionContext"));
    assert!(source_execution.contains("impl Runtime"));
    assert!(source_execution.contains("pub fn execute_source("));
    assert!(source_execution.contains("fn execute_source_blocks("));
    assert!(!source_execution.contains("execute_source_with_options"));
}

#[test]
fn verify_state_vocabulary_is_semantic() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let forbidden = [
        ["Use", "ContextVerifyState"].concat(),
        ["Use", "BuiltinRuleVerifyState"].concat(),
        ["VerifyState", "::new("].concat(),
        ["VerifyState", "::new_with_final_round"].concat(),
        ["BuiltinRuleSearchState", "::new("].concat(),
        ["new_state_with_", "round_increased"].concat(),
        ["with_well_defined_", "already_verified"].concat(),
        ["is_round_", "0"].concat(),
        ["well_defined_", "already_verified"].concat(),
    ];
    let offenders: Vec<_> = [root.join("src"), root.join("tests")]
        .into_iter()
        .flat_map(|directory| rust_files_below(&directory))
        .filter(|path| {
            let source = fs::read_to_string(path).expect("Rust source should be readable");
            forbidden.iter().any(|name| source.contains(name))
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "proof-search state must use the canonical semantic vocabulary: {offenders:#?}"
    );

    let state = fs::read_to_string(root.join("src/verification/proof_search/context_state.rs"))
        .expect("proof-search state source should be readable");
    assert!(state.contains("pub struct VerifyState"));
    let removed_list_membership_switch =
        ["list_set_membership_", "may_use_equality_builtin"].concat();
    assert!(!state.contains(&removed_list_membership_switch));
    for constructor in [
        "pub fn initial()",
        "pub fn final_round()",
        "pub fn with_next_round(&self)",
        "pub fn with_final_round(&self)",
        "pub fn with_child_proof_scope(&self)",
        "pub fn is_initial_round(&self)",
    ] {
        assert!(state.contains(constructor), "missing `{constructor}`");
    }
}

#[test]
fn claim_result_is_one_flat_execution_pipeline() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = fs::read_to_string(root.join("src/result/statement/success/proof_blocks.rs"))
        .expect("claim result source should be readable");
    let claim_start = result
        .find("pub struct SuccessClaimStmtResult {")
        .expect("flat claim result should exist");
    let claim_body = &result[claim_start..];
    let claim_end = claim_body
        .find("\n}")
        .expect("flat claim result should have a closing brace");
    let claim_body = &claim_body[..claim_end];
    let mut previous = 0;
    for field in [
        "pub statement: ClaimStmt",
        "pub well_definedness:",
        "pub domain:",
        "pub proof_steps:",
        "pub conclusion_checks:",
        "pub environment_effects:",
    ] {
        let position = claim_body
            .find(field)
            .unwrap_or_else(|| panic!("flat claim result is missing `{field}`"));
        assert!(
            position >= previous,
            "claim fields must follow execution order"
        );
        previous = position;
    }
    assert!(!claim_body.contains("pub common:"));
    assert!(!claim_body.contains("pub verification:"));
    assert!(!claim_body.contains(&["execution", "trace"].join("_")));

    let goal_proof =
        fs::read_to_string(root.join("src/execution/proof_block_execution/goal_proof.rs"))
            .expect("goal proof source should be readable");
    assert!(goal_proof.contains("pub fn verify_checked_goal_block("));
    assert!(goal_proof.contains("Result<SuccessCheckedGoalBlockResult, RuntimeError>"));
    assert!(!goal_proof.contains("SuccessClaimStmtResult"));
    assert!(!goal_proof.contains("ProofBlockStmt::ClaimStmt"));

    let claim = fs::read_to_string(root.join("src/execution/proof_block_execution/claim.rs"))
        .expect("claim execution source should be readable");
    let verification = claim
        .find("self.verify_checked_goal_block(")
        .expect("claim must execute the checked goal pipeline");
    let environment = claim
        .find("self.exec_claim_stmt_affect_environment(stmt)?")
        .expect("claim must publish its completed fact");
    let construction = claim
        .find("SuccessClaimStmtResult::checked(")
        .expect("claim must construct its flat result");
    assert!(verification < environment && environment < construction);
    assert!(!claim.contains(".with_infers("));

    let statement_execution = fs::read_to_string(root.join("src/execution/statement_execution.rs"))
        .expect("statement execution source should be readable");
    assert!(!statement_execution.contains("finish_statement_execution"));
    assert!(!statement_execution.contains("clear_statement_proof_state"));
}

#[test]
fn statement_results_expose_only_real_execution_artifacts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src = root.join("src");
    let retired_field = ["execution", "trace"].join("_");
    let retired_types = [
        ["Statement", "Execution", "Trace"].concat(),
        ["Execution", "Phase", "Trace"].concat(),
        ["Statement", "Phase", "Status"].concat(),
        ["Statement", "Execution", "Phase"].concat(),
    ];
    let offenders: Vec<_> = rust_files_below(&src)
        .into_iter()
        .filter(|path| {
            let source = fs::read_to_string(path).expect("Rust source should be readable");
            source.contains(&retired_field)
                || retired_types.iter().any(|name| source.contains(name))
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "statement results must expose execution artifacts directly, without a synthetic wrapper: {offenders:#?}"
    );

    let output = src.join("output");
    let retired_output_key = ["pha", "ses"].concat();
    let output_offenders: Vec<_> = rust_files_below(&output)
        .into_iter()
        .filter(|path| {
            let source = fs::read_to_string(path).expect("output source should be readable");
            source.contains(&format!("\"{retired_output_key}\""))
        })
        .collect();
    assert!(
        output_offenders.is_empty(),
        "rendered statement and error output must not reconstruct lifecycle phases: {output_offenders:#?}"
    );
}

#[test]
fn verification_local_environments_always_open_child_proof_scopes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let verification_root = root.join("src/verification");
    let local_environment = verification_root.join("well_definedness/local_environment.rs");
    let offenders: Vec<_> = rust_files_below(&verification_root)
        .into_iter()
        .filter(|path| path != &local_environment)
        .filter(|path| {
            let source = fs::read_to_string(path).expect("verification source should be readable");
            source.contains(".run_in_local_env(") || source.contains(".run_in_local_env_and_take(")
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "verification-local environments must use the proof-scope-aware adapter: {offenders:#?}"
    );

    let adapter = fs::read_to_string(&local_environment)
        .expect("local verification environment adapter should be readable");
    assert!(adapter.contains("verify_state.with_child_proof_scope()"));
    assert!(adapter.contains("run_in_local_verification_env"));
    assert!(adapter.contains("run_in_local_verification_env_and_take"));
}

#[test]
fn result_outcomes_and_atomic_polarity_use_distinct_vocabulary() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = fs::read_to_string(root.join("src/result/statement/result/inspection.rs"))
        .expect("statement result source should be readable");
    let atomic = fs::read_to_string(root.join("src/fact/atomic/classification.rs"))
        .expect("atomic fact source should be readable");
    let old_call = [".is_", "true()"].concat();
    let old_definition = ["fn is_", "true"].concat();

    assert!(result.contains("pub fn is_success(&self) -> bool"));
    assert!(atomic.contains("pub fn has_positive_polarity(&self) -> bool"));
    let offenders: Vec<_> = [root.join("src"), root.join("tests")]
        .into_iter()
        .flat_map(|directory| rust_files_below(&directory))
        .filter(|path| {
            let source = fs::read_to_string(path).expect("Rust source should be readable");
            source.contains(&old_call) || source.contains(&old_definition)
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "truth vocabulary must not conflate execution outcomes with fact polarity: {offenders:#?}"
    );
}

#[test]
fn verification_cache_vocabulary_names_scope_and_operation() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let proof_search_memo = fs::read_to_string(root.join("src/verification/proof_search/memo.rs"))
        .expect("proof-search memo source should be readable");
    let persistent_cache = fs::read_to_string(root.join("src/verification/support/helper.rs"))
        .expect("persistent verification cache source should be readable");
    let old_names = [
        ["verify_fact_from_cache_using_", "display_string"].concat(),
        ["verify_atomic_fact_from_", "statement_memo"].concat(),
        ["remember_successful_atomic_fact_", "for_statement"].concat(),
        ["new_with_", "statement_memo"].concat(),
        ["statement_", "proof_cache"].concat(),
    ];

    assert!(proof_search_memo.contains("verification_result_from_proof_search_memo"));
    assert!(proof_search_memo.contains("remember_successful_atomic_fact_for_proof_search"));
    assert!(persistent_cache.contains("verification_result_from_known_fact_cache"));
    let offenders: Vec<_> = [root.join("src"), root.join("tests")]
        .into_iter()
        .flat_map(|directory| rust_files_below(&directory))
        .filter(|path| {
            let source = fs::read_to_string(path).expect("Rust source should be readable");
            old_names.iter().any(|name| source.contains(name))
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "verification cache names must identify their scope and operation: {offenders:#?}"
    );
}

#[test]
fn result_to_lean_entry_and_dispatch_names_match_their_effects() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source_compilation =
        fs::read_to_string(root.join("src/stmt_result_to_lean_compiler/source_compilation.rs"))
            .expect("compiler source entry should be readable");
    let result_dispatch = fs::read_to_string(
        root.join("src/stmt_result_to_lean_compiler/compiler/result_dispatch.rs"),
    )
    .expect("compiler Result dispatcher should be readable");
    let fact_compilation =
        rust_files_below(&root.join("src/stmt_result_to_lean_compiler/compiler/fact_compilation"))
            .into_iter()
            .map(|path| {
                fs::read_to_string(path).expect("compiler fact implementation should be readable")
            })
            .collect::<Vec<_>>()
            .join("\n");
    let report =
        fs::read_to_string(root.join("src/stmt_result_to_lean_compiler/compilation_report.rs"))
            .expect("compiler report source should be readable");

    assert!(source_compilation.contains("compile_litex_source_to_lean_compilation_report"));
    assert!(source_compilation.contains("execute_litex_source_for_lean_compilation"));
    assert!(!source_compilation
        .contains("compile_litex_source_to_stmt_result_to_lean_compilation_report"));
    assert!(!source_compilation.contains("execute_litex_source_to_stmt_results"));
    assert!(result_dispatch.contains("fn compile_stmt_result("));
    assert!(!result_dispatch.contains("compile_stmt_result_to_lean_source"));
    assert!(result_dispatch.contains("fn unsupported_success_stmt_result("));
    assert!(!fact_compilation.contains("fn unsupported_success_stmt_result("));
    assert!(!report.contains("StmtResultReading"));
}

#[test]
fn environment_repeated_parent_filenames_are_exactly_the_owner_entrypoints() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let environment_root = root.join("src/environment");
    let mut repeated_files = rust_files_below(&environment_root)
        .into_iter()
        .filter(|path| {
            let Some(stem) = path.file_stem() else {
                return false;
            };
            path.parent()
                .and_then(Path::file_name)
                .is_some_and(|parent_name| parent_name == stem)
        })
        .collect::<Vec<_>>();
    repeated_files.sort();

    let mut expected = vec![
        root.join("src/environment/caches/caches.rs"),
        root.join("src/environment/definitions/definitions.rs"),
        root.join("src/environment/environment.rs"),
        root.join("src/environment/facts/facts.rs"),
        root.join("src/environment/object/object.rs"),
        root.join(
            "src/environment/predicate_algebraic_properties/predicate_algebraic_properties.rs",
        ),
    ];
    expected.sort();
    assert_eq!(repeated_files, expected);

    for (module_path, entrypoint_declaration, entrypoint_reexport) in [
        (
            "src/environment/mod.rs",
            "mod environment;",
            "pub use environment::Environment;",
        ),
        (
            "src/environment/definitions/mod.rs",
            "mod definitions;",
            "pub use definitions::EnvironmentDefinitionRegistry;",
        ),
        (
            "src/environment/facts/mod.rs",
            "mod facts;",
            "pub use facts::EnvironmentFactStore;",
        ),
        (
            "src/environment/object/mod.rs",
            "mod object;",
            "pub use object::EnvironmentObjectKnowledgeStore;",
        ),
        (
            "src/environment/predicate_algebraic_properties/mod.rs",
            "mod predicate_algebraic_properties;",
            "pub use predicate_algebraic_properties::EnvironmentPredicateAlgebraicPropertyStore;",
        ),
        (
            "src/environment/caches/mod.rs",
            "mod caches;",
            "pub use caches::EnvironmentInferenceCache;",
        ),
    ] {
        let module = fs::read_to_string(root.join(module_path))
            .unwrap_or_else(|error| panic!("{module_path} should be readable: {error}"));
        assert!(module.contains(entrypoint_declaration));
        assert!(module.contains(entrypoint_reexport));
        assert!(!module.contains("struct "));
        assert!(!module.contains("impl "));
        assert!(!module.contains("fn "));
    }
}

#[test]
fn environment_exposes_five_direct_owners_without_flat_compatibility_storage() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let production_sources = rust_files_below(&root.join("src"))
        .into_iter()
        .map(|path| {
            fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("{} should be readable: {error}", path.display()))
        })
        .collect::<Vec<_>>()
        .join("\n");
    let environment = fs::read_to_string(root.join("src/environment/environment.rs"))
        .expect("Environment source should be readable");
    let environment_module = fs::read_to_string(root.join("src/environment/mod.rs"))
        .expect("Environment module wiring should be readable");
    let fact_store = fs::read_to_string(root.join("src/environment/facts/facts.rs"))
        .expect("fact store should be readable");
    let forall_index = fs::read_to_string(root.join("src/environment/facts/forall_conclusions.rs"))
        .expect("forall conclusion index should be readable");
    let object_store = fs::read_to_string(root.join("src/environment/object/object.rs"))
        .expect("object knowledge store should be readable");
    let object_value = fs::read_to_string(root.join("src/environment/object/known_value.rs"))
        .expect("known object value should be readable");
    let predicate_store =
        fs::read_to_string(root.join(
            "src/environment/predicate_algebraic_properties/predicate_algebraic_properties.rs",
        ))
        .expect("predicate property store should be readable");
    let well_definedness_delta =
        fs::read_to_string(root.join("src/environment/well_definedness_environment_delta.rs"))
            .expect("well-definedness delta should be readable");

    for direct_owner in [
        "pub definitions: EnvironmentDefinitionRegistry",
        "pub facts: EnvironmentFactStore",
        "pub objects: EnvironmentObjectKnowledgeStore",
        "pub predicate_algebraic_properties: EnvironmentPredicateAlgebraicPropertyStore",
        "pub inference_cache: EnvironmentInferenceCache",
    ] {
        assert!(environment.contains(direct_owner));
    }
    assert!(!environment.contains("pub repositories:"));
    assert!(!environment.contains("impl Deref for Environment"));
    assert!(!environment.contains("EnvironmentPersistentRepositories"));
    assert!(!root.join("src/environment.rs").exists());
    assert!(!root.join("src/environment/environment_state.rs").exists());
    assert!(environment_module.contains("mod environment;"));
    assert!(environment_module.contains("pub use environment::Environment;"));
    assert!(!production_sources.contains("ParamObjType"));
    assert!(!production_sources.contains("defined_identifiers"));

    for owner_path in [
        "src/environment/definitions/definitions.rs",
        "src/environment/definitions/mod.rs",
        "src/environment/facts/facts.rs",
        "src/environment/facts/mod.rs",
        "src/environment/object/object.rs",
        "src/environment/predicate_algebraic_properties/predicate_algebraic_properties.rs",
        "src/environment/predicate_algebraic_properties/mod.rs",
        "src/environment/caches/caches.rs",
        "src/environment/caches/mod.rs",
        "src/environment/facts/known_equality.rs",
        "src/environment/facts/atomic.rs",
        "src/environment/facts/set_relations.rs",
        "src/environment/facts/quantified.rs",
        "src/environment/facts/forall_conclusions.rs",
        "src/environment/facts/stored_facts.rs",
    ] {
        assert!(
            root.join(owner_path).is_file(),
            "environment owner path should exist: {owner_path}"
        );
    }
    for retired_path in [
        "src/environment/definitions.rs",
        "src/environment/definitions/registry.rs",
        "src/environment/facts.rs",
        "src/environment/facts/store.rs",
        "src/environment/facts/atomic_index.rs",
        "src/environment/facts/set_relation_index.rs",
        "src/environment/facts/quantified_index.rs",
        "src/environment/facts/forall_conclusion_index.rs",
        "src/environment/facts/stored_fact_store.rs",
        "src/environment/object_knowledge",
        "src/environment/predicate_algebraic_properties.rs",
        "src/environment/predicates",
        "src/environment/caches.rs",
        "src/environment/verification_cache.rs",
    ] {
        assert!(
            !root.join(retired_path).exists(),
            "retired environment path should not exist: {retired_path}"
        );
    }

    for fact_owner in [
        "pub atomic: AtomicFactIndex",
        "pub set_relations: SetRelationIndex",
        "pub quantified: QuantifiedFactIndex",
        "pub forall_conclusions: ForallConclusionIndex",
        "pub stored_facts: EnvironmentStoredFactStore",
    ] {
        assert!(fact_store.contains(fact_owner));
    }
    assert!(forall_index.contains("pub struct ForallConclusionIndex"));
    assert!(!environment.contains("AtomicFactInForallArgShapeIndex"));
    assert!(!environment.contains("pub enum KnownObjValue"));

    assert!(object_store
        .contains("pub knowledge_by_object: HashMap<ObjString, EnvironmentObjectKnowledge>"));
    assert!(object_value.contains("pub enum KnownObjValue"));
    assert!(predicate_store
        .contains("pub properties_by_predicate: HashMap<String, EnvironmentPredicateProperties>"));
    assert!(well_definedness_delta.contains("pub struct WellDefinednessEnvironmentDelta"));
    assert!(well_definedness_delta.contains("pub fn apply_to("));
    assert!(!well_definedness_delta.contains("pub definitions:"));
    assert!(!well_definedness_delta.contains("pub facts:"));
}

#[test]
fn builtin_rules_use_typed_rust_evidence_without_a_runtime_catalog() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let success_results = rust_files_below(&root.join("src/result/verification/success"))
        .into_iter()
        .map(|path| {
            fs::read_to_string(&path).expect("verification success results should be readable")
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(success_results.contains(
        "pub enum SuccessBuiltinFactProofEvidenceResult {\n    Typed(BuiltinRuleEvidence),\n}"
    ));

    let production_sources = rust_files_below(&root.join("src"))
        .into_iter()
        .map(|path| {
            fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("{} should be readable: {error}", path.display()))
        })
        .collect::<Vec<_>>()
        .join("\n");
    for retired_mechanism in [
        "RegisteredLocalBuiltinRuleEvidence",
        "registered_local_builtin_rules",
        "semantic_fingerprint",
        "new_with_verified_by_builtin_rules_recording_stmt",
        "new_with_verified_by_builtin_strategy_recording_stmt",
        "new_with_verified_by_builtin_rules_label_and_steps",
        "SuccessBuiltinFactProofEvidenceResult::DiagnosticOnly",
    ] {
        assert!(
            !production_sources.contains(retired_mechanism),
            "retired runtime builtin mechanism `{retired_mechanism}` returned"
        );
    }

    for retired_module in [
        "src/verification/local_builtin_catalog/mod.rs",
        "src/verification/rule_schema/mod.rs",
    ] {
        assert!(
            !root.join(retired_module).exists(),
            "retired runtime builtin module `{retired_module}` returned"
        );
    }

    let json_output = rust_files_below(&root.join("src/output/statement_result/renderer"))
        .into_iter()
        .map(|path| fs::read_to_string(path).expect("Result JSON source should be readable"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(json_output.contains("string_field(\"rule_id\", evidence.rule_id())"));

    let compiler_validation =
        rust_files_below(&root.join("src/stmt_result_to_lean_compiler/compiler/validation"))
            .into_iter()
            .map(|path| {
                fs::read_to_string(path).expect("ToLean builtin validation should be readable")
            })
            .collect::<Vec<_>>()
            .join("\n");
    assert!(compiler_validation.contains("builtin rule `{}` has no reviewed ToLean mapping"));
}
