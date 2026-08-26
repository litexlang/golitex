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

fn directories_below(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut directories = Vec::new();
    while let Some(path) = pending.pop() {
        for entry in fs::read_dir(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()))
        {
            let path = entry.expect("directory entry should be readable").path();
            if path.is_dir() {
                pending.push(path.clone());
                directories.push(path);
            }
        }
    }
    directories.sort();
    directories
}

#[test]
fn rust_visibility_does_not_regress_to_crate_only() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let forbidden = ["pub", "(crate)"].concat();
    let offenders: Vec<_> = [root.join("src"), root.join("tests")]
        .into_iter()
        .flat_map(|directory| rust_files_below(&directory))
        .filter(|path| {
            fs::read_to_string(path)
                .expect("Rust source should be readable")
                .contains(&forbidden)
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "crate-only visibility returned in: {offenders:#?}"
    );
}

#[test]
fn production_sources_contain_loaders_but_no_test_bodies() {
    let source_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let test_attribute = ["#[", "test]"].concat();
    let source_files = rust_files_below(&source_root);
    let offenders: Vec<_> = source_files
        .iter()
        .filter(|path| {
            fs::read_to_string(path)
                .expect("Rust source should be readable")
                .contains(&test_attribute)
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "test bodies must live below tests/, not src/: {offenders:#?}"
    );

    let cfg_test = ["#[cfg(", "test)]"].concat();
    let mut non_loader_cfg = Vec::new();
    for path in source_files {
        let source = fs::read_to_string(&path).expect("Rust source should be readable");
        let lines: Vec<_> = source.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            if line.trim() != cfg_test {
                continue;
            }
            let next = lines
                .get(index + 1)
                .map(|line| line.trim())
                .unwrap_or_default();
            if !next.starts_with("#[path = ") || !next.contains("tests/unit/") {
                non_loader_cfg.push((path.clone(), index + 1));
            }
        }
    }
    assert!(
        non_loader_cfg.is_empty(),
        "cfg(test) in src/ is reserved for tests/unit loaders: {non_loader_cfg:#?}"
    );
}

#[test]
fn compiler_and_test_directories_follow_the_repository_layout() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let manifest =
        fs::read_to_string(root.join("Cargo.toml")).expect("Cargo manifest should be readable");
    let cli = root.join("src/cli");
    assert!(cli.join("command_dispatch.rs").is_file());
    assert!(cli.join("lean_commands.rs").is_file());
    assert!(cli.join("conversion_commands.rs").is_file());
    assert!(!cli.join("cli.rs").exists());
    assert!(root.join("tests/unit/cli/command_dispatch").is_dir());
    assert!(!root.join("tests/unit/cli/cli").exists());
    let runner = root.join("src/runner");
    assert!(runner.join("target_execution.rs").is_file());
    assert!(!runner.join("runner.rs").exists());
    assert!(!root
        .join("src/pipeline/source_execution/compatibility.rs")
        .exists());
    let pipeline = root.join("src/pipeline");
    for responsibility in [
        "run.rs",
        "source_execution.rs",
        "file_execution.rs",
        "output_rendering.rs",
    ] {
        assert!(pipeline.join(responsibility).is_file());
    }
    assert!(!pipeline.join("execution_trace.rs").exists());
    let compiler = root.join("src/stmt_result_to_lean_compiler");
    assert!(root
        .join("src/bin/stmt_result_to_lean_compiler.rs")
        .is_file());
    assert!(!compiler.join("main.rs").exists());
    assert!(manifest.contains("path = \"src/bin/stmt_result_to_lean_compiler.rs\""));
    let compiler_cli_tests = root.join("tests/unit/stmt_result_to_lean_compiler");
    assert!(compiler_cli_tests.join("compiler_cli").is_dir());
    assert!(!compiler_cli_tests.join("main").exists());
    let compiler_contracts = root.join("tests/unit/kernel_contracts/stmt_result_to_lean_compiler");
    assert!(compiler_contracts.join("mod.rs").is_file());
    assert!(!root
        .join("tests/unit/kernel_contracts/stmt_result_to_lean_compiler.rs")
        .exists());
    for responsibility in [
        "builtin_evidence_and_fact_ids.rs",
        "definitions_and_collections.rs",
        "existentials_claims_and_theorems.rs",
        "forall_and_direct_fact_proofs.rs",
        "known_forall_and_transformations.rs",
        "proof_composition_and_scopes.rs",
        "registered_rules_and_environments.rs",
        "result_schema_contracts.rs",
    ] {
        assert!(compiler_contracts.join(responsibility).is_file());
    }
    assert!(compiler.join("implementation").is_dir());
    assert!(!compiler.join("stmt_result_to_lean_compiler").exists());
    assert!(compiler.join("compiler_state.rs").is_file());
    assert!(!compiler.join("stmt_result_to_lean_compiler.rs").exists());
    for current_file in [
        "source_compilation.rs",
        "file_compilation.rs",
        "markdown_compilation.rs",
        "compilation_report.rs",
        "compiler_environment.rs",
    ] {
        assert!(compiler.join(current_file).is_file());
    }
    for retired_file in [
        "compile_litex_source_to_lean_source.rs",
        "compile_litex_file_to_lean_file.rs",
        "compile_litex_markdown_code_blocks_to_lean_file.rs",
        "stmt_result_to_lean_compilation_report.rs",
        "stmt_result_to_lean_compiler_environment_stack.rs",
    ] {
        assert!(!compiler.join(retired_file).exists());
    }
    let result = root.join("src/result");
    for (directory, responsibilities) in [
        (
            "statement",
            &[
                "execution_trace.rs",
                "result.rs",
                "success.rs",
                "traversal.rs",
                "unknown.rs",
            ][..],
        ),
        (
            "verification",
            &[
                "builtin_evidence.rs",
                "success.rs",
                "success_access.rs",
                "unknown_fact.rs",
            ][..],
        ),
        ("well_definedness", &["proof.rs", "results.rs"][..]),
    ] {
        let group = result.join(directory);
        assert!(group.join("mod.rs").is_file());
        for responsibility in responsibilities {
            assert!(group.join(responsibility).is_file());
        }
    }
    assert!(result.join("object_evaluation.rs").is_file());
    for retired_root_file in [
        "builtin_rule_evidence.rs",
        "execution_trace.rs",
        "runtime_success.rs",
        "runtime_success_access.rs",
        "stmt_result.rs",
        "success_evaluate_obj_result.rs",
        "success_stmt_result.rs",
        "success_stmt_result_traversal.rs",
        "success_well_defined_result.rs",
        "unknown_fact_result.rs",
        "unknown_stmt_result.rs",
        "well_definedness_proof.rs",
    ] {
        assert!(!result.join(retired_root_file).exists());
    }
    let result_tests = root.join("tests/unit/result");
    for test_file in [
        "statement/execution_trace.rs",
        "statement/result.rs",
        "verification/success_access.rs",
    ] {
        assert!(result_tests.join(test_file).is_file());
    }
    let fact = root.join("src/fact");
    for (directory, responsibilities) in [
        (
            "atomic",
            &["arguments.rs", "conversions.rs", "core.rs", "metadata.rs"][..],
        ),
        (
            "composite",
            &[
                "conjunction_and_chain.rs",
                "disjunction.rs",
                "order_closure.rs",
                "quantifier_free.rs",
            ][..],
        ),
        (
            "quantified",
            &[
                "existential.rs",
                "nested.rs",
                "parameter_coverage.rs",
                "universal.rs",
                "universal_iff.rs",
            ][..],
        ),
        (
            "validation",
            &["fact_parameters.rs", "object_parameters.rs"][..],
        ),
    ] {
        let group = fact.join(directory);
        assert!(group.join("mod.rs").is_file());
        for responsibility in responsibilities {
            assert!(group.join(responsibility).is_file());
        }
    }
    assert!(fact.join("types.rs").is_file());
    assert!(fact.join("support.rs").is_file());
    for retired_root_file in [
        "atomic_fact.rs",
        "atomic_fact_args.rs",
        "atomic_fact_from.rs",
        "atomic_fact_metadata.rs",
        "chain_fact_order_closure.rs",
        "check_fact_has_no_duplicate_free_parameter.rs",
        "check_obj_has_no_duplicate_free_parameter.rs",
        "exist_fact.rs",
        "fact_inside_forall.rs",
        "fact_types.rs",
        "forall_fact.rs",
        "forall_fact_with_iff.rs",
        "helper.rs",
        "mark_forall_param_coverage.rs",
        "matchable_fact_with_atomic_fact_inside.rs",
        "or_fact.rs",
        "quantifier_free_fact.rs",
    ] {
        assert!(!fact.join(retired_root_file).exists());
    }
    let fact_tests = root.join("tests/unit/fact");
    assert!(fact_tests.join("composite/order_closure.rs").is_file());
    assert!(fact_tests.join("quantified/universal.rs").is_file());
    let runtime = root.join("src/runtime");
    assert!(runtime.join("state.rs").is_file());
    assert!(!runtime.join("runtime_state.rs").exists());
    assert!(!runtime.join("runtime.rs").exists());
    for (directory, responsibilities) in [
        (
            "instantiation",
            &["fact.rs", "function_forall.rs", "object.rs"][..],
        ),
        (
            "name_resolution",
            &[
                "bare_symbols.rs",
                "free_parameters.rs",
                "local_scopes.rs",
                "name_generation.rs",
                "object_resolution.rs",
                "parameter_definition.rs",
                "symbols.rs",
            ][..],
        ),
        (
            "definition_state",
            &[
                "lookup.rs",
                "object_properties.rs",
                "parameter_type_facts.rs",
                "support.rs",
            ][..],
        ),
    ] {
        let group = runtime.join(directory);
        assert!(group.join("mod.rs").is_file());
        for responsibility in responsibilities {
            assert!(group.join(responsibility).is_file());
        }
    }
    assert!(runtime.join("statement_proof_state.rs").is_file());
    assert!(runtime.join("fact_storage.rs").is_file());
    let repeated_runtime_source_names: Vec<_> = rust_files_below(&runtime)
        .into_iter()
        .filter(|path| {
            path.file_name()
                .is_some_and(|name| name.to_string_lossy().starts_with("runtime_"))
        })
        .collect();
    assert!(
        repeated_runtime_source_names.is_empty(),
        "runtime source files repeat their parent responsibility: {repeated_runtime_source_names:#?}"
    );
    let runtime_tests = root.join("tests/unit/runtime");
    for directory in [
        "instantiation/fact",
        "instantiation/object",
        "name_resolution/name_generation",
        "state",
        "statement_proof_state",
        "fact_storage",
    ] {
        assert!(runtime_tests.join(directory).is_dir());
    }
    let repeated_runtime_test_names: Vec<_> = directories_below(&runtime_tests)
        .into_iter()
        .filter(|path| {
            path.file_name()
                .is_some_and(|name| name.to_string_lossy().starts_with("runtime_"))
        })
        .collect();
    assert!(
        repeated_runtime_test_names.is_empty(),
        "runtime test directories repeat their parent responsibility: {repeated_runtime_test_names:#?}"
    );
    let parser = root.join("src/parse");
    assert!(parser.join("statement_parsing.rs").is_file());
    assert!(!parser.join("parse_stmt.rs").exists());
    assert!(root.join("tests/unit/parse/statement_parsing").is_dir());
    assert!(root
        .join("tests/unit/parse/statement_parsing/diagnostics.rs")
        .is_file());
    assert!(!root.join("tests/unit/parse/parse_stmt").exists());
    for (directory, responsibilities) in [
        (
            "object",
            &[
                "expression.rs",
                "collections.rs",
                "primary.rs",
                "reference.rs",
            ][..],
        ),
        ("fact", &["expression.rs", "parameter_definition.rs"][..]),
        (
            "statements",
            &[
                "claim.rs",
                "definition.rs",
                "evaluation.rs",
                "example.rs",
                "have_function.rs",
                "have_object.rs",
                "obtain_and_algorithm.rs",
                "sketch.rs",
                "strategy.rs",
                "theorem.rs",
                "tooling.rs",
                "trust_fact.rs",
                "try_block.rs",
                "witness.rs",
            ][..],
        ),
    ] {
        let group = parser.join(directory);
        assert!(group.is_dir());
        for responsibility in responsibilities {
            assert!(group.join(responsibility).is_file());
        }
    }
    assert!(parser.join("helper.rs").is_file());
    for retired_root_file in [
        "parse_claim_stmt.rs",
        "parse_def_stmt.rs",
        "parse_eval_stmt.rs",
        "parse_example_stmt.rs",
        "parse_fact.rs",
        "parse_have_function_stmt.rs",
        "parse_have_object_stmt.rs",
        "parse_helpers.rs",
        "parse_obj.rs",
        "parse_obj_collections.rs",
        "parse_obtain_and_algorithm_stmt.rs",
        "parse_param_def.rs",
        "parse_primary_obj.rs",
        "parse_reference_obj.rs",
        "parse_sketch_stmt.rs",
        "parse_strategy_stmt.rs",
        "parse_thm_stmt.rs",
        "parse_tooling_stmt.rs",
        "parse_trust_fact_stmt.rs",
        "parse_try_stmt.rs",
        "parse_witness.rs",
    ] {
        assert!(!parser.join(retired_root_file).exists());
    }
    let parser_tests = root.join("tests/unit/parse");
    for test_file in [
        "object/expression/module_qualification.rs",
        "object/expression/matrix_operators.rs",
        "object/expression/precedence.rs",
        "object/primary/keyword_objects.rs",
        "fact/expression/inline_forall.rs",
        "statements/evaluation.rs",
    ] {
        assert!(parser_tests.join(test_file).is_file());
    }
    let statements = root.join("src/stmt");
    for (directory, responsibilities) in [
        (
            "core",
            &[
                "conversions.rs",
                "display.rs",
                "metadata.rs",
                "type_names.rs",
                "types.rs",
            ][..],
        ),
        (
            "definitions",
            &[
                "algorithm.rs",
                "axiom.rs",
                "parameters.rs",
                "statement.rs",
                "strategy.rs",
                "structure.rs",
                "theorem.rs",
            ][..],
        ),
        (
            "proof_blocks",
            &[
                "claim.rs",
                "example.rs",
                "sketch.rs",
                "trust.rs",
                "try_block.rs",
                "witness.rs",
            ][..],
        ),
        ("commands", &["evaluation.rs", "tooling.rs"][..]),
    ] {
        let group = statements.join(directory);
        assert!(group.is_dir());
        for responsibility in responsibilities {
            assert!(group.join(responsibility).is_file());
        }
    }
    for retired_root_file in [
        "axiom_stmt.rs",
        "claim_stmt.rs",
        "define_algorithm_stmt.rs",
        "definition_stmt.rs",
        "eval_stmt.rs",
        "example_stmt.rs",
        "parameter_def.rs",
        "sketch_stmt.rs",
        "statement_types.rs",
        "stmt_display.rs",
        "stmt_from.rs",
        "stmt_metadata.rs",
        "stmt_type_name.rs",
        "strategy_stmt.rs",
        "struct_stmt.rs",
        "thm_stmt.rs",
        "tooling_stmt.rs",
        "trust_stmt.rs",
        "try_stmt.rs",
        "witness_stmt.rs",
    ] {
        assert!(!statements.join(retired_root_file).exists());
    }
    assert!(root
        .join("tests/unit/stmt/definitions/parameters.rs")
        .is_file());
    assert!(!root.join("tests/unit/stmt/parameter_def").exists());
    let verifier = root.join("src/verify");
    assert!(verifier.join("dispatch.rs").is_file());
    for (directory, responsibilities) in [
        (
            "atomic",
            &[
                "core.rs",
                "definition.rs",
                "function_membership.rs",
                "function_properties.rs",
                "known_facts.rs",
                "non_equational.rs",
                "numeric_membership.rs",
                "set_relations.rs",
                "universal_search.rs",
            ][..],
        ),
        (
            "composite",
            &[
                "conjunction_and_chain.rs",
                "disjunction.rs",
                "disjunction_search.rs",
            ][..],
        ),
        (
            "quantified",
            &[
                "existential.rs",
                "existential_search.rs",
                "negated_existential.rs",
                "not_universal.rs",
                "universal.rs",
                "universal_iff.rs",
            ][..],
        ),
        (
            "equality",
            &["core.rs", "function.rs", "function_set.rs", "patterns.rs"][..],
        ),
        (
            "proof_search",
            &[
                "builtin_rule.rs",
                "builtin_rule_state.rs",
                "builtin_strategy.rs",
                "context_state.rs",
                "explicit_syntax.rs",
                "universal_profile.rs",
            ][..],
        ),
        (
            "well_definedness",
            &["fact.rs", "local_environment.rs", "object.rs"][..],
        ),
        (
            "support",
            &[
                "argument_matching.rs",
                "helper.rs",
                "parameter_requirements.rs",
            ][..],
        ),
    ] {
        let group = verifier.join(directory);
        assert!(group.is_dir());
        for responsibility in responsibilities {
            assert!(group.join(responsibility).is_file());
        }
    }
    for responsibility in [
        "advanced.rs",
        "core.rs",
        "iterated.rs",
        "matrix.rs",
        "scalar.rs",
        "sets.rs",
        "structs.rs",
    ] {
        assert!(verifier
            .join("well_definedness/object")
            .join(responsibility)
            .is_file());
    }
    for retired_root_file in [
        "builtin_rule_verify_state.rs",
        "known_forall_profile.rs",
        "not_exist_demorgan_forall.rs",
        "use_context_verify_state.rs",
        "verify_and_chain_fact.rs",
        "verify_arg_satisfy_param_def.rs",
        "verify_atomic_fact.rs",
        "verify_atomic_fact_by_definition.rs",
        "verify_atomic_fact_with_known_forall.rs",
        "verify_atomic_fact_with_strategy.rs",
        "verify_builtin_rule.rs",
        "verify_builtin_strategy.rs",
        "verify_by_syntax.rs",
        "verify_dispatch.rs",
        "verify_equality.rs",
        "verify_equality_by_builtin_rules.rs",
        "verify_exist_fact.rs",
        "verify_exist_fact_with_known_forall.rs",
        "verify_fact_well_defined.rs",
        "verify_facts_the_same_type_and_return_matched_args.rs",
        "verify_fn_equal_in_builtin.rs",
        "verify_fn_membership_by_definition.rs",
        "verify_fn_set_equality_builtin_rule.rs",
        "verify_forall_fact.rs",
        "verify_forall_fact_with_iff.rs",
        "verify_function_properties_builtin.rs",
        "verify_helper.rs",
        "verify_known_atomic_facts.rs",
        "verify_non_equational_atomic_fact.rs",
        "verify_not_forall_fact.rs",
        "verify_number_in_standard_set.rs",
        "verify_obj_well_defined.rs",
        "verify_or_fact.rs",
        "verify_or_fact_with_known_forall.rs",
        "verify_proper_set_relations_builtin.rs",
        "verify_well_defined_in_local_env.rs",
    ] {
        assert!(!verifier.join(retired_root_file).exists());
    }
    assert!(!verifier.join("verify_obj_well_defined").exists());
    let verifier_tests = root.join("tests/unit/verify");
    for test_file in [
        "atomic/non_equational.rs",
        "equality/core.rs",
        "proof_search/builtin_rule.rs",
        "proof_search/builtin_rule_state.rs",
        "proof_search/context_state.rs",
        "quantified/existential_search.rs",
        "well_definedness/object.rs",
    ] {
        assert!(verifier_tests.join(test_file).is_file());
    }
    let execute = root.join("src/execute");
    let object_definitions = execute.join("definition_execution/object");
    assert!(object_definitions.is_dir());
    for responsibility in [
        "definition_support.rs",
        "existential_elimination.rs",
        "function_cases.rs",
        "function_equality.rs",
        "function_equality_support.rs",
        "function_induction.rs",
        "function_unique_existence.rs",
        "let_binding.rs",
        "object_equality.rs",
        "object_membership.rs",
        "preimage.rs",
        "sequence_and_matrix.rs",
        "tuple_and_cartesian.rs",
    ] {
        assert!(object_definitions.join(responsibility).is_file());
    }
    for (directory, responsibilities) in [
        (
            "definition_execution",
            &[
                "abstract_proposition.rs",
                "algorithm.rs",
                "axiom.rs",
                "definition_storage.rs",
                "parameter_definition.rs",
                "proposition.rs",
                "structure.rs",
                "template.rs",
                "theorem.rs",
            ][..],
        ),
        (
            "proof_block_execution",
            &["claim.rs", "goal_proof.rs", "sketch.rs", "try_block.rs"][..],
        ),
        ("command_execution", &["evaluation.rs"][..]),
        (
            "trust_execution",
            &["assumed_facts.rs", "parameterized_assumptions.rs"][..],
        ),
    ] {
        let group = execute.join(directory);
        assert!(group.join("mod.rs").is_file());
        for responsibility in responsibilities {
            assert!(group.join(responsibility).is_file());
        }
    }
    assert!(execute.join("strategy_execution.rs").is_file());
    assert!(execute.join("verified_fact_storage.rs").is_file());
    assert!(execute.join("witness_execution.rs").is_file());
    assert!(!execute.join("object_introduction").exists());
    for retired_root_file in [
        "exec_axiom_stmt.rs",
        "exec_claim_stmt.rs",
        "exec_def_abstract_prop_stmt.rs",
        "exec_def_algo_stmt.rs",
        "exec_def_prop_stmt.rs",
        "exec_def_struct_stmt.rs",
        "exec_def_template_stmt.rs",
        "exec_def_thm_stmt.rs",
        "exec_define_params_with_set.rs",
        "exec_eval_stmt.rs",
        "exec_goal_proof_block.rs",
        "exec_have_by_preimage_stmt.rs",
        "exec_have_fn_by_forall_exist_unique.rs",
        "exec_have_fn_by_induc.rs",
        "exec_have_fn_equal_case_by_case_stmt.rs",
        "exec_have_fn_equal_shared.rs",
        "exec_have_fn_equal_stmt.rs",
        "exec_have_obj_equal_stmt.rs",
        "exec_have_obj_in_nonempty_set_or_param_type_stmt.rs",
        "exec_have_seq_matrix_stmt.rs",
        "exec_have_tuple_cart_stmt.rs",
        "exec_let_obj_stmt.rs",
        "exec_object_definition_helper.rs",
        "exec_obtain_obj.rs",
        "exec_sketch_stmt.rs",
        "exec_store_definitions.rs",
        "exec_strategy_stmt.rs",
        "exec_tooling_stmt.rs",
        "exec_trust_have_stmt.rs",
        "exec_trust_stmt.rs",
        "exec_try_stmt.rs",
        "exec_verify_then_store_facts.rs",
        "exec_witness_stmt.rs",
    ] {
        assert!(!execute.join(retired_root_file).exists());
    }
    let execute_module =
        fs::read_to_string(execute.join("mod.rs")).expect("execute module should be readable");
    assert!(
        execute_module.contains("pub use definition_execution::object::function_equality_support;")
    );
    assert!(!execute_module.contains(" as exec_have_fn_equal_shared"));
    assert!(root.join("tests/unit").is_dir());
    assert!(root.join("tests/integration").is_dir());
    assert!(root.join("tests/tooling").is_dir());
}

#[test]
fn cli_dispatch_delegates_execution_and_path_resolution_to_their_owners() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let dispatch = fs::read_to_string(root.join("src/cli/command_dispatch.rs"))
        .expect("CLI dispatch source should be readable");
    let handlers = fs::read_to_string(root.join("src/cli/command_handlers.rs"))
        .expect("CLI handler source should be readable");
    let lean_commands = fs::read_to_string(root.join("src/cli/lean_commands.rs"))
        .expect("Lean command source should be readable");
    let conversion_commands = fs::read_to_string(root.join("src/cli/conversion_commands.rs"))
        .expect("conversion command source should be readable");
    let run = fs::read_to_string(root.join("src/pipeline/run.rs"))
        .expect("pipeline run source should be readable");
    let source_execution = fs::read_to_string(root.join("src/pipeline/source_execution.rs"))
        .expect("source execution source should be readable");
    let file_execution = fs::read_to_string(root.join("src/pipeline/file_execution.rs"))
        .expect("file execution source should be readable");
    let output_rendering = fs::read_to_string(root.join("src/pipeline/output_rendering.rs"))
        .expect("output rendering source should be readable");
    let runner_execution = fs::read_to_string(root.join("src/runner/target_execution.rs"))
        .expect("runner execution source should be readable");
    let graph_execution = fs::read_to_string(root.join("src/graph/graph_execution.rs"))
        .expect("graph execution source should be readable");

    assert!(dispatch.contains("run_code_command("));
    assert!(!dispatch.contains("Runtime::default()"));
    assert!(!dispatch.contains("compile_litex_file_to_lean_file("));
    assert!(!dispatch.contains("compile_litex_markdown_code_blocks_to_lean_file("));
    assert!(!dispatch.contains("compile_code_to_latex("));
    assert!(!dispatch.contains("compile_code_to_python("));
    assert!(!handlers.contains("command_dispatch::"));
    assert!(dispatch.contains("run_lean_file_command("));
    assert!(dispatch.contains("run_lean_ledger_command("));
    assert!(dispatch.contains("run_latex_command("));
    assert!(dispatch.contains("run_python_command("));
    assert!(lean_commands.contains("compile_litex_file_to_lean_file("));
    assert!(lean_commands.contains("compile_litex_markdown_code_blocks_to_lean_file("));
    assert!(conversion_commands.contains("compile_code_to_latex("));
    assert!(conversion_commands.contains("compile_code_to_python("));
    assert!(handlers.contains("RunTarget::code("));
    assert!(handlers.contains("RunTarget::file("));
    assert!(handlers.contains("RunTarget::repository("));
    assert!(run.contains("pub enum RunTarget"));
    assert!(run.contains("pub struct RunOptions"));
    assert!(run.contains("pub struct RunRequest"));
    assert!(run.contains("pub fn run(request: RunRequest)"));
    assert!(source_execution.contains("pub fn execute_source("));
    assert!(source_execution.contains("self.parse_statement(&mut block)"));
    assert!(!source_execution.contains("pub struct RunRequest"));
    assert!(!source_execution.contains("pub fn execute_file_in_runtime("));
    assert!(!source_execution.contains("pub fn render_run_output("));
    assert!(file_execution.contains("pub fn resolve_source_file_path("));
    assert!(file_execution.contains("pub fn execute_file_in_runtime("));
    assert!(output_rendering.contains("pub fn render_run_output("));
    assert!(!source_execution.contains("pub fn run_source_code_in_file"));
    assert!(!source_execution.contains("pub fn run_repository_with"));
    assert!(runner_execution.contains("pub fn run_runner(request: RunnerRequest)"));
    assert!(runner_execution.contains("let outcome = run(run_request);"));
    assert!(!runner_execution.contains("pub fn run_runner_for_"));
    assert!(graph_execution.contains("pub fn run_graph(request: GraphRequest)"));
    assert!(graph_execution.contains("let mut outcome = run(run_request);"));
    assert!(!graph_execution.contains("pub fn run_graph_for_"));

    let abbreviated_parser_call = [".parse_", "stmt("].concat();
    let abbreviated_callers: Vec<_> = [root.join("src"), root.join("tests")]
        .into_iter()
        .flat_map(|directory| rust_files_below(&directory))
        .filter(|path| {
            fs::read_to_string(path)
                .expect("Rust source should be readable")
                .contains(&abbreviated_parser_call)
        })
        .collect();
    assert!(
        abbreviated_callers.is_empty(),
        "repository callers must use parse_statement: {abbreviated_callers:#?}"
    );
}

#[test]
fn main_execution_spine_names_its_dependencies_explicitly() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let entry_files = [
        root.join("src/main.rs"),
        root.join("src/cli/arguments.rs"),
        root.join("src/cli/command_dispatch.rs"),
        root.join("src/cli/command_handlers.rs"),
        root.join("src/cli/conversion_commands.rs"),
        root.join("src/cli/lean_commands.rs"),
        root.join("src/pipeline/run.rs"),
        root.join("src/pipeline/file_execution.rs"),
        root.join("src/pipeline/source_execution.rs"),
        root.join("src/pipeline/top_level_statement_execution.rs"),
        root.join("src/pipeline/output_rendering.rs"),
        root.join("src/parse/statement_parsing.rs"),
        root.join("src/execute/statement_execution.rs"),
        root.join("src/execute/verified_statement_execution.rs"),
        root.join("src/execute/trusted_statement_execution.rs"),
        root.join("src/execute/submitted_fact_execution.rs"),
        root.join("src/verify/dispatch.rs"),
        root.join("src/verify/atomic/core.rs"),
        root.join("src/verify/atomic/non_equational.rs"),
        root.join("src/verify/equality/core.rs"),
        root.join("src/result/statement/result.rs"),
    ];
    let wildcard_prelude = ["prelude::", "*"].concat();
    let offenders: Vec<_> = entry_files
        .into_iter()
        .filter(|path| {
            fs::read_to_string(path)
                .expect("entry source should be readable")
                .contains(&wildcard_prelude)
        })
        .collect();
    assert!(
        offenders.is_empty(),
        "main execution-spine files must name dependency owners explicitly: {offenders:#?}"
    );
}

#[test]
fn atomic_and_equality_route_controls_use_semantic_names() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let atomic = fs::read_to_string(root.join("src/verify/atomic/non_equational.rs"))
        .expect("non-equational verifier should be readable");
    let equality = fs::read_to_string(root.join("src/verify/equality/core.rs"))
        .expect("equality verifier should be readable");
    let old_equal_route = ["verify_equal_fact_with_", "direct_routes"].concat();
    let old_atomic_route = ["verify_non_equational_atomic_fact_with_", "direct_routes"].concat();

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
    let statement_execution = fs::read_to_string(root.join("src/execute/statement_execution.rs"))
        .expect("statement execution source should be readable");
    let trusted_execution =
        fs::read_to_string(root.join("src/execute/trusted_statement_execution.rs"))
            .expect("trusted statement execution source should be readable");
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
fn proof_search_state_vocabulary_is_semantic() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let forbidden = [
        ["Use", "ContextVerifyState"].concat(),
        ["Use", "BuiltinRuleVerifyState"].concat(),
        ["ProofSearchState", "::new("].concat(),
        ["ProofSearchState", "::new_with_final_round"].concat(),
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

    let state = fs::read_to_string(root.join("src/verify/proof_search/context_state.rs"))
        .expect("proof-search state source should be readable");
    for constructor in [
        "pub fn initial()",
        "pub fn after_well_definedness()",
        "pub fn final_round()",
        "pub fn final_round_after_well_definedness()",
        "pub fn with_next_round(&self)",
        "pub fn with_well_definedness_verified(&self)",
        "pub fn is_initial_round(&self)",
    ] {
        assert!(state.contains(constructor), "missing `{constructor}`");
    }
}

#[test]
fn result_outcomes_and_atomic_polarity_use_distinct_vocabulary() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let result = fs::read_to_string(root.join("src/result/statement/result.rs"))
        .expect("statement result source should be readable");
    let atomic = fs::read_to_string(root.join("src/fact/atomic/core.rs"))
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
    let statement_cache = fs::read_to_string(root.join("src/runtime/statement_proof_state.rs"))
        .expect("statement proof cache source should be readable");
    let persistent_cache = fs::read_to_string(root.join("src/verify/support/helper.rs"))
        .expect("persistent verification cache source should be readable");
    let old_names = [
        ["verify_fact_from_cache_using_", "display_string"].concat(),
        ["verify_atomic_fact_from_", "statement_memo"].concat(),
        ["remember_successful_atomic_fact_", "for_statement"].concat(),
        ["new_with_", "statement_memo"].concat(),
    ];

    assert!(statement_cache.contains("verification_result_from_statement_proof_cache"));
    assert!(statement_cache.contains("cache_successful_atomic_fact_for_statement"));
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
        root.join("src/stmt_result_to_lean_compiler/implementation/result_dispatch.rs"),
    )
    .expect("compiler Result dispatcher should be readable");
    let fact_compilation = fs::read_to_string(
        root.join("src/stmt_result_to_lean_compiler/implementation/fact_compilation.rs"),
    )
    .expect("compiler fact implementation should be readable");
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
fn source_and_test_paths_do_not_repeat_their_parent_name() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let source_root = root.join("src");
    let repeated_source_directories: Vec<_> = directories_below(&source_root)
        .into_iter()
        .filter(|path| {
            let Some(name) = path.file_name() else {
                return false;
            };
            path.parent()
                .and_then(Path::file_name)
                .is_some_and(|parent_name| parent_name == name)
        })
        .collect();
    assert!(
        repeated_source_directories.is_empty(),
        "source directories must use responsibility names instead of repeating their parent: {repeated_source_directories:#?}"
    );

    let repeated_source_files: Vec<_> = rust_files_below(&source_root)
        .into_iter()
        .filter(|path| {
            let Some(stem) = path.file_stem() else {
                return false;
            };
            path.parent()
                .and_then(Path::file_name)
                .is_some_and(|parent_name| parent_name == stem)
        })
        .collect();
    assert!(
        repeated_source_files.is_empty(),
        "source files must name their responsibility instead of repeating their parent: {repeated_source_files:#?}"
    );

    let unit_test_root = root.join("tests/unit");
    let repeated_test_directories: Vec<_> = directories_below(&unit_test_root)
        .into_iter()
        .filter(|path| {
            let Some(name) = path.file_name() else {
                return false;
            };
            path.parent()
                .and_then(Path::file_name)
                .is_some_and(|parent_name| parent_name == name)
        })
        .collect();
    assert!(
        repeated_test_directories.is_empty(),
        "unit-test directories must mirror responsibilities without repeating their parent: {repeated_test_directories:#?}"
    );
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
    let environment = fs::read_to_string(root.join("src/environment.rs"))
        .expect("Environment source should be readable");
    let fact_store = fs::read_to_string(root.join("src/environment/facts/store.rs"))
        .expect("fact store should be readable");
    let forall_index =
        fs::read_to_string(root.join("src/environment/facts/forall_conclusion_index.rs"))
            .expect("forall conclusion index should be readable");
    let object_store = fs::read_to_string(root.join("src/environment/object_knowledge/store.rs"))
        .expect("object knowledge store should be readable");
    let object_value =
        fs::read_to_string(root.join("src/environment/object_knowledge/known_value.rs"))
            .expect("known object value should be readable");
    let predicate_store = fs::read_to_string(root.join("src/environment/predicates/store.rs"))
        .expect("predicate property store should be readable");
    let well_definedness_delta =
        fs::read_to_string(root.join("src/environment/well_definedness_environment_delta.rs"))
            .expect("well-definedness delta should be readable");

    for direct_owner in [
        "pub definitions: EnvironmentDefinitionRegistry",
        "pub facts: EnvironmentFactStore",
        "pub objects: EnvironmentObjectKnowledgeStore",
        "pub predicate_properties: EnvironmentPredicatePropertyStore",
        "pub caches: EnvironmentVerificationCache",
    ] {
        assert!(environment.contains(direct_owner));
    }
    assert!(!environment.contains("pub repositories:"));
    assert!(!environment.contains("impl Deref for Environment"));
    assert!(!environment.contains("EnvironmentPersistentRepositories"));
    assert!(!root.join("src/environment/environment_state.rs").exists());
    assert!(!root.join("src/environment/mod.rs").exists());
    assert!(!production_sources.contains("ParamObjType"));
    assert!(!production_sources.contains("defined_identifiers"));

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
fn definition_terminology_has_one_core_route_without_legacy_rust_names() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let statement_types = fs::read_to_string(root.join("src/stmt/core/types.rs"))
        .expect("statement types should be readable");
    let success_results = fs::read_to_string(root.join("src/result/statement/success.rs"))
        .expect("success result types should be readable");
    let environment = fs::read_to_string(root.join("src/environment.rs"))
        .expect("environment should be readable");
    let execute_module = fs::read_to_string(root.join("src/execute/mod.rs"))
        .expect("execute module should be readable");
    let parameter_types = fs::read_to_string(root.join("src/stmt/definitions/parameters.rs"))
        .expect("parameter types should be readable");
    let mut core_terminology_sources = [
        "src/stmt/core/types.rs",
        "src/result/statement/success.rs",
        "src/environment.rs",
        "src/environment/definitions/registry.rs",
        "src/environment/facts/store.rs",
        "src/environment/facts/stored_fact_store.rs",
        "src/execute/mod.rs",
        "src/obj/free_param_obj.rs",
        "src/obj/object_types.rs",
        "src/parse/object/reference.rs",
        "src/runtime/definition_state/object_properties.rs",
        "src/stmt/definitions/parameters.rs",
        "src/verify/atomic/function_membership.rs",
        "src/verify/verify_builtin_rules/in_fact_builtin/structured_membership.rs",
    ]
    .into_iter()
    .map(|relative| {
        fs::read_to_string(root.join(relative))
            .unwrap_or_else(|error| panic!("{relative} should be readable: {error}"))
    })
    .collect::<Vec<_>>();
    core_terminology_sources.extend(
        rust_files_below(&root.join("src/execute/definition_execution"))
            .into_iter()
            .map(|path| {
                fs::read_to_string(&path).unwrap_or_else(|error| {
                    panic!("{} should be readable: {error}", path.display())
                })
            }),
    );
    let core_terminology_sources = core_terminology_sources.join("\n");

    assert!(statement_types.contains("Definition(DefinitionStmt)"));
    assert!(success_results.contains("Definition(SuccessDefinitionStmtResult)"));
    assert!(environment.contains("pub definitions: EnvironmentDefinitionRegistry"));
    assert!(
        execute_module.contains("pub use definition_execution::object::function_equality_support;")
    );
    assert!(parameter_types.contains("pub struct TypedParameterList"));
    assert!(parameter_types.contains("pub struct SetBoundParameterList"));

    for legacy_name in [
        "DefObjStmt",
        "DefPredicateStmt",
        "DefInterfaceStmt",
        "SuccessDefObjStmtResult",
        "SuccessDefPredicateStmtResult",
        "SuccessDefInterfaceStmtResult",
        "EnvironmentDeclarationRegistry",
        "EnvironmentFactDatabase",
        "EnvironmentStoredFactRepository",
        "pub declarations:",
        "ObjectIntroductionItem",
        "ParamDefWithType",
        "ParamDefWithSet",
        "ParamGroupWithParamType",
        "ParamGroupWithSet",
        "BindingScope::DeclaredObject",
        "is_declared_object",
        "declaration_binding",
        "declared_identifier_obj",
        "build_declared_function_obj_with_param_bindings",
        "verify_value_in_declared_return_set",
        "declared_function_set",
    ] {
        assert!(
            !core_terminology_sources.contains(legacy_name),
            "legacy core name `{legacy_name}` returned"
        );
    }

    assert!(!root.join("src/execute/object_introduction").exists());
    assert!(root.join("docs/Developer_Terminology.md").is_file());
}
