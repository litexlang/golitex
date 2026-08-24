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
    assert!(!cli.join("cli.rs").exists());
    assert!(root.join("tests/unit/cli/command_dispatch").is_dir());
    assert!(!root.join("tests/unit/cli/cli").exists());
    let runner = root.join("src/runner");
    assert!(runner.join("target_execution.rs").is_file());
    assert!(!runner.join("runner.rs").exists());
    assert!(root
        .join("src/pipeline/source_execution/compatibility.rs")
        .is_file());
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
    let runtime = root.join("src/runtime");
    assert!(runtime.join("runtime_state.rs").is_file());
    assert!(!runtime.join("runtime.rs").exists());
    let parser = root.join("src/parse");
    assert!(parser.join("statement_parsing.rs").is_file());
    assert!(!parser.join("parse_stmt.rs").exists());
    assert!(root.join("tests/unit/parse/statement_parsing").is_dir());
    assert!(root
        .join("tests/unit/parse/statement_parsing/diagnostics.rs")
        .is_file());
    assert!(!root.join("tests/unit/parse/parse_stmt").exists());
    let execute = root.join("src/execute");
    let object_introduction = execute.join("object_introduction");
    assert!(object_introduction.is_dir());
    for responsibility in [
        "function_cases.rs",
        "function_equality.rs",
        "function_equality_support.rs",
        "function_induction.rs",
        "function_unique_existence.rs",
        "introduction_support.rs",
        "let_binding.rs",
        "object_equality.rs",
        "object_membership.rs",
        "obtain.rs",
        "preimage.rs",
        "sequence_and_matrix.rs",
        "tuple_and_cartesian.rs",
        "witness.rs",
    ] {
        assert!(object_introduction.join(responsibility).is_file());
    }
    for retired_root_file in [
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
        "exec_object_introduction_helper.rs",
        "exec_obtain_obj.rs",
        "exec_witness_stmt.rs",
    ] {
        assert!(!execute.join(retired_root_file).exists());
    }
    let execute_module =
        fs::read_to_string(execute.join("mod.rs")).expect("execute module should be readable");
    assert!(execute_module.contains("pub use object_introduction::function_equality_support;"));
    assert!(execute_module.contains(
        "pub use object_introduction::function_equality_support as exec_have_fn_equal_shared;"
    ));
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
    let source_execution = fs::read_to_string(root.join("src/pipeline/source_execution.rs"))
        .expect("source execution source should be readable");
    let source_execution_compatibility =
        fs::read_to_string(root.join("src/pipeline/source_execution/compatibility.rs"))
            .expect("source execution compatibility source should be readable");
    let runner_execution = fs::read_to_string(root.join("src/runner/target_execution.rs"))
        .expect("runner execution source should be readable");
    let runner_module = fs::read_to_string(root.join("src/runner/mod.rs"))
        .expect("runner module source should be readable");

    assert!(dispatch.contains("run_code_command("));
    assert!(!dispatch.contains("Runtime::new()"));
    assert!(!handlers.contains("command_dispatch::"));
    assert!(handlers.contains("resolve_source_file_path(file_flag)"));
    assert!(source_execution.contains("pub fn resolve_source_file_path("));
    let source_entry = source_execution
        .find("pub fn run_source_code(")
        .expect("canonical source entry should remain present");
    let structured_source_entry = source_execution
        .find("pub fn run_source_code_with_options(")
        .expect("structured source entry should remain present");
    let file_entry = source_execution
        .find("pub fn run_file(")
        .expect("canonical file entry should remain present");
    assert!(source_entry < structured_source_entry);
    assert!(structured_source_entry < file_entry);
    assert!(source_execution.contains("runtime.parse_statement(&mut block)"));
    assert!(!source_execution.contains("pub fn run_source_code_in_file_for_cli_with_"));
    assert!(source_execution_compatibility
        .contains("pub fn run_source_code_in_file_for_cli_with_strict("));
    assert!(runner_execution.contains("resolve_source_file_path(file_path)"));
    assert!(!runner_execution.contains("fn resolve_litex_file_path("));
    assert!(runner_module
        .contains("pub use crate::pipeline::resolve_source_file_path as resolve_litex_file_path;"));

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
