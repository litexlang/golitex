use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult};
use crate::runtime::CodeSource;

fn load_prefix() -> crate::run_module::LoadedLeanSource {
    let command = parse_launch_command(&[
        "-lean".into(),
        "-strict".into(),
        "-f".into(),
        "lean/examples/module_export_prefix/statement.lit".into(),
    ])
    .unwrap();
    let LoadLeanSourceResult::Success(loaded) = load_file_for_lean(command).unwrap() else {
        panic!("original project prefix must verify")
    };
    loaded
}

#[test]
fn module_loader_retains_actual_export_prefix_and_original_qualified_callee() {
    let loaded = load_prefix();
    assert_eq!(
        loaded.runtime.result_detail(),
        crate::result_detail::OutputDetail::Detailed
    );
    assert_eq!(loaded.closure.files.len(), 2);
    assert_eq!(loaded.closure.target_file, 1);
    assert!(matches!(
        loaded.closure.files[0].source,
        CodeSource::RootExport {
            export_file_id: 0,
            ..
        }
    ));
    assert!(matches!(
        loaded.closure.files[1].source,
        CodeSource::RootExport {
            export_file_id: 1,
            ..
        }
    ));
    for file in &loaded.closure.files {
        assert!(file.run.success);
    }
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(call))) =
        &loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("actual theorem call")
    };
    assert!(matches!(
        call.call.name,
        AtomicName::WithExportFileId {
            export_file_id: 0,
            ..
        }
    ));
    assert!(loaded.runtime.execution_environments_stack.is_empty());
}

#[test]
fn module_prefix_compiles_all_original_files_in_distinct_namespaces() {
    let loaded = load_prefix();
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let output = compiler
        .compile_module(&loaded.closure, "module_prefix")
        .unwrap();
    assert!(output.contains("namespace source_0"));
    assert!(output.contains("namespace source_1"));
    assert!(!output.contains("namespace source_2"));
    assert!(output.contains("source_0.h_"));
    assert_eq!(output.matches("import Litex").count(), 1);
    assert_eq!(
        output,
        compiler
            .compile_module(&loaded.closure, "module_prefix")
            .unwrap()
    );
}

fn target_call(
    loaded: &mut crate::run_module::LoadedLeanSource,
) -> &mut crate::execute::execute_by_stmt::ExecByThmStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(call))) =
        &mut loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("original call")
    };
    call
}

#[test]
fn module_callee_rejects_missing_future_and_changed_original_capture() {
    for export in [1, 2, 99] {
        let mut loaded = load_prefix();
        let AtomicName::WithExportFileId { export_file_id, .. } =
            &mut target_call(&mut loaded).call.name
        else {
            panic!("qualified")
        };
        *export_file_id = export;
        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        assert!(compiler
            .compile_module(&loaded.closure, "bad_callee")
            .is_err());
    }
    let mut loaded = load_prefix();
    let ResolvedTheoremCallee::UserTheorem(declaration) = &mut target_call(&mut loaded).callee
    else {
        panic!("user theorem")
    };
    declaration.name.push_str("_changed");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "bad_capture")
        .is_err());
}

#[test]
fn module_scope_keeps_ordinary_facts_local_and_original_stage_order() {
    use crate::compile_to_lean::source_position::SourcePosition;
    let loaded = load_prefix();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(producer),
    )) = &loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("producer")
    };
    let id = producer.statement.fact.fact_id();
    let later = SourcePosition::module_file(&loaded.closure, 1, 1);
    assert!(
        later.visible_fact(id, &loaded.runtime).is_err(),
        "ordinary facts cannot leak from an earlier export"
    );
    let before = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(
        before.visible_fact(id, &loaded.runtime).is_err(),
        "completed runtime cannot publish a future source stage"
    );
    let after = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(after.visible_fact(id, &loaded.runtime).is_ok());
}

#[test]
fn module_prefix_rejects_missing_file_failed_file_and_missing_call_stage() {
    let mut loaded = load_prefix();
    loaded.closure.files.remove(0);
    loaded.closure.target_file = 0;
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "missing_file")
        .is_err());
    let mut loaded = load_prefix();
    loaded.closure.files[0].run.success = false;
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "failed_file")
        .is_err());
    let mut loaded = load_prefix();
    target_call(&mut loaded).type_proofs.clear();
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "missing_stage")
        .is_err());
}

fn load_example(name: &str) -> crate::run_module::LoadedLeanSource {
    let command = parse_launch_command(&[
        "-lean".into(),
        "-strict".into(),
        "-f".into(),
        format!("lean/examples/{name}/statement.lit"),
    ])
    .unwrap();
    let LoadLeanSourceResult::Success(loaded) = load_file_for_lean(command).unwrap() else {
        panic!("original module fixture must verify: {name}")
    };
    loaded
}

#[test]
fn module_transitive_alias_diamond_and_nonexport_preserve_original_closure() {
    for (name, count) in [
        ("module_import_chain", 3),
        ("module_diamond", 4),
        ("module_alias_collision", 5),
        ("module_nonexport_target", 4),
        ("module_mixed_foundations", 2),
    ] {
        let loaded = load_example(name);
        assert_eq!(loaded.closure.files.len(), count, "{name}");
        assert_eq!(loaded.closure.target_file, count - 1);
        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        let output = compiler.compile_module(&loaded.closure, name).unwrap();
        for index in 0..count {
            assert!(output.contains(&format!("namespace source_{index}")));
        }
        assert_eq!(
            output,
            compiler.compile_module(&loaded.closure, name).unwrap()
        );
        if name == "module_mixed_foundations" {
            assert_eq!(
                output
                    .matches("[_functionSemantics : Litex.FunctionSemantics M]")
                    .count(),
                1
            );
            assert!(!output.contains("[_setSemantics : Litex.SetSemantics M]"));
        }
        if name == "module_nonexport_target" {
            assert!(matches!(
                loaded.closure.files[count - 1].source,
                CodeSource::Real(_)
            ));
        }
    }
}

#[test]
fn module_qualified_declaration_rejects_sibling_import_from_original_package() {
    use crate::compile_to_lean::source_position::SourcePosition;
    let loaded = load_example("module_diamond");
    let CodeSource::ImportedExport { global_mod_id, .. } = loaded.closure.files[2].source else {
        panic!("right package")
    };
    let sibling = AtomicName::WithModAndExportFileId {
        global_mod_id,
        export_file_id: 0,
        name: "replay_add_zero".into(),
    };
    let left = SourcePosition::module_file(&loaded.closure, 1, 1);
    assert_eq!(
        left.qualified_file_scope(&sibling, &loaded.runtime)
            .err()
            .unwrap()
            .route,
        "Module/DeclarationVisibility"
    );
}

#[test]
fn module_scope_rejects_changed_source_path_and_future_own_declaration() {
    use crate::compile_to_lean::source_position::SourcePosition;
    let loaded = load_prefix();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(producer),
    )) = &loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("producer")
    };
    let callee = ResolvedTheoremCallee::UserTheorem(producer.statement.clone());
    let name = AtomicName::WithExportFileId {
        export_file_id: 0,
        name: producer.statement.name.clone(),
    };
    let before = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(before
        .user_callee_reference(&name, &callee, &loaded.runtime)
        .is_err());
    let after = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(after
        .user_callee_reference(&name, &callee, &loaded.runtime)
        .is_ok());
    let mut loaded = loaded;
    let CodeSource::RootExport { path, .. } = &mut loaded.closure.files[0].source else {
        panic!("source")
    };
    path.set_file_name("wrong_source.lit");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "wrong_path")
        .is_err());
}

struct ModuleFixture(std::path::PathBuf);
impl ModuleFixture {
    fn new() -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "litex-lean-source-{}-{nonce}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(root.join("lib")).unwrap();
        std::fs::write(
            root.join("litex.config"),
            "[import]\nLibrary = \"./lib\"\n\n[export]\nmain = \"./statement.lit\"\n",
        )
        .unwrap();
        std::fs::write(
            root.join("statement.lit"),
            "by thm Library::facts::replay_add_zero(2) => 2 + 0 = 2\n",
        )
        .unwrap();
        std::fs::write(
            root.join("lib/litex.config"),
            "[export]\nfacts = \"./facts.lit\"\n",
        )
        .unwrap();
        std::fs::write(
            root.join("lib/facts.lit"),
            include_str!("../../../lean/examples/module_export_prefix/base.lit"),
        )
        .unwrap();
        Self(root)
    }
    fn command(&self) -> LaunchCommand {
        parse_launch_command(&[
            "-lean".into(),
            "-strict".into(),
            "-f".into(),
            self.0.join("statement.lit").to_string_lossy().into_owned(),
        ])
        .unwrap()
    }
}
impl Drop for ModuleFixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn module_source_capture_skips_cache_write_and_keeps_all_evidence_after_cache_warmup() {
    let f = ModuleFixture::new();
    let LoadLeanSourceResult::Success(cold) = load_file_for_lean(f.command()).unwrap() else {
        panic!("cold source")
    };
    assert_eq!(cold.closure.files.len(), 2);
    assert!(!f.0.join("lib/__litex_knowledge_base__").exists());
    let warm = crate::run_module::run_file_with_config(LaunchCommand::File {
        path: f.0.join("statement.lit"),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
    .unwrap();
    assert!(warm.run.success);
    assert!(
        f.0.join("lib/__litex_knowledge_base__").exists(),
        "ordinary loading keeps normal writeback"
    );
    let LoadLeanSourceResult::Success(replayed) = load_file_for_lean(f.command()).unwrap() else {
        panic!("source with cache")
    };
    assert_eq!(replayed.closure.files.len(), 2);
    let compiler = super::LitexToLeanCompiler::new(replayed.runtime);
    assert!(compiler
        .compile_module(&replayed.closure, "cached_source")
        .is_ok());
}

#[test]
fn module_loader_preserves_import_cycle_and_failed_original_file_without_artifact() {
    use crate::run_module::LoadLeanSourceFailure;
    let f = ModuleFixture::new();
    std::fs::write(f.0.join("lib/facts.lit"), "2 = 3\n").unwrap();
    assert!(matches!(
        load_file_for_lean(f.command()).unwrap(),
        LoadLeanSourceResult::Failed(LoadLeanSourceFailure::Import { .. })
    ));
    let f = ModuleFixture::new();
    std::fs::write(f.0.join("statement.lit"), "2 = 3\n").unwrap();
    let LoadLeanSourceResult::Failed(LoadLeanSourceFailure::File(failure)) =
        load_file_for_lean(f.command()).unwrap()
    else {
        panic!("original target failure")
    };
    assert!(!failure.run.success);
    assert!(failure
        .run
        .statement_results
        .iter()
        .any(ExecStmtResult::is_failed));
    let f = ModuleFixture::new();
    std::fs::write(
        f.0.join("lib/litex.config"),
        "[import]\nRoot = \"..\"\n\n[export]\nfacts = \"./facts.lit\"\n",
    )
    .unwrap();
    assert!(matches!(
        load_file_for_lean(f.command()).unwrap(),
        LoadLeanSourceResult::Failed(LoadLeanSourceFailure::Import { .. })
    ));
}

#[test]
fn module_cli_returns_only_complete_artifact_or_original_verification_failure() {
    let f = ModuleFixture::new();
    let compiled = crate::run::run_compile_to_lean::run_compile_to_lean(f.command()).unwrap();
    assert!(compiled.success);
    assert!(compiled.source.starts_with("import Litex\n"));
    assert!(compiled.source.contains("namespace source_1"));
    std::fs::write(f.0.join("statement.lit"), "2 = 3\n").unwrap();
    let failed = crate::run::run_compile_to_lean::run_compile_to_lean(f.command()).unwrap();
    assert!(!failed.success);
    assert!(failed.source.contains("phase=verify:"));
    assert!(!failed.source.contains("import Litex"));
    std::fs::write(f.0.join("lib/facts.lit"), "2 = 3\n").unwrap();
    let error = crate::run::run_compile_to_lean::run_compile_to_lean(f.command())
        .err()
        .unwrap();
    assert!(error.to_string().contains("phase=verify:"));
}
