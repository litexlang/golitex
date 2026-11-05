use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult};
use crate::runtime::CodeSource;

fn load_prefix() -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load("module_export_prefix")
}

#[test]
fn module_loader_retains_actual_export_prefix_and_original_qualified_callee() {
    let (loaded, _project_1) = load_prefix();
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
    let (loaded, _project_2) = load_prefix();
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
        let (mut loaded, _project_3) = load_prefix();
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
    let (mut loaded, _project_4) = load_prefix();
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
    let (loaded, _project_5) = load_prefix();
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
    let (mut loaded, _project_6) = load_prefix();
    loaded.closure.files.remove(0);
    loaded.closure.target_file = 0;
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "missing_file")
        .is_err());
    let (mut loaded, _project_7) = load_prefix();
    loaded.closure.files[0].run.success = false;
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "failed_file")
        .is_err());
    let (mut loaded, _project_8) = load_prefix();
    target_call(&mut loaded).type_proofs.clear();
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    assert!(compiler
        .compile_module(&loaded.closure, "missing_stage")
        .is_err());
}

fn load_example(name: &str) -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load(name)
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
        let (loaded, _project_9) = load_example(name);
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
    let (loaded, _project_10) = load_example("module_diamond");
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
    let (loaded, _project_11) = load_prefix();
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
            r#"thm replay_add_zero:
    ? forall x R:
        x + 0 = x
    x + 0 = x
"#,
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
fn foreign_arbitrary_parameters_inherit_the_original_generic_context() {
    let fixture = ModuleFixture::new();
    std::fs::write(fixture.0.join("lib/facts.lit"), "have a R\n").unwrap();
    std::fs::write(
        fixture.0.join("statement.lit"),
        "Library::facts::a = Library::facts::a\n",
    )
    .unwrap();
    let LoadLeanSourceResult::Success(loaded) = load_file_for_lean(fixture.command()).unwrap()
    else {
        panic!("source itself verifies");
    };
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let output = compiler
        .compile_module(&loaded.closure, "ForeignParameter")
        .unwrap();
    let target = output.split("namespace source_1").nth(1).unwrap();
    assert!(target.contains("Litex.Representation M _Host_i"));
    assert!(target.contains("Litex.Obj (M := M) _Host_i"));
    assert!(target.contains("Litex.In _value_i"));
}

#[test]
fn cross_file_parameters_keep_order_source_ids_and_stage_boundaries() {
    use crate::compile_to_lean::source_position::SourcePosition;
    let (loaded, _project_12) = super::module_fixtures::load("module_cross_file_parameters");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let original = SourcePosition::module_file(
        &loaded.closure,
        0,
        loaded.closure.files[0].run.statement_results.len(),
    );
    let target = SourcePosition::module_file(&loaded.closure, 1, 0);
    assert_eq!(target.context_parameters(), original.context_parameters());
    assert_eq!(
        target
            .context_parameters()
            .iter()
            .map(|(p, _, _)| p.name.as_str())
            .collect::<Vec<_>>(),
        ["a", "A", "f"]
    );
    for (bound, _, fact_id) in target.context_parameters() {
        let object = Obj::Identifier(original.parameter_identifier(bound).unwrap());
        assert_eq!(
            compiler.compile_object_reference(&object, &target).unwrap(),
            format!("_value_i{}", bound.id.value())
        );
        let (fact, reference) = target.visible_fact(fact_id, &compiler.runtime).unwrap();
        assert_eq!(fact.fact_id(), fact_id);
        assert_eq!(reference, format!("h_{}", fact_id.value()));
        assert!(compiler
            .compile_object_reference(&object, &SourcePosition::module_file(&loaded.closure, 0, 0))
            .is_err());
    }
    compiler
        .compile_module(&loaded.closure, "InheritedContext")
        .unwrap();
}

#[test]
fn inherited_parameters_do_not_publish_unrelated_foreign_facts() {
    use crate::compile_to_lean::source_position::SourcePosition;
    let fixture = ModuleFixture::new();
    std::fs::write(fixture.0.join("lib/facts.lit"), "have a R\na = a\n").unwrap();
    std::fs::write(
        fixture.0.join("statement.lit"),
        "Library::facts::a = Library::facts::a\n",
    )
    .unwrap();
    let LoadLeanSourceResult::Success(loaded) = load_file_for_lean(fixture.command()).unwrap()
    else {
        panic!("source verifies")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        &loaded.closure.files[0].run.statement_results[1]
    else {
        panic!("original fact")
    };
    let id = p.store_and_infer_result.primary_fact_id();
    let target = SourcePosition::module_file(&loaded.closure, 1, 0);
    assert!(target.visible_fact(id, &loaded.runtime).is_err());
}

#[test]
fn inherited_parameter_requires_its_unchanged_source_declaration_capture() {
    let fixture = ModuleFixture::new();
    std::fs::write(fixture.0.join("lib/facts.lit"), "have a R\n").unwrap();
    std::fs::write(
        fixture.0.join("statement.lit"),
        "Library::facts::a = Library::facts::a\n",
    )
    .unwrap();
    let LoadLeanSourceResult::Success(mut loaded) = load_file_for_lean(fixture.command()).unwrap()
    else {
        panic!("source verifies")
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult::Success(
            p,
        )),
    )) = &mut loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("original have")
    };
    p.statement.param_def.groups[0].params[0].name = "another".into();
    assert!(super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "AlteredCapture")
        .is_err());
}

#[test]
fn imported_parameter_aliases_keep_distinct_ids_and_producer_argument_prefixes() {
    use crate::compile_to_lean::source_position::SourcePosition;
    let (loaded, _project_13) = super::module_fixtures::load("module_imported_parameters");
    let original = SourcePosition::module_file(
        &loaded.closure,
        0,
        loaded.closure.files[0].run.statement_results.len(),
    );
    let target = SourcePosition::module_file(
        &loaded.closure,
        loaded.closure.target_file,
        loaded.closure.files[loaded.closure.target_file]
            .run
            .statement_results
            .len(),
    );
    let parameters = target.context_parameters();
    assert_eq!(
        parameters
            .iter()
            .map(|(p, _, _)| p.name.as_str())
            .collect::<Vec<_>>(),
        ["a", "A", "f", "element", "a"]
    );
    assert_ne!(parameters[0].0.id, parameters[4].0.id);
    let application = target.declaration_reference("probe", &original).unwrap();
    for (parameter, _, _) in &parameters[..3] {
        assert!(application.contains(&format!("_value_i{}", parameter.id.value())));
    }
    for (parameter, _, _) in &parameters[3..] {
        assert!(!application.contains(&format!("_value_i{}", parameter.id.value())));
    }
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    compiler
        .compile_module(&loaded.closure, "ImportedParameterContext")
        .unwrap();
}

#[test]
fn inherited_parameters_do_not_implicitly_inherit_foreign_trust_assumptions() {
    let fixture = ModuleFixture::new();
    std::fs::write(fixture.0.join("lib/facts.lit"), "have a R\ntrust:\n    a > 0\nthm conditional:\n    ? forall x R:\n        a > 0\n    a > 0\n").unwrap();
    std::fs::write(fixture.0.join("statement.lit"), "release obj def Library::facts::a\nby thm Library::facts::conditional(2) => Library::facts::a > 0\n").unwrap();
    let command = parse_launch_command(&[
        "-lean".into(),
        "-f".into(),
        fixture
            .0
            .join("statement.lit")
            .to_string_lossy()
            .into_owned(),
    ])
    .unwrap();
    let LoadLeanSourceResult::Success(loaded) = load_file_for_lean(command).unwrap() else {
        panic!("conditional source verifies")
    };
    let error = super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "ForeignAssumption")
        .unwrap_err();
    assert!(
        error
            .route
            .starts_with("Module/DeclarationContextArguments"),
        "{error:?}"
    );
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
