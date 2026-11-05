use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult, LoadedLeanSource};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{EqualitySearchProofByObjectDefinition, by_identifier::EqualitySearchProofByIdentifierObjectDefinition};

fn load_tracer() -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load("module_additive_constant")
}

#[test]
fn module_arbitrary_parameters_preserve_their_generic_hosts_and_source_facts() {
    for name in [
        "module_real_parameter",
        "module_set_kind_parameters",
        "module_function_parameter",
        "module_coordinate_parameters",
        "module_derivative_parameter",
    ] {
        let (loaded, _project_1) = load_example(name);
        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        let output = compiler
            .compile_module(&loaded.closure, "ArbitraryRealParameter")
            .unwrap();
        assert!(output.contains("Litex.Representation M _Host_i"));
        assert!(output.contains("Litex.Obj (M := M) _Host_i"));
        assert_eq!(
            output,
            compiler
                .compile_module(&loaded.closure, "ArbitraryRealParameter")
                .unwrap()
        );
    }
}

#[test]
fn module_arbitrary_parameter_keeps_its_original_introduction_stage() {
    let (loaded, _project_2) = load_example("module_real_parameter");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let object = Obj::Identifier(IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "a".into(),
    });
    let before = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(compiler.compile_object_reference(&object, &before).is_err());
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(compiler
        .compile_object_reference(&object, &after)
        .unwrap()
        .starts_with("_value_i"));
}

#[test]
fn module_arbitrary_parameter_rejects_another_source_declaration_capture() {
    for name in ["module_real_parameter", "module_derivative_parameter"] {
        let (mut loaded, _project_3) = load_example(name);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(p),
            ),
        )) = &mut loaded.closure.files[0].run.statement_results[0]
        else {
            panic!()
        };
        p.statement.param_def.groups[0].params[0].name = "unrelated".into();
        assert!(!compiles(loaded));
    }
}

#[test]
fn module_identifier_replays_original_let_publication_and_selected_definition_residual() {
    let (loaded, _project_4) = load_tracer();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(declaration)),
    )) = &loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("original let")
    };
    let site = SourcePosition::module_file(&loaded.closure, 0, 1);
    let fact = site
        .source_fact(declaration.stored_fact_ids[0], &loaded.runtime)
        .unwrap();
    assert!(matches!(
        fact,
        Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            left: Obj::Identifier(IdentifierObj::WithExportFileId {
                export_file_id: 0,
                ..
            }),
            ..
        }))
    ));
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(target)) =
        &loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("target")
    };
    let VerifyFactResult::Equality(target) = &target.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(target) = target.as_ref() else {
        panic!("verified equality")
    };
    assert!(matches!(
        &target.searched_proof,
        EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByIdentifier(
                EqualitySearchProofByIdentifierObjectDefinition::LetObj(_)
            )
        )
    ));
    let output = super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "exported_two")
        .unwrap();
    assert!(output.contains("source_0._object_i"));
    assert!(output.contains("source_0.h_"));
}

fn load_example(name: &str) -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load(name)
}
#[test]
fn module_identifier_replays_typed_reverse_nested_imported_and_released_definitions() {
    for name in [
        "module_typed_constant",
        "module_identifier_chain",
        "module_identifier_import",
        "module_identifier_local_binder",
        "module_identifier_release",
        "module_identifier_guarded_value",
        "module_identifier_alias_collision",
    ] {
        let (loaded, _project_5) = load_example(name);
        let output = super::LitexToLeanCompiler::new(loaded.runtime)
            .compile_module(&loaded.closure, name)
            .unwrap();
        assert!(output.contains("source_0._object_i"), "{name}");
        assert!(output.contains("source_0.h_"), "{name}");
    }
}

fn compiles(loaded: LoadedLeanSource) -> bool {
    super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "identifier_control")
        .is_ok()
}
fn let_mut(loaded: &mut LoadedLeanSource) -> &mut ExecLetObjStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &mut loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("original let")
    };
    p
}
fn let_fold_mut(loaded: &mut LoadedLeanSource) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_identifier::by_let_obj::ByLetObjObjectDefinitionProof{
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        &mut loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("target")
    };
    let VerifyFactResult::Equality(p) = &mut p.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(p) = p.as_mut() else {
        panic!("success")
    };
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByIdentifier(
            EqualitySearchProofByIdentifierObjectDefinition::LetObj(p),
        ),
    ) = &mut p.searched_proof
    else {
        panic!("selected identifier route")
    };
    p
}
#[test]
fn module_identifier_requires_original_binding_capture_and_store_subject() {
    let (mut loaded, _project_6) = load_tracer();
    let changed_id = loaded.runtime.global_ids.allocate_identifier_id();
    let_mut(&mut loaded).statement.name.id = changed_id;
    assert!(
        !compiles(loaded),
        "a qualified spelling cannot hide another bound ID"
    );
    let (mut loaded, _project_7) = load_tracer();
    let_mut(&mut loaded).stored_fact_ids.clear();
    assert!(!compiles(loaded));
    let (mut loaded, _project_8) = load_tracer();
    let id = let_mut(&mut loaded).stored_fact_ids[0];
    let fact = loaded.runtime.global_module_manager.root_exports[0]
        .exec_env
        .facts
        .facts_by_id
        .get_mut(&id)
        .unwrap();
    let Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
        left: Obj::Identifier(IdentifierObj::WithExportFileId { export_file_id, .. }),
        ..
    })) = fact
    else {
        panic!("qualified subject")
    };
    *export_file_id = 1;
    assert!(!compiles(loaded));
}
#[test]
fn module_identifier_rejects_missing_future_producer_and_foreign_ordinary_fact() {
    let (loaded, _project_9) = load_tracer();
    let object = Obj::Identifier(IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "two".into(),
    });
    let before = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(before
        .with_visible_alias(&object, &loaded.runtime, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_none());
    let after = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(after
        .with_visible_alias(&object, &loaded.runtime, &mut |_, _, _, _| Ok(()))
        .unwrap()
        .is_some());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("let")
    };
    let target = SourcePosition::module_file(&loaded.closure, 1, 1);
    assert!(target
        .visible_fact(p.stored_fact_ids[0], &loaded.runtime)
        .is_err());
    let mut loaded = loaded;
    loaded.closure.files[0].run.statement_results.clear();
    assert!(!compiles(loaded));
}
#[test]
fn module_identifier_keeps_recorded_expansion_and_residual_endpoint() {
    let (mut loaded, _project_10) = load_tracer();
    let_fold_mut(&mut loaded).expanded_rhs = Obj::StandardSet(StandardSet::R);
    assert!(!compiles(loaded));
    let (mut loaded, _project_11) = load_tracer();
    let p = let_fold_mut(&mut loaded);
    let VerifyFactResult::Equality(child) = &mut p.residual_equal else {
        panic!("child")
    };
    let VerifyEqualityResult::Success(child) = child.as_mut() else {
        panic!("child success")
    };
    child.fact.right = child.fact.left.clone();
    assert!(!compiles(loaded));
}
#[test]
fn module_identifier_release_borrows_only_original_constructor_after_publication() {
    let (loaded, _project_12) = load_example("module_identifier_release");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("let")
    };
    let before = SourcePosition::module_file(&loaded.closure, 1, 0);
    assert!(before
        .with_released_definition_wd(&p.statement.value, &loaded.runtime, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    let after = SourcePosition::module_file(&loaded.closure, 1, 1);
    let VerifyObjWellDefinedResult::Success(original) = &p.value_well_defined else {
        panic!("original WD")
    };
    assert!(after
        .with_released_definition_wd(&p.statement.value, &loaded.runtime, &mut |wd, _| Ok(
            std::ptr::eq(wd, original)
        ))
        .unwrap()
        .unwrap());
    assert!(after
        .visible_fact(p.stored_fact_ids[0], &loaded.runtime)
        .is_err());
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::ObjDef(
        crate::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult::Success(release),
    )) = &loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("release")
    };
    assert!(after
        .visible_fact(
            release.store_and_infer[0].primary_fact_id(),
            &loaded.runtime
        )
        .is_ok());
}

#[test]
fn module_identifier_guard_constructor_keeps_original_fact_namespace() {
    let (loaded, _project_13) = load_example("module_identifier_guarded_value");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        &loaded.closure.files[0].run.statement_results[2]
    else {
        panic!("original nonzero fact")
    };
    let id = crate::compile_to_lean::helper::source_subject(&p.verify_result)
        .unwrap()
        .fact_id();
    let original = SourcePosition::module_file(&loaded.closure, 0, 3);
    assert!(original
        .visible_fact(id, &loaded.runtime)
        .unwrap()
        .1
        .contains("source_0.h_"));
    let caller = SourcePosition::module_file(&loaded.closure, 1, 1);
    assert!(caller.visible_fact(id, &loaded.runtime).is_err());
}

#[test]
fn module_identifier_package_bindings_keep_identity_and_visibility() {
    use crate::runtime::CodeSource;
    let (loaded, _project_14) = load_example("module_identifier_alias_collision");
    let CodeSource::ImportedExport {
        global_mod_id: left,
        ..
    } = loaded.closure.files[0].source
    else {
        panic!("left")
    };
    let CodeSource::ImportedExport {
        global_mod_id: right,
        ..
    } = loaded.closure.files[1].source
    else {
        panic!("right")
    };
    let left_name = IdentifierObj::WithModAndExportFileId {
        global_mod_id: left,
        export_file_id: 0,
        name: "value".into(),
    };
    let right_name = IdentifierObj::WithModAndExportFileId {
        global_mod_id: right,
        export_file_id: 0,
        name: "value".into(),
    };
    let target = SourcePosition::module_file(&loaded.closure, 2, 0);
    let (left_bound, _, _) = target
        .qualified_identifier_scope(&left_name, &loaded.runtime)
        .unwrap();
    let (right_bound, _, _) = target
        .qualified_identifier_scope(&right_name, &loaded.runtime)
        .unwrap();
    assert_ne!(left_bound.id, right_bound.id);
    let left_scope = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(left_scope
        .qualified_identifier_scope(&right_name, &loaded.runtime)
        .is_err());
    assert!(
        target
            .with_visible_alias(
                &Obj::Identifier(left_name),
                &loaded.runtime,
                &mut |bound, _, _, _| Ok(bound.id)
            )
            .unwrap()
            == Some(left_bound.id)
    );
    assert!(
        target
            .with_visible_alias(
                &Obj::Identifier(right_name),
                &loaded.runtime,
                &mut |bound, _, _, _| Ok(bound.id)
            )
            .unwrap()
            == Some(right_bound.id)
    );
}
#[test]
fn module_identifier_release_keeps_original_capture_and_store_count() {
    use crate::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult;
    let (mut loaded, _project_15) = load_example("module_identifier_release");
    let changed_id = loaded.runtime.global_ids.allocate_identifier_id();
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::ObjDef(
        ExecReleaseObjDefStmtResult::Success(p),
    )) = &mut loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("release")
    };
    let crate::exec_env::StoredIdentifierDefinition::LetObj((_, statement)) = &mut p.looked_up
    else {
        panic!("let capture")
    };
    std::rc::Rc::make_mut(statement).name.id = changed_id;
    assert!(!compiles(loaded));
    let (mut loaded, _project_16) = load_example("module_identifier_release");
    let ExecStmtResult::ReleaseAndExpand(crate::execute::ExecReleaseAndExpandStmtResult::ObjDef(
        ExecReleaseObjDefStmtResult::Success(p),
    )) = &mut loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("release")
    };
    p.store_and_infer.clear();
    assert!(!compiles(loaded));
}
#[test]
fn module_identifier_does_not_reinterpret_an_actual_typed_definition_route_as_let() {
    let (mut typed, _project_17) = load_example("module_typed_constant");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        typed.closure.files[1].run.statement_results.pop().unwrap()
    else {
        panic!("typed target")
    };
    let VerifyFactResult::Equality(p) = p.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(p) = *p else {
        panic!("success")
    };
    assert!(matches!(
        p.searched_proof,
        EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByIdentifier(
                EqualitySearchProofByIdentifierObjectDefinition::HaveObjEqual(_)
            )
        )
    ));
    let recorded = p.searched_proof;
    let (mut loaded, _project_18) = load_tracer();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        &mut loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("let target")
    };
    let VerifyFactResult::Equality(p) = &mut p.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(p) = p.as_mut() else {
        panic!("success")
    };
    p.searched_proof = recorded;
    let error = super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "wrong_definition_family")
        .unwrap_err();
    assert_eq!(error.route, "IdentifierDefinition/ProducerFamily");
}
