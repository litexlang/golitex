use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult, ExecReleaseAndExpandStmtResult};
use crate::execute::execute_release_obj_def_stmt::ExecReleaseObjDefStmtResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    EqualitySearchProofByObjectDefinition,
    by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
        normalize_function_body::{AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof, FunctionBodySourceProof}},
};
use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult, LoadedLeanSource};

fn load(name: &str) -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load(name)
}
fn tracer() -> super::module_fixtures::LoadedProject {
    load("module_function_definition")
}

#[test]
fn exported_selected_functions_replay_original_unique_witnesses_and_release() {
    let (loaded, _project_1) = load("module_selected_identity");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let output = compiler
        .compile_module(&loaded.closure, "ExportedSelectedIdentity")
        .unwrap();
    assert!(output.contains("Litex.selectedFn"));
    assert!(output.contains("source_0._object_i"));
    assert_eq!(
        output,
        compiler
            .compile_module(&loaded.closure, "ExportedSelectedIdentity")
            .unwrap()
    );
}

#[test]
fn exported_selected_release_requires_exact_capture_order_and_all_stores() {
    use crate::execute::execute_release_obj_def_stmt::ReleaseObjDefByKind;
    for mutation in 0..4 {
        let (mut loaded, _project_2) = load("module_selected_identity");
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ObjDef(
            ExecReleaseObjDefStmtResult::Success(p),
        )) = &mut loaded.closure.files[1].run.statement_results[1]
        else {
            panic!()
        };
        match mutation {
            0 => {
                let ReleaseObjDefByKind::HaveFnByForallExistUnique {
                    property_forall,
                    uniqueness_forall,
                    ..
                } = &mut p.released
                else {
                    panic!()
                };
                std::mem::swap(property_forall, uniqueness_forall);
            }
            1 => {
                p.store_and_infer.pop();
            }
            2 => {
                let crate::exec_env::StoredIdentifierDefinition::HaveFnByForallExistUnique((
                    key,
                    _,
                )) = &mut p.looked_up
                else {
                    panic!()
                };
                *key = "unrelated".into();
            }
            _ => {
                let ReleaseObjDefByKind::HaveFnByForallExistUnique {
                    uniqueness_forall, ..
                } = &mut p.released
                else {
                    panic!()
                };
                let Fact::ForallFact(f) = uniqueness_forall else {
                    panic!()
                };
                let input = Obj::Identifier(IdentifierObj::from_bound_name(
                    &f.typed_parameters.groups[0].params[0],
                ));
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut f.then_facts[0]
                else {
                    panic!()
                };
                eq.left = input;
            }
        }
        assert!(!compiles(loaded));
    }
}

#[test]
fn qualified_selected_identifier_requires_the_completed_original_declaration() {
    let (mut loaded, _project_3) = load("module_selected_identity");
    let identifier = IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "selected".into(),
    };
    let before = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(before
        .visible_selected_identifier(&identifier, &loaded.runtime)
        .is_err());
    let after = SourcePosition {
        before: 2,
        ..before
    };
    assert!(after
        .visible_selected_identifier(&identifier, &loaded.runtime)
        .is_ok());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
        crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
    )) = &mut loaded.closure.files[0].run.statement_results[1]
    else {
        panic!()
    };
    p.statement.name.name = "unrelated".into();
    let caller = SourcePosition::module_file(&loaded.closure, 1, 0);
    assert!(caller
        .visible_selected_identifier(&identifier, &loaded.runtime)
        .is_err());
    assert!(!compiles(loaded));
}

#[test]
fn exported_recursive_functions_replay_restricted_self_publication_release_and_calls() {
    for name in [
        "module_recursive_constant",
        "module_recursive_guarded",
        "module_recursive_function_values",
    ] {
        let (loaded, _project_4) = load(name);
        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        let output = compiler
            .compile_module(&loaded.closure, "ExportedRecursiveConstant")
            .unwrap();
        assert!(output.contains("source_0._object_i"));
        assert!(output.contains("source_0.h_"));
        assert_eq!(
            output,
            compiler
                .compile_module(&loaded.closure, "ExportedRecursiveConstant")
                .unwrap()
        );
    }
}

#[test]
fn qualified_recursive_call_dependency_uses_the_original_constructor_tree() {
    let (loaded, _project_5) = load("module_recursive_constant");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let statement = &loaded.closure.files[0].run.statement_results[0];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        crate::execute::ExecHaveFnByInducStmtResult::Success(proof),
    )) = statement
    else {
        panic!()
    };
    let root = SourcePosition::module_file(&loaded.closure, 0, 0);
    let declaration = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 0);
    let function =
        SourcePosition::new(Some(&declaration), SourceOwner::RecursiveFunction(proof), 8);
    let branch = SourcePosition::new(
        Some(&function),
        SourceOwner::RecursiveCase(&proof.case_checks.cases[1]),
        2,
    );
    let crate::ast::stmt::HaveFnByInducCaseBody::EqualTo(body) = &proof.statement.cases[1].body
    else {
        panic!()
    };
    assert!(compiler
        .recursive_body_uses_self(body, proof, &branch)
        .unwrap());
    assert!(!compiler
        .recursive_body_uses_self(&super::number_object("1"), proof, &branch)
        .unwrap());
    assert!(compiler
        .recursive_identifier_is_self(
            &IdentifierObj::WithExportFileId {
                export_file_id: 0,
                name: "repeat_one".into()
            },
            proof,
            &branch
        )
        .unwrap());
}

#[test]
fn qualified_recursive_self_is_local_until_the_public_declaration_completes() {
    let (loaded, _project_6) = load("module_recursive_constant");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let statement = &loaded.closure.files[0].run.statement_results[0];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        crate::execute::ExecHaveFnByInducStmtResult::Success(proof),
    )) = statement
    else {
        panic!()
    };
    let root = SourcePosition::module_file(&loaded.closure, 0, 0);
    let declaration = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 0);
    let identifier = IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "repeat_one".into(),
    };
    let object = Obj::Identifier(identifier.clone());
    for stage in [6, 7] {
        let scope = SourcePosition::new(
            Some(&declaration),
            SourceOwner::RecursiveFunction(proof),
            stage,
        );
        let term = compiler.compile_object_reference(&object, &scope);
        assert_eq!(
            scope
                .visible_recursive_self_identifier(&identifier, &compiler.runtime)
                .is_ok(),
            stage == 7
        );
        if stage == 6 {
            assert!(term.is_err());
        } else {
            assert_eq!(
                term.unwrap(),
                format!("_object_i{}", proof.statement.name.id.value())
            );
        }
    }
    assert!(root
        .visible_recursive_identifier(&identifier, &compiler.runtime)
        .is_err());
    let complete = SourcePosition { before: 1, ..root };
    assert!(complete
        .visible_recursive_self_identifier(&identifier, &compiler.runtime)
        .is_err());
    let term = compiler
        .compile_object_reference(&object, &complete)
        .unwrap();
    assert!(term.contains("source_0._object_i"));
}

#[test]
fn exported_recursive_release_requires_capture_order_and_complete_publications() {
    use crate::execute::execute_release_obj_def_stmt::ReleaseObjDefByKind;
    for mutation in 0..3 {
        let (mut loaded, _project_7) = load("module_recursive_constant");
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ObjDef(
            ExecReleaseObjDefStmtResult::Success(p),
        )) = &mut loaded.closure.files[1].run.statement_results[1]
        else {
            panic!()
        };
        match mutation {
            0 => {
                let ReleaseObjDefByKind::HaveFnByInduc { case_foralls, .. } = &mut p.released
                else {
                    panic!()
                };
                case_foralls.swap(0, 1);
            }
            1 => {
                p.store_and_infer.pop();
            }
            _ => {
                let crate::exec_env::StoredIdentifierDefinition::HaveFnByInduc((key, _)) =
                    &mut p.looked_up
                else {
                    panic!()
                };
                *key = "unrelated".into();
            }
        }
        assert!(!compiles(loaded));
    }
}

#[test]
fn qualified_recursive_identifiers_require_the_exact_original_definition() {
    let (mut loaded, _project_8) = load("module_recursive_constant");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        crate::execute::ExecHaveFnByInducStmtResult::Success(proof),
    )) = &mut loaded.closure.files[0].run.statement_results[0]
    else {
        panic!()
    };
    proof.statement.name.name = "unrelated".into();
    let caller = SourcePosition::module_file(&loaded.closure, 1, 0);
    let identifier = IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "repeat_one".into(),
    };
    assert!(caller
        .visible_recursive_identifier(&identifier, &loaded.runtime)
        .is_err());
    assert!(!compiles(loaded));
}

#[test]
fn exported_piecewise_functions_replay_definition_release_and_guarded_calls() {
    let (loaded, _project_9) = load("module_piecewise_reciprocal");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let first = compiler
        .compile_module(&loaded.closure, "ExportedReciprocal")
        .unwrap();
    assert!(first.contains("Litex.piecewiseFn"));
    assert!(first.contains("source_0._object_i"));
    assert!(first.contains("source_0.h_"));
    assert_eq!(
        first,
        compiler
            .compile_module(&loaded.closure, "ExportedReciprocal")
            .unwrap()
    );
}

#[test]
fn exported_piecewise_identifier_obeys_its_original_constructor_stage() {
    let (loaded, _project_10) = load("module_piecewise_reciprocal");
    let name = IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "reciprocal".into(),
    };
    let before = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(before
        .visible_piecewise_identifier(&name, &loaded.runtime)
        .is_err());
    let statement = &loaded.closure.files[0].run.statement_results[0];
    for stage in [4, 5] {
        let site = SourcePosition::new(Some(&before), SourceOwner::Statement(statement), stage);
        assert_eq!(
            site.visible_piecewise_identifier(&name, &loaded.runtime)
                .is_ok(),
            stage == 5
        );
    }
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert_eq!(
        after
            .visible_piecewise_identifier(&name, &loaded.runtime)
            .unwrap()
            .1
            .module_file_number(),
        Some(0)
    );
}

#[test]
fn exported_piecewise_identifier_requires_the_exact_captured_definition() {
    let (mut loaded, _project_11) = load("module_piecewise_reciprocal");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
        crate::execute::ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
    )) = &mut loaded.closure.files[0].run.statement_results[0]
    else {
        panic!()
    };
    p.statement.equal_tos[1] = super::number_object("7");
    let caller = SourcePosition::module_file(&loaded.closure, 1, 0);
    let name = IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "reciprocal".into(),
    };
    assert!(caller
        .visible_piecewise_identifier(&name, &loaded.runtime)
        .is_err());
    assert!(!compiles(loaded));
}

#[test]
fn exported_piecewise_release_retains_original_order_capture_and_all_stores() {
    use crate::execute::execute_release_obj_def_stmt::ReleaseObjDefByKind;
    for mutation in 0..3 {
        let (mut loaded, _project_12) = load("module_piecewise_reciprocal");
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ObjDef(
            ExecReleaseObjDefStmtResult::Success(p),
        )) = &mut loaded.closure.files[1].run.statement_results[1]
        else {
            panic!()
        };
        match mutation {
            0 => {
                let ReleaseObjDefByKind::HaveFnEqualCaseByCase { case_foralls, .. } =
                    &mut p.released
                else {
                    panic!()
                };
                case_foralls.swap(0, 1);
            }
            1 => {
                p.store_and_infer.pop();
            }
            _ => {
                let crate::exec_env::StoredIdentifierDefinition::HaveFnEqualCaseByCase((key, _)) =
                    &mut p.looked_up
                else {
                    panic!()
                };
                *key = "unrelated".into();
            }
        }
        assert!(!compiles(loaded));
    }
}
fn definition(statement: &ExecStmtResult) -> &ExecHaveFnEqualStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(p),
    )) = statement
    else {
        panic!("original HaveFnEqual")
    };
    p
}
fn definition_mut(loaded: &mut LoadedLeanSource) -> &mut ExecHaveFnEqualStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(p),
    )) = &mut loaded.closure.files[0].run.statement_results[0]
    else {
        panic!("original HaveFnEqual")
    };
    p
}
fn expansion(loaded: &mut LoadedLeanSource) -> &mut AnonymousFunctionBodyExpansionProof {
    let target = super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut loaded.closure.files[1].run.statement_results[1])
            .verify_result,
    );
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(p),
        ),
    ) = &mut target.searched_proof
    else {
        panic!("actual function normalization route")
    };
    let FunctionBodyExpansionProof::Anonymous(p) = &mut p.normalization.expansions[0] else {
        panic!("actual anonymous expansion")
    };
    p
}
fn compiles(loaded: LoadedLeanSource) -> bool {
    super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "module_function_control")
        .is_ok()
}

#[test]
fn module_function_replays_actual_declarations_calls_guards_imports_and_bindings() {
    for name in [
        "module_function_definition",
        "module_function_local_binder",
        "module_function_guarded",
        "module_function_import",
        "module_function_alias_collision",
    ] {
        let (loaded, _project_13) = load(name);
        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        let output = compiler.compile_module(&loaded.closure, name).unwrap();
        assert_eq!(
            output,
            compiler.compile_module(&loaded.closure, name).unwrap()
        );
        assert!(output.contains("source_0._object_i"), "{name}");
    }
}

#[test]
fn module_function_constructor_reuses_original_wd_only_after_both_formation_stages() {
    let (loaded, _project_14) = tracer();
    let statement = &loaded.closure.files[0].run.statement_results[0];
    let original = definition(statement);
    let completed = SourcePosition::module_file(&loaded.closure, 0, 1);
    let Fact::AtomicFact(AtomicFact::InFact(member)) = completed
        .source_fact(
            original.store_and_infer_result.membership_fact_id,
            &loaded.runtime,
        )
        .unwrap()
    else {
        panic!("membership")
    };
    assert!(matches!(
        member.element,
        Obj::Identifier(IdentifierObj::WithExportFileId { .. })
    ));
    let root = SourcePosition::module_file(&loaded.closure, 0, 0);
    for stage in [0, 1, 2] {
        let site = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), stage);
        let reused = site
            .with_visible_alias(
                &member.element,
                &loaded.runtime,
                &mut |bound, value, wd, producer| {
                    assert_eq!(bound, &original.statement.name);
                    assert!(std::ptr::eq(wd, &original.anonymous_fn_well_defined));
                    assert_eq!(
                        value,
                        &Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                            original.statement.equal_to_anonymous_fn.clone()
                        ))
                    );
                    assert_eq!(producer.before, 0);
                    Ok(())
                },
            )
            .unwrap();
        assert_eq!(reused.is_some(), stage == 2);
    }
}

#[test]
fn module_function_keeps_original_binding_capture_and_ordered_store_identity() {
    let (mut loaded, _project_15) = tracer();
    definition_mut(&mut loaded).statement.name.id =
        loaded.runtime.global_ids.allocate_identifier_id();
    assert!(!compiles(loaded));
    let (mut loaded, _project_16) = tracer();
    definition_mut(&mut loaded)
        .store_and_infer_result
        .stored_fact_ids
        .clear();
    assert!(!compiles(loaded));
    let (mut loaded, _project_17) = tracer();
    let p = definition_mut(&mut loaded);
    p.store_and_infer_result.membership_fact_id = p.store_and_infer_result.defining_equal_fact_id;
    assert!(!compiles(loaded));
}

#[test]
fn module_function_requires_original_anonymous_and_signature_formation_subjects() {
    for signature in [false, true] {
        let (mut loaded, _project_18) = tracer();
        let p = definition_mut(&mut loaded);
        let wd = if signature {
            &mut p.fn_set_well_defined
        } else {
            &mut p.anonymous_fn_well_defined
        };
        let VerifyObjWellDefinedResult::Success(wd) = wd else {
            panic!("original WD")
        };
        super::replace_wd_subject(wd, super::number_object("7"));
        assert!(!compiles(loaded));
    }
}

#[test]
fn module_function_requires_original_source_result_and_prior_file() {
    let (mut loaded, _project_19) = tracer();
    loaded.closure.files[0].run.statement_results.clear();
    assert!(!compiles(loaded));
    let (mut loaded, _project_20) = tracer();
    loaded.closure.files.swap(0, 1);
    assert!(!compiles(loaded));
}

#[test]
fn module_function_release_publishes_local_facts_without_exposing_original_fact_ids() {
    let (loaded, _project_21) = tracer();
    let original = definition(&loaded.closure.files[0].run.statement_results[0]);
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ObjDef(
        ExecReleaseObjDefStmtResult::Success(released),
    )) = &loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("actual release")
    };
    let before = SourcePosition::module_file(&loaded.closure, 1, 0);
    let after = SourcePosition::module_file(&loaded.closure, 1, 1);
    for store in &released.store_and_infer {
        assert!(before
            .visible_fact(store.primary_fact_id(), &loaded.runtime)
            .is_err());
        assert!(after
            .visible_fact(store.primary_fact_id(), &loaded.runtime)
            .is_ok());
    }
    for id in [
        original.store_and_infer_result.membership_fact_id,
        original.store_and_infer_result.defining_equal_fact_id,
    ] {
        assert!(after.visible_fact(id, &loaded.runtime).is_err());
    }
}

#[test]
fn module_function_normalization_requires_its_exact_local_equality_citation() {
    let (mut loaded, _project_22) = tracer();
    let foreign = definition(&loaded.closure.files[0].run.statement_results[0])
        .store_and_infer_result
        .defining_equal_fact_id;
    let FunctionBodySourceProof::KnownEquality(path) = &mut expansion(&mut loaded).function_body
    else {
        panic!("actual equality path")
    };
    assert!(!path.path.is_empty());
    assert_ne!(path.path[0].2, foreign);
    path.path[0].2 = foreign;
    assert!(
        !compiles(loaded),
        "same original proposition is not an available caller FactId"
    );
}

#[test]
fn module_function_normalization_preserves_original_call_formation_and_body_substitution() {
    let (mut loaded, _project_23) = tracer();
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(wd),
        ..
    } = expansion(&mut loaded)
        .application_well_defined
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("original call WD")
    };
    assert!(!wd.requirement_fact_verified.is_empty());
    wd.requirement_fact_verified.clear();
    assert!(!compiles(loaded));
    let (mut loaded, _project_24) = tracer();
    let step = expansion(&mut loaded);
    step.expanded_body = super::number_object("7");
    step.continued_body = step.expanded_body.clone();
    assert!(!compiles(loaded));
}

#[test]
fn module_function_release_requires_original_capture_and_complete_publications() {
    for capture in [false, true] {
        let (mut loaded, _project_25) = tracer();
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::ObjDef(
            ExecReleaseObjDefStmtResult::Success(released),
        )) = &mut loaded.closure.files[1].run.statement_results[0]
        else {
            panic!("actual release")
        };
        if capture {
            let crate::exec_env::StoredIdentifierDefinition::HaveFnEqual((_, declaration)) =
                &mut released.looked_up
            else {
                panic!("captured function")
            };
            std::rc::Rc::make_mut(declaration)
                .equal_to_anonymous_fn
                .body
                .ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            released.store_and_infer.pop();
        }
        assert!(!compiles(loaded));
    }
}
