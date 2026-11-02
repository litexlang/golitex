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

fn load(name: &str) -> LoadedLeanSource {
    let command = parse_launch_command(&[
        "-lean".into(),
        "-strict".into(),
        "-f".into(),
        format!("lean/examples/{name}/statement.lit"),
    ])
    .unwrap();
    let LoadLeanSourceResult::Success(loaded) = load_file_for_lean(command).unwrap() else {
        panic!("source must verify: {name}")
    };
    loaded
}
fn tracer() -> LoadedLeanSource {
    load("module_function_definition")
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
        let loaded = load(name);
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
    let loaded = tracer();
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
    let mut loaded = tracer();
    definition_mut(&mut loaded).statement.name.id =
        loaded.runtime.global_ids.allocate_identifier_id();
    assert!(!compiles(loaded));
    let mut loaded = tracer();
    definition_mut(&mut loaded)
        .store_and_infer_result
        .stored_fact_ids
        .clear();
    assert!(!compiles(loaded));
    let mut loaded = tracer();
    let p = definition_mut(&mut loaded);
    p.store_and_infer_result.membership_fact_id = p.store_and_infer_result.defining_equal_fact_id;
    assert!(!compiles(loaded));
}

#[test]
fn module_function_requires_original_anonymous_and_signature_formation_subjects() {
    for signature in [false, true] {
        let mut loaded = tracer();
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
    let mut loaded = tracer();
    loaded.closure.files[0].run.statement_results.clear();
    assert!(!compiles(loaded));
    let mut loaded = tracer();
    loaded.closure.files.swap(0, 1);
    assert!(!compiles(loaded));
}

#[test]
fn module_function_release_publishes_local_facts_without_exposing_original_fact_ids() {
    let loaded = tracer();
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
    let mut loaded = tracer();
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
    let mut loaded = tracer();
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
    let mut loaded = tracer();
    let step = expansion(&mut loaded);
    step.expanded_body = super::number_object("7");
    step.continued_body = step.expanded_body.clone();
    assert!(!compiles(loaded));
}

#[test]
fn module_function_release_requires_original_capture_and_complete_publications() {
    for capture in [false, true] {
        let mut loaded = tracer();
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
