use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult, LoadedLeanSource};
use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByDefStmtSuccess};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{AtomicExceptEqualityFactSearchProofByDefinition, UserDefinedPropDefinitionProof};

fn load(name: &str) -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load(name)
}
fn call(loaded: &mut LoadedLeanSource) -> &mut ExecByDefStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof))) =
        &mut loaded
            .closure
            .files
            .last_mut()
            .unwrap()
            .run
            .statement_results[0]
    else {
        panic!("original by def")
    };
    proof
}
fn fold(proof: &mut ExecByDefStmtSuccess) -> &mut UserDefinedPropDefinitionProof {
    let VerifyFactResult::AtomicExceptEquality(result) = &mut proof.proof else {
        panic!("actual atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(success) = result.as_mut() else {
        panic!("success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByDefinition(
        AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(proof),
    ) = &mut success.searched_proof
    else {
        panic!("original definition route")
    };
    proof
}
fn compiles(loaded: LoadedLeanSource) -> bool {
    super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "predicate_control")
        .is_ok()
}
#[test]
fn module_predicate_replays_original_fold_inference_and_forall_scope() {
    let (mut loaded, _project_1) = load("module_positive_predicate");
    assert_eq!(fold(call(&mut loaded)).requirement_facts.len(), 2);
    assert_eq!(fold(call(&mut loaded)).proof_of_requirement_facts.len(), 2);
    let output = super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "positive_predicate")
        .unwrap();
    assert!(output.contains("source_0.prop_1"));
    assert_eq!(output.matches("def prop_1").count(), 1);
}
#[test]
fn module_predicate_rejects_missing_reordered_and_changed_original_requirements() {
    let (mut loaded, _project_2) = load("module_positive_predicate");
    fold(call(&mut loaded)).proof_of_requirement_facts.pop();
    assert!(!compiles(loaded));
    let (mut loaded, _project_3) = load("module_positive_predicate");
    fold(call(&mut loaded))
        .proof_of_requirement_facts
        .swap(0, 1);
    assert!(!compiles(loaded));
    let (mut loaded, _project_4) = load("module_positive_predicate");
    fold(call(&mut loaded)).requirement_facts.swap(0, 1);
    assert!(!compiles(loaded));
    let (mut loaded, _project_5) = load("module_positive_predicate");
    let Fact::AtomicFact(AtomicFact::InFact(fact)) =
        &mut fold(call(&mut loaded)).requirement_facts[0]
    else {
        panic!("original carrier")
    };
    fact.set = Obj::StandardSet(StandardSet::C);
    assert!(!compiles(loaded));
}
#[test]
fn module_predicate_requires_original_qualified_producer_and_formation() {
    use crate::compile_to_lean::source_position::SourcePosition;
    let (loaded, _project_6) = load("module_positive_predicate");
    let name = AtomicName::WithExportFileId {
        export_file_id: 0,
        name: "positive".into(),
    };
    let before = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(before.visible_prop(&name, &loaded.runtime).is_err());
    let after = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(after.visible_prop(&name, &loaded.runtime).is_ok());
    let target = SourcePosition::module_file(&loaded.closure, 1, 0);
    for export_file_id in [1, 99] {
        let wrong = AtomicName::WithExportFileId {
            export_file_id,
            name: "positive".into(),
        };
        assert!(target.visible_prop(&wrong, &loaded.runtime).is_err());
    }
    let mut loaded = loaded;
    loaded.closure.files.remove(0);
    loaded.closure.target_file = 0;
    assert!(!compiles(loaded));
}

#[test]
fn module_predicate_nested_exist_projection_keeps_original_definition_namespace() {
    let (loaded, _project_7) = load("module_nested_predicates");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::ExecDefPropStmtResult::Success(pair),
    )) = &loaded.closure.files[0].run.statement_results[1]
    else {
        panic!("nested declaration")
    };
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(clause)) = &pair.statement.iff_facts[0]
    else {
        panic!("predicate clause")
    };
    assert!(
        matches!(
            clause.predicate,
            AtomicName::WithExportFileId {
                export_file_id: 0,
                ..
            }
        ),
        "file parsing preserves canonical declaration identity"
    );
    let output = super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "nested_positive")
        .unwrap();
    assert!(output.contains("source_0.prop_3"));
    assert!(
        !output.contains("((prop_1 (M := M))"),
        "a copied original clause must keep its producer namespace"
    );
}

#[test]
fn module_predicate_profiles_cover_guarded_dependent_imported_and_distinct_definitions() {
    for name in [
        "module_guarded_predicate",
        "module_dependent_predicate",
        "module_import_predicates",
        "module_predicate_alias_collision",
    ] {
        let (loaded, _project_8) = load(name);
        let output = super::LitexToLeanCompiler::new(loaded.runtime)
            .compile_module(&loaded.closure, name)
            .unwrap();
        assert!(output.contains("source_0.prop_1"), "{name}");
        if name == "module_predicate_alias_collision" {
            assert!(output.contains("source_1.prop_1"));
        }
    }
}

#[test]
fn module_predicate_keeps_namespace_identity_and_private_formation_scope() {
    use crate::compile_to_lean::source_position::SourcePosition;
    use crate::runtime::CodeSource;
    let (loaded, _project_9) = load("module_predicate_alias_collision");
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
    let left_name = AtomicName::WithModAndExportFileId {
        global_mod_id: left,
        export_file_id: 0,
        name: "signed".into(),
    };
    let right_name = AtomicName::WithModAndExportFileId {
        global_mod_id: right,
        export_file_id: 0,
        name: "signed".into(),
    };
    let target = SourcePosition::module_file(&loaded.closure, 2, 0);
    let (left_prop, _, _) = target.visible_prop(&left_name, &loaded.runtime).unwrap();
    let (right_prop, _, _) = target.visible_prop(&right_name, &loaded.runtime).unwrap();
    assert!(matches!(
        left_prop.statement.iff_facts[0],
        Fact::AtomicFact(AtomicFact::GreaterFact(_))
    ));
    assert!(matches!(
        right_prop.statement.iff_facts[0],
        Fact::AtomicFact(AtomicFact::LessFact(_))
    ));
    assert_ne!(
        left_prop.statement.typed_parameters.ordered_param_ids(),
        right_prop.statement.typed_parameters.ordered_param_ids()
    );
    let left_scope = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(
        left_scope
            .visible_prop(&right_name, &loaded.runtime)
            .is_err(),
        "a sibling package is outside the declaration scope"
    );
    let private = left_prop.assumed_iff_facts[0]
        .store_and_infer
        .primary_fact_id();
    assert!(target.visible_fact(private, &loaded.runtime).is_err());
    assert!(
        left_scope.visible_fact(private, &loaded.runtime).is_err(),
        "formation assumptions remain private after the declaration"
    );
}

#[test]
fn module_predicate_set_kinds_keep_exact_wd_and_domain_store() {
    for index in [0, 1] {
        let (mut loaded, _project_10) = load("module_dependent_predicate");
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            crate::execute::ExecDefPropStmtResult::Success(prop),
        )) = &mut loaded.closure.files[0].run.statement_results[index]
        else {
            panic!("prop")
        };
        prop.param_type_well_defined[0] = ParamTypeWellDefinedProof::Set;
        assert!(!compiles(loaded));
        let (mut loaded, _project_11) = load("module_dependent_predicate");
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            crate::execute::ExecDefPropStmtResult::Success(prop),
        )) = &mut loaded.closure.files[0].run.statement_results[index]
        else {
            panic!("prop")
        };
        prop.statement.typed_parameters.groups[0].param_type =
            ParamType::Set(crate::ast::param::Set {});
        prop.param_type_well_defined[0] = ParamTypeWellDefinedProof::Set;
        assert!(
            !compiles(loaded),
            "sethood cannot replace the original nonempty/finite contract"
        );
    }
}

#[test]
fn module_predicate_requires_original_inference_signature_and_requirement_identity() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferNormalAtomicFactResult, InferResult,
    };
    for missing in [false, true] {
        let (mut loaded, _project_12) = load("module_positive_predicate");
        let Some(InferResult::AtomicFact(InferAtomicFactResult::NormalAtomicFact(rules))) =
            &mut call(&mut loaded).stored.infer
        else {
            panic!("original predicate inference")
        };
        if missing {
            let InferNormalAtomicFactResult::ExpandDefinition(expansion) = &mut rules[1] else {
                panic!("body expansion")
            };
            expansion.derived.clear();
        } else {
            rules.swap(0, 1);
        }
        assert!(!compiles(loaded));
    }
    let (mut loaded, _project_13) = load("module_positive_predicate");
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::AtomicExceptEquality(
        AtomicFactWellDefinedProof::Detailed(wd),
    )) = &mut call(&mut loaded).goal_wd
    else {
        panic!("actual formation")
    };
    let PredicateSignatureWellDefinedProof::Prop {
        predicate: AtomicName::WithExportFileId { export_file_id, .. },
        ..
    } = &mut wd.predicate_signature
    else {
        panic!("qualified signature")
    };
    *export_file_id = 1;
    assert!(!compiles(loaded));
    let (mut loaded, _project_14) = load("module_positive_predicate");
    let changed_id = loaded.runtime.global_ids.allocate_fact_id();
    let Fact::AtomicFact(AtomicFact::InFact(fact)) =
        &mut fold(call(&mut loaded)).requirement_facts[0]
    else {
        panic!("carrier requirement")
    };
    fact.fact_id = changed_id;
    assert!(
        !compiles(loaded),
        "the same proposition with another ID cannot replace the actual requirement"
    );
}
