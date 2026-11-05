use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecDefStructStmtResult, ExecDefStructStmtSuccessResult};
use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult, LoadedLeanSource};

fn load(name: &str) -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load(name)
}

#[test]
fn exported_dependent_record_fields_keep_their_original_type_scope() {
    let (loaded, _project_1) = load("module_exported_dependent_record");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let caller = SourcePosition::module_file(&loaded.closure, 1, 1);
    let record = Obj::Identifier(IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "record".into(),
    });
    compiler
        .with_struct_receiver(&record, &caller, |carrier, member, producer| {
            assert_eq!(producer.module_file_number(), Some(0));
            assert!(member.contains("source_0.h_"));
            assert!(compiler
                .compile_struct_reference_arguments(carrier, &caller)
                .is_err());
            assert_eq!(
                compiler
                    .compile_struct_reference_arguments(carrier, producer)?
                    .len(),
                2
            );
            Ok(())
        })
        .unwrap();
    let first = compiler
        .compile_module(&loaded.closure, "ExportedDependentRecord")
        .unwrap();
    assert_eq!(
        first,
        compiler
            .compile_module(&loaded.closure, "ExportedDependentRecord")
            .unwrap()
    );
    let before = SourcePosition::module_file(&loaded.closure, 0, 1);
    assert!(compiler.compile_struct_receiver(&record, &before).is_err());
}

#[test]
fn exported_record_preflight_retains_its_qualified_hypothetical_subject() {
    let (loaded, _project_2) = load("module_coordinate_value");
    let statement = &loaded.closure.files[0].run.statement_results[1];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = statement
    else {
        panic!("typed coordinate value")
    };
    let root = SourcePosition::module_file(&loaded.closure, 0, 1);
    let statement_position = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 0);
    let preflight = SourcePosition::new(
        Some(&statement_position),
        SourceOwner::HaveEqualType(proof),
        1,
    );
    let id = proof.type_preflight.defined_params.store_and_infer_results[0].primary_fact_id();
    let Fact::AtomicFact(AtomicFact::InFact(member)) =
        preflight.source_fact(id, &loaded.runtime).unwrap()
    else {
        panic!("hypothetical membership")
    };
    assert!(
        matches!(&member.element, Obj::Identifier(IdentifierObj::WithExportFileId {
        export_file_id: 0, name,
    }) if name=="point")
    );
    let ParamType::Obj(carrier) = &proof.statement.param_def.groups[0].param_type else {
        panic!("declared record carrier")
    };
    assert_eq!(member.set.ir(), carrier.ir());
}

#[test]
fn exported_record_preflight_binding_is_scoped_and_keeps_its_original_id() {
    let (loaded, _project_3) = load("module_coordinate_value");
    let statement = &loaded.closure.files[0].run.statement_results[1];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = statement
    else {
        panic!("typed coordinate value")
    };
    let parameter = &proof.statement.param_def.groups[0].params[0];
    let identifier = IdentifierObj::WithExportFileId {
        export_file_id: 0,
        name: "point".into(),
    };
    let root = SourcePosition::module_file(&loaded.closure, 0, 1);
    let statement_position = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 0);
    for stage in [0, 1] {
        let site = SourcePosition::new(
            Some(&statement_position),
            SourceOwner::HaveEqualType(proof),
            stage,
        );
        let found = site.preflight_parameter(&identifier, &loaded.runtime);
        if stage == 0 {
            assert!(found.is_err());
        } else {
            assert_eq!(found.unwrap(), Some(parameter));
        }
        for export_file_id in [1, 99] {
            let wrong = IdentifierObj::WithExportFileId {
                export_file_id,
                name: "point".into(),
            };
            assert!(site
                .preflight_parameter(&wrong, &loaded.runtime)
                .unwrap()
                .is_none());
        }
    }
    let published = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 3);
    let unintroduced = SourcePosition::new(Some(&published), SourceOwner::HaveEqualType(proof), 0);
    let plain = IdentifierObj::from_bound_name(parameter);
    for identifier in [&plain, &identifier] {
        assert!(unintroduced
            .preflight_parameter(identifier, &loaded.runtime)
            .is_err());
    }
    for before in [1, 2] {
        let outside = SourcePosition::module_file(&loaded.closure, 0, before);
        assert!(outside
            .preflight_parameter(&identifier, &loaded.runtime)
            .unwrap()
            .is_none());
    }
}

#[test]
fn exported_record_preflight_rejects_drifted_temporary_binding_capture() {
    let (mut loaded, _project_4) = load("module_coordinate_value");
    let changed = loaded.runtime.global_ids.allocate_identifier_id();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = &mut loaded.closure.files[0].run.statement_results[1]
    else {
        panic!("typed coordinate value")
    };
    let Some(crate::exec_env::StoredIdentifierDefinition::ParamType((bound, _))) = proof
        .type_local_env
        .definitions
        .identifiers
        .get_mut("point")
    else {
        panic!("original hypothetical binding")
    };
    bound.id = changed;
    let error = super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "wrong_preflight_binding")
        .err()
        .unwrap();
    assert!(error.to_string().contains("Parameters/PreflightCapture"));
}

#[test]
fn dependent_record_membership_requires_the_original_preceding_group_value() {
    use crate::compile_to_lean::helper::{parameter_type_fact_matches, source_subject};
    use std::collections::HashMap;
    let (loaded, _project_5) = load("module_dependent_record_value");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = &loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("dependent carrier and record declaration")
    };
    let groups = &proof.statement.param_def.groups;
    let carrier = groups[0].params[0].id;
    let record = groups[1].params[0].id;
    let fact = source_subject(&proof.membership_checks[1]).unwrap();
    let matches = |bindings| {
        parameter_type_fact_matches(
            &groups[1].param_type,
            &proof.statement.objs_equal_to[1],
            &fact,
            &bindings,
        )
    };
    assert!(matches(HashMap::from([(
        carrier,
        proof.statement.objs_equal_to[0].clone()
    )])));
    assert!(!matches(HashMap::new()));
    assert!(!matches(HashMap::from([(
        carrier,
        Obj::StandardSet(StandardSet::C)
    )])));
    assert!(!matches(HashMap::from([(
        record,
        proof.statement.objs_equal_to[0].clone()
    )])));
}

#[test]
fn declared_type_specialization_waits_for_publication_and_obeys_stage_ceilings() {
    let (loaded, _project_6) = load("module_dependent_record_value");
    let statement = &loaded.closure.files[1].run.statement_results[0];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = statement
    else {
        panic!("dependent declaration")
    };
    let ParamType::Obj(carrier) = &proof.statement.param_def.groups[1].param_type else {
        panic!("record carrier")
    };
    let root = SourcePosition::module_file(&loaded.closure, 1, 0);
    let finds = |site: &SourcePosition<'_>| {
        site.with_visible_declared_type(carrier, &mut |found, group, _| {
            Ok((group, std::ptr::eq(found, proof)))
        })
        .unwrap()
    };
    for before in [0, 1, 2, 4, 5] {
        let site = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), before);
        assert!(finds(&site).is_none());
    }
    let published = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 6);
    assert_eq!(finds(&published), Some((1, true)));
    let ceiling = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 5);
    let closed = SourcePosition::module_file(&loaded.closure, 1, 1);
    // A completed enclosing run cannot reopen this unfinished statement.
    let limited = SourcePosition::new(Some(&closed), SourceOwner::Statement(statement), 5);
    assert!(finds(&limited).is_none());
    assert_eq!(finds(&closed), Some((1, true)));
    let preflight = SourcePosition::new(Some(&ceiling), SourceOwner::HaveEqualType(proof), 1);
    // A genuine preflight parent is the statement's zero stage.
    let zero = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 0);
    let preflight = SourcePosition {
        parent: Some(&zero),
        ..preflight
    };
    assert!(finds(&preflight).is_none());
    let specialized = SourcePosition::new(Some(&published), SourceOwner::HaveEqualType(proof), 1);
    assert!(finds(&specialized).is_none());
}

#[test]
fn declared_type_closure_uses_its_formal_parameter_instead_of_the_actual_alias() {
    let (loaded, _project_7) = load("module_dependent_record_value");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = &loaded.closure.files[1].run.statement_results[0]
    else {
        panic!("dependent declaration")
    };
    let ParamType::Obj(carrier) = &proof.statement.param_def.groups[1].param_type else {
        panic!("record carrier")
    };
    let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier)) = carrier else {
        panic!("structured carrier")
    };
    let id = proof.statement.param_def.groups[0].params[0].id.value();
    let closed = SourcePosition::module_file(&loaded.closure, 1, 1);
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let arguments = compiler
        .compile_declared_struct_arguments(carrier, &closed)
        .unwrap()
        .unwrap();
    assert!(
        arguments[0].contains(&format!("=> _value_i{id})")),
        "{}",
        arguments[0]
    );
}

#[test]
fn declared_type_specialization_replays_cartesian_and_function_carriers() {
    let (loaded, _project_8) = load("module_dependent_function_and_vector");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let output = compiler
        .compile_module(&loaded.closure, "DependentParameterTypes")
        .unwrap();
    assert_eq!(
        output,
        compiler
            .compile_module(&loaded.closure, "DependentParameterTypes")
            .unwrap()
    );
}

fn declaration(statement: &ExecStmtResult) -> &ExecDefStructStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        ExecDefStructStmtResult::Success(proof),
    )) = statement
    else {
        panic!("original structure declaration")
    };
    proof
}

fn declaration_mut(statement: &mut ExecStmtResult) -> &mut ExecDefStructStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(
        ExecDefStructStmtResult::Success(proof),
    )) = statement
    else {
        panic!("original structure declaration")
    };
    proof
}

fn root_name(export_file_id: usize) -> AtomicName {
    AtomicName::WithExportFileId {
        export_file_id,
        name: "CoordinatePair".into(),
    }
}

fn imported_name(global_mod_id: usize, export_file_id: usize) -> AtomicName {
    AtomicName::WithModAndExportFileId {
        global_mod_id,
        export_file_id,
        name: "CoordinatePair".into(),
    }
}

#[test]
fn qualified_structures_replay_fields_conditions_headers_and_dependent_function_returns() {
    for name in [
        "module_coordinate_fields",
        "module_imported_structure_fields",
        "module_coordinate_value",
        "module_dependent_record_value",
    ] {
        let (loaded, _project_9) = load(name);
        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        let output = compiler.compile_module(&loaded.closure, name).unwrap();
        assert_eq!(
            output,
            compiler.compile_module(&loaded.closure, name).unwrap()
        );
        assert!(output.contains("source_0.struct_1"));
        if name == "module_imported_structure_fields" {
            assert!(output.contains("source_1.struct_1"));
            assert!(output.contains("source_0._struct_indices_4"));
        }
    }
}

#[test]
fn qualified_structures_keep_original_producers_when_local_and_imported_names_collide() {
    for (fixture, names) in [
        ("module_coordinate_fields", [root_name(0), root_name(1)]),
        (
            "module_imported_structure_fields",
            [imported_name(0, 0), imported_name(1, 0)],
        ),
    ] {
        let (loaded, _project_10) = load(fixture);
        let file = loaded.closure.target_file;
        let scope = SourcePosition::module_file(
            &loaded.closure,
            file,
            loaded.closure.files[file].run.statement_results.len(),
        );
        for (expected_file, name) in names.iter().enumerate() {
            let (proof, producer, index) = scope.visible_struct(name, &loaded.runtime).unwrap();
            let expected_index = if fixture == "module_coordinate_fields" && expected_file == 1 {
                2
            } else {
                0
            };
            assert_eq!(producer.module_file_number(), Some(expected_file));
            assert_eq!(index, expected_index);
            assert!(std::ptr::eq(
                proof,
                declaration(
                    &loaded.closure.files[expected_file].run.statement_results[expected_index],
                )
            ));
        }
    }
}

#[test]
fn qualified_structure_visibility_preserves_file_prefix_and_own_statement_stage() {
    let (loaded, _project_11) = load("module_coordinate_fields");
    let base_before = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(base_before
        .visible_struct(&root_name(0), &loaded.runtime)
        .is_err());
    let main_before = SourcePosition::module_file(&loaded.closure, 1, 2);
    assert!(main_before
        .visible_struct(&root_name(0), &loaded.runtime)
        .is_ok());
    assert!(main_before
        .visible_struct(&root_name(1), &loaded.runtime)
        .is_err());
    let statement = &loaded.closure.files[1].run.statement_results[2];
    for stage in [0, 1] {
        let site =
            SourcePosition::new(Some(&main_before), SourceOwner::Statement(statement), stage);
        assert_eq!(
            site.visible_struct(&root_name(1), &loaded.runtime).is_ok(),
            stage == 1
        );
    }
    for export in [2, 99] {
        assert!(main_before
            .visible_struct(&root_name(export), &loaded.runtime)
            .is_err());
    }
}

#[test]
fn qualified_structures_reject_missing_imports_and_unrelated_completed_environments() {
    let (loaded, _project_12) = load("module_imported_structure_fields");
    let caller = SourcePosition::module_file(&loaded.closure, 0, 4);
    assert!(caller
        .visible_struct(&imported_name(1, 0), &loaded.runtime)
        .is_err());
    let main = SourcePosition::module_file(&loaded.closure, 2, 0);
    for name in [imported_name(99, 0), imported_name(0, 99), root_name(0)] {
        assert!(main.visible_struct(&name, &loaded.runtime).is_err());
    }
}

#[test]
fn qualified_structure_capture_rejects_changed_field_identity() {
    let (mut loaded, _project_13) = load("module_coordinate_fields");
    let changed = loaded.runtime.global_ids.allocate_identifier_id();
    declaration_mut(&mut loaded.closure.files[0].run.statement_results[0])
        .statement
        .fields[0]
        .binding
        .id = changed;
    let main = SourcePosition::module_file(&loaded.closure, 1, 0);
    let error = main
        .visible_struct(&root_name(0), &loaded.runtime)
        .err()
        .unwrap();
    assert!(error.to_string().contains("Struct/DeclarationCapture"));
    assert!(super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "changed_struct_capture")
        .is_err());
}

#[test]
fn qualified_struct_law_publications_reject_a_different_module_carrier() {
    let (mut loaded, _project_14) = load("module_imported_structure_fields");
    let proof = declaration_mut(&mut loaded.closure.files[0].run.statement_results[1]);
    let StoreFactResult::ForallFact(stored) = &mut proof.definition_facts[0].store_and_infer.store
    else {
        panic!("published quantified law")
    };
    let ParamType::Obj(Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier))) =
        &mut stored.fact.typed_parameters.groups[0].param_type
    else {
        panic!("published record carrier")
    };
    carrier.name = AtomicName::WithModAndExportFileId {
        global_mod_id: 1,
        export_file_id: 0,
        name: "PositivePoint".into(),
    };
    let error = super::LitexToLeanCompiler::new(loaded.runtime)
        .compile_module(&loaded.closure, "wrong_struct_law")
        .err()
        .unwrap();
    assert!(error.to_string().contains("Struct/PublishedLawCarrier"));
}
