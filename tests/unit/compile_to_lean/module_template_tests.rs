use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult};
use crate::prelude::*;
use crate::run_module::{load_file_for_lean, LoadLeanSourceResult, LoadedLeanSource};

fn load(name: &str) -> super::module_fixtures::LoadedProject {
    super::module_fixtures::load(name)
}

fn template(statement: &ExecStmtResult) -> &ExecDefTemplateStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(p),
    )) = statement
    else {
        panic!("template declaration")
    };
    p
}

#[test]
fn qualified_template_values_replay_export_import_guards_aliases_and_distinct_owners() {
    for name in ["module_template_values", "module_imported_templates"] {
        let (loaded, _project_1) = load(name);
        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        let first = compiler
            .compile_module(&loaded.closure, "QualifiedTemplates")
            .unwrap();
        assert_eq!(
            first,
            compiler
                .compile_module(&loaded.closure, "QualifiedTemplates")
                .unwrap()
        );
        assert!(first.contains("source_0._template_i"));
        assert!(first.contains("source_1._template_i"));
    }
}

#[test]
fn qualified_template_lookup_retains_the_original_declaration_and_source_prefix() {
    let (loaded, _project_2) = load("module_template_values");
    let name = |file, name: &str| AtomicName::WithExportFileId {
        export_file_id: file,
        name: name.into(),
    };
    let base = SourcePosition::module_file(&loaded.closure, 0, 0);
    assert!(base
        .visible_template(&name(0, "translate"), &loaded.runtime)
        .is_err());
    let after = SourcePosition { before: 1, ..base };
    assert!(after
        .visible_template(&name(0, "translate"), &loaded.runtime)
        .is_ok());
    assert!(after
        .visible_template(&name(0, "quotient"), &loaded.runtime)
        .is_err());
    for before in [4, 5] {
        let caller = SourcePosition::module_file(&loaded.closure, 1, before);
        let (original, producer, index) = caller
            .visible_template(&name(0, "translate"), &loaded.runtime)
            .unwrap();
        assert_eq!(producer.module_file_number(), Some(0));
        assert_eq!(index, 0);
        assert!(std::ptr::eq(
            original,
            template(&loaded.closure.files[0].run.statement_results[0])
        ));
        assert_eq!(
            caller
                .visible_template(&name(1, "translate"), &loaded.runtime)
                .is_ok(),
            before == 5
        );
        assert!(caller
            .visible_template(&name(99, "translate"), &loaded.runtime)
            .is_err());
    }
}

#[test]
fn imported_same_named_templates_do_not_share_owners_or_visibility() {
    let (loaded, _project_3) = load("module_imported_templates");
    let name = |module| AtomicName::WithModAndExportFileId {
        global_mod_id: module,
        export_file_id: 0,
        name: "translate".into(),
    };
    let caller = SourcePosition::module_file(&loaded.closure, 2, 0);
    for (file, index) in [(0, 1), (1, 0)] {
        let (proof, producer, found) = caller
            .visible_template(&name(file), &loaded.runtime)
            .unwrap();
        assert_eq!(producer.module_file_number(), Some(file));
        assert_eq!(found, index);
        assert!(std::ptr::eq(
            proof,
            template(&loaded.closure.files[file].run.statement_results[index])
        ));
    }
    let unrelated = SourcePosition::module_file(&loaded.closure, 0, 2);
    assert!(unrelated
        .visible_template(&name(1), &loaded.runtime)
        .is_err());
    assert!(caller.visible_template(&name(99), &loaded.runtime).is_err());
}

#[test]
fn template_self_reference_requires_its_full_original_owner() {
    let (loaded, _project_4) = load("module_template_values");
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let root = SourcePosition::module_file(&loaded.closure, 1, 4);
    let statement = &loaded.closure.files[1].run.statement_results[4];
    let declaration = SourcePosition::new(Some(&root), SourceOwner::Statement(statement), 0);
    let p = template(statement);
    let complete = SourcePosition::new(Some(&declaration), SourceOwner::Template(p), 2);
    let args = p
        .statement
        .template_arg_def
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p)))
        .collect::<Vec<_>>();
    for file in [0, 1, 99] {
        let instance = InstantiatedTemplateObj {
            template_name: AtomicName::WithExportFileId {
                export_file_id: file,
                name: "translate".into(),
            },
            args: args.clone(),
        };
        let reference = compiler
            .template_self_reference(&instance, &complete)
            .unwrap();
        assert_eq!(reference.is_some(), file == 1);
        if let Some(reference) = reference {
            assert!(reference.contains("source_1._template_i"));
        }
    }
}

#[test]
fn qualified_template_lookup_rejects_changed_original_header_capture() {
    let (mut loaded, _project_5) = load("module_template_values");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(p),
    )) = &mut loaded.closure.files[0].run.statement_results[0]
    else {
        panic!()
    };
    p.statement.template_name = "unrelated".into();
    let caller = SourcePosition::module_file(&loaded.closure, 1, 0);
    let name = AtomicName::WithExportFileId {
        export_file_id: 0,
        name: "translate".into(),
    };
    let error = caller
        .visible_template(&name, &loaded.runtime)
        .err()
        .unwrap();
    assert!(error.to_string().contains("Template/DeclarationCapture"));
}

#[test]
fn exported_template_fields_use_the_original_membership_publication() {
    let (loaded, _project_6) = load("module_template_record_fields");
    let publication = template(&loaded.closure.files[0].run.statement_results[1]).definition_facts
        [0]
    .store_and_infer
    .primary_fact_id();
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let output = compiler
        .compile_module(&loaded.closure, "ExportedPairTemplate")
        .unwrap();
    assert!(output.contains(&format!("source_0.h_{}", publication.value())));
    assert_eq!(
        output,
        compiler
            .compile_module(&loaded.closure, "ExportedPairTemplate")
            .unwrap()
    );
}

#[test]
fn qualified_template_formation_retains_argument_wd_and_the_nonzero_guard() {
    for mutation in 0..3 {
        let (mut loaded, _project_7) = load("module_template_values");
        let fact = super::fact_statement_mut(&mut loaded.closure.files[1].run.statement_results[2]);
        let proof = super::equality_proof_mut(&mut fact.verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(instance),
            ..
        } = proof
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .left
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("quotient instance formation")
        };
        assert_eq!(instance.requirement_fact_verified.len(), 3);
        match mutation {
            0 => {
                instance.requirement_fact_verified.pop();
            }
            1 => instance.requirement_fact_verified.swap(0, 1),
            _ => instance.child_obj_well_defined.swap(0, 1),
        }
        assert!(super::LitexToLeanCompiler::new(loaded.runtime)
            .compile_module(&loaded.closure, "IncompleteQualifiedTemplateWD")
            .is_err());
    }
}

#[test]
fn selected_template_functions_cite_their_original_membership_publication() {
    let (mut loaded, _project_8) = load("module_template_selected_function");
    let publication = template(&loaded.closure.files[0].run.statement_results[0]).definition_facts
        [0]
    .store_and_infer
    .primary_fact_id();
    let checked = super::fact_statement_mut(&mut loaded.closure.files[0].run.statement_results[1]);
    let proof = super::atomic_proof_mut(&mut checked.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(citation) = &proof.searched_proof
    else {
        panic!("original template membership citation")
    };
    assert_eq!(citation.detailed_ref().cite.fact_id, publication);
    let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
    let output = compiler
        .compile_module(&loaded.closure, "SelectedTemplateFunction")
        .unwrap();
    assert!(output.contains(&format!("source_0.h_{}", publication.value())));
    assert_eq!(
        output,
        compiler
            .compile_module(&loaded.closure, "SelectedTemplateFunction")
            .unwrap()
    );
    let checked = super::fact_statement_mut(&mut loaded.closure.files[0].run.statement_results[1]);
    let proof = super::atomic_proof_mut(&mut checked.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(citation) =
        &mut proof.searched_proof
    else {
        panic!()
    };
    citation.as_detailed_mut().unwrap().cite.fact_id = FactId::new(u64::MAX);
    assert!(compiler
        .compile_module(&loaded.closure, "ChangedTemplateCitation")
        .is_err());
}
