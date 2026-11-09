use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty,
    InFactSearchProofByKnownSpecialProperty,
    TemplateFunctionInDeclaredFnSetProof,
};
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
    for mutation in 0..7 {
        let (mut loaded, _project) = load("module_template_selected_function");
        let publication = template(&loaded.closure.files[0].run.statement_results[0])
            .definition_facts[0]
            .store_and_infer
            .primary_fact_id();
        let checked =
            super::fact_statement_mut(&mut loaded.closure.files[0].run.statement_results[1]);
        let proof = super::atomic_proof_mut(&mut checked.verify_result);
        let AtomicFact::InFact(goal) = &proof.fact else {
            panic!("membership goal")
        };
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
            AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
                InFactSearchProofByKnownSpecialProperty::TemplateFunctionInDeclaredFnSet(selected),
            ),
        ) = &proof.searched_proof
        else {
            panic!("declared template function signature")
        };
        assert_eq!(
            goal.element,
            Obj::InstantiatedTemplateObj(selected.instance.clone())
        );
        assert!(matches!(&selected.instance.template_name,
            AtomicName::WithExportFileId { export_file_id: 0, name } if name == "selected_function"));
        assert_eq!(
            selected.instance.args,
            vec![Obj::StandardSet(StandardSet::R); 2]
        );
        assert_eq!(
            *selected.declared_signature.ret_set,
            Obj::StandardSet(StandardSet::R)
        );
        assert!(matches!(
            selected.signature_match,
            EqualFactSearchedProof::ByTheyAreTheSame(_)
        ));

        let compiler = super::LitexToLeanCompiler::new(loaded.runtime);
        let output = compiler
            .compile_module(&loaded.closure, "SelectedTemplateFunction")
            .unwrap();
        // The selected native proof reads the declared signature directly, but
        // Lean still obtains the chosen function's membership from this exact
        // original publication, with the instance's own argument WD.
        assert!(output.contains(&format!("source_0.h_{}", publication.value())));
        if mutation == 0 {
            assert_eq!(
                output,
                compiler
                    .compile_module(&loaded.closure, "SelectedTemplateFunction")
                    .unwrap()
            );
        }
        match mutation {
            0 => {
                selected_function_signature(&mut loaded.closure.files[0].run.statement_results[1])
                    .instance
                    .template_name = AtomicName::WithExportFileId {
                    export_file_id: 99,
                    name: "selected_function".into(),
                }
            }
            1 => {
                selected_function_signature(&mut loaded.closure.files[0].run.statement_results[1])
                    .declared_signature
                    .ret_set = Box::new(Obj::StandardSet(StandardSet::N))
            }
            2 => {
                selected_function_signature(&mut loaded.closure.files[0].run.statement_results[1])
                    .instance
                    .args[0] = Obj::StandardSet(StandardSet::N)
            }
            3 | 4 => {
                let checked = super::fact_statement_mut(
                    &mut loaded.closure.files[0].run.statement_results[1],
                );
                let proof = super::atomic_proof_mut(&mut checked.verify_result);
                let wd = &mut proof
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter[0];
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(instance),
                    ..
                } = wd.as_detailed_mut().unwrap()
                else {
                    panic!("instance formation")
                };
                assert_eq!(instance.child_obj_well_defined.len(), 2);
                assert_eq!(instance.requirement_fact_verified.len(), 2);
                if mutation == 3 {
                    instance.child_obj_well_defined.clear();
                } else {
                    instance.requirement_fact_verified.clear();
                }
            }
            5 | 6 => {
                let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
                    ExecDefTemplateStmtResult::Success(declaration),
                )) = &mut loaded.closure.files[0].run.statement_results[0]
                else {
                    panic!("template")
                };
                if mutation == 5 {
                    declaration.definition_facts[0].source_fact_id = FactId::new(u64::MAX);
                } else {
                    declaration.definition_facts.clear();
                }
            }
            _ => unreachable!(),
        }
        compiler
            .compile_module(&loaded.closure, "ChangedTemplateEvidence")
            .expect_err(&format!("tampered template evidence {mutation}"));
    }
}

fn selected_function_signature(
    statement: &mut ExecStmtResult,
) -> &mut TemplateFunctionInDeclaredFnSetProof {
    let checked = super::fact_statement_mut(statement);
    let proof = super::atomic_proof_mut(&mut checked.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::TemplateFunctionInDeclaredFnSet(selected),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("declared template function signature")
    };
    selected
}
