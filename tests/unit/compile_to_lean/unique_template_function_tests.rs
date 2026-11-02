use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof as Match;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult,
    ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnByForallExistUniqueStmtSuccessResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/unique_record_field/statement.lit"),
    include_str!("../../../lean/examples/unique_record_with_field/statement.lit"),
    include_str!("../../../lean/examples/template_unique_guarded_scalar/statement.lit"),
    include_str!("../../../lean/examples/template_unique_record_field/statement.lit"),
];
fn template(run: &mut RunLitexCodeResult) -> &mut ExecDefTemplateStmtSuccessResult {
    run.statement_results
        .iter_mut()
        .find_map(|s| match s {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
                ExecDefTemplateStmtResult::Success(p),
            )) => Some(p),
            _ => None,
        })
        .unwrap()
}
fn selected(run: &mut RunLitexCodeResult) -> &mut ExecHaveFnByForallExistUniqueStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
        ExecHaveFnByForallExistUniqueStmtResult::Success(p),
    )) = template(run).body.as_mut()
    else {
        panic!("selected template body")
    };
    p
}
#[test]
fn unique_fields_and_templates_replay_original_existence_and_call_proofs() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let code = compiler.compile_run(&run, "unique_fields").expect(source);
        assert_eq!(code, compiler.compile_run(&run, "unique_fields").unwrap());
        assert!(!code.contains("sorry") && !code.contains("axiom "));
    }
}
#[test]
fn selected_template_requires_its_original_membership_and_unique_property() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = selected(&mut run);
        match mutation {
            0 => p.property_forall_fact_id = p.membership_fact_id,
            1 => {
                p.stored_fact_ids.pop();
            }
            2 => {
                let StoreFactResult::AtomicFact(s) = &mut p.membership.store else {
                    panic!()
                };
                let AtomicFact::InFact(member) = &mut s.fact else {
                    panic!()
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &mut member.set else {
                    panic!()
                };
                signature.ret_set = Box::new(Obj::StandardSet(StandardSet::N));
            }
            3 => {
                let StoreFactResult::ForallFact(s) = &mut p.property.store else {
                    panic!()
                };
                s.fact.then_facts.clear();
            }
            4 => {
                let StoreFactResult::ForallFact(s) = &mut p.uniqueness.store else {
                    panic!()
                };
                s.fact.dom_facts.pop();
            }
            5 => {
                let FactWellDefinedProof::ForallFact(wd) = &mut p.property_well_defined else {
                    panic!()
                };
                wd.as_detailed_mut()
                    .unwrap()
                    .introduced_params
                    .defined_params
                    .store_and_infer_results
                    .clear();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_selected_template")
            .expect_err(&format!("mutation {mutation}"));
    }
}
#[test]
fn selected_template_publications_preserve_header_guards_and_source_ids() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        match mutation {
            0 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            1 => {
                p.definition_facts.pop();
            }
            2 | 3 => {
                let StoreFactResult::ForallFact(s) =
                    &mut p.definition_facts[1].store_and_infer.store
                else {
                    panic!()
                };
                if mutation == 2 {
                    s.fact.dom_facts.clear();
                } else {
                    s.fact.typed_parameters.groups.pop();
                }
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_publication")
            .expect_err(&format!("mutation {mutation}"));
    }
}
#[test]
fn known_template_call_checks_argument_then_head_matching_order() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        compiler.compile_run(&run, "baseline").unwrap();
        let fact = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
        let p = super::equality_proof_mut(&mut fact.verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(known) = &mut p.searched_proof else {
            panic!("known template property")
        };
        let Match::ByStructure { child_matches, .. } =
            known.as_detailed_mut().unwrap().arg_match_proofs[0]
                .as_detailed_mut()
                .unwrap()
        else {
            panic!("call matching")
        };
        assert_eq!(child_matches.len(), 2);
        match mutation {
            0 => {
                child_matches.pop();
            }
            1 => child_matches.swap(0, 1),
            2 => {
                let Match::ByStructure { child_matches, .. } =
                    child_matches[1].as_detailed_mut().unwrap()
                else {
                    panic!("template head")
                };
                child_matches.clear();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_call_match")
            .expect_err(&format!("mutation {mutation}"));
    }
}
#[test]
fn selected_template_local_object_appears_only_after_its_body() {
    let (mut run, compiler) = super::execute(SOURCES[2]);
    compiler.compile_run(&run, "baseline").unwrap();
    let declaration = template(&mut run);
    let id = match declaration.body.as_ref() {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
            ExecHaveFnByForallExistUniqueStmtResult::Success(p),
        )) => p.statement.name.id,
        _ => panic!(),
    };
    let head = declaration
        .statement
        .template_arg_def
        .ordered_param_ids()
        .len()
        + declaration.assumed_dom_facts.len();
    let before = SourcePosition::new(None, SourceOwner::Template(declaration), head);
    let after = SourcePosition {
        before: head + 1,
        ..before
    };
    assert!(before.visible_selected_function(&id).is_err());
    assert!(after.visible_selected_function(&id).is_ok());
}
