use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult, ExecDefThmBodyProof,
    ExecObtainObjFromAtomicFactStmtResult, ExecObtainObjFromExistFactStmtResult,
    ObtainExistVerifySuccess,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/obtained_template_real_composition/statement.lit"),
    include_str!("../../../lean/examples/obtained_template_reciprocal/statement.lit"),
    include_str!("../../../lean/examples/obtained_template_function_composition/statement.lit"),
    include_str!("../../../lean/examples/obtained_template_generic_copy/statement.lit"),
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

#[test]
fn obtained_template_compositions_preserve_witnesses_in_formula_bodies() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "obtained_compositions")
            .expect(source);
        assert!(lean.contains("Litex.obtainedValue") && lean.contains("Litex.obtainedObject"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "obtained_compositions").unwrap()
        );
    }
}

#[test]
fn obtained_template_requires_original_existence_formation_and_publication() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                ExecObtainObjFromExistFactStmtResult::Success(body),
            ),
        )) = p.body.as_mut()
        else {
            panic!("ordinary template obtain")
        };
        let ObtainExistVerifySuccess::Exist(existence) = &mut body.verify_exist else {
            panic!()
        };
        match mutation {
            0 => existence
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .assumed_body_facts
                .clear(),
            1 => body
                .store_and_infer_result
                .store_and_infer_results
                .swap(0, 1),
            2 => body.statement.equal_tos[0].id = IdentifierId::new(u64::MAX),
            3 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            4 => p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            5 => existence
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_obtain")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn obtained_function_predicate_requires_its_original_projection_and_stores() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                ExecObtainObjFromAtomicFactStmtResult::Success(body),
            ),
        )) = p.body.as_mut()
        else {
            panic!("predicate obtain")
        };
        match mutation {
            0 => body.store_and_infer_result.store_and_infer_results.clear(),
            1 => body.statement.fact.body.swap(0, 2),
            2 => p.definition_facts[1].source_fact_id = FactId::new(u64::MAX),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_function_obtain")
            .expect_err(&format!("mutation {mutation}"));
    }
}

fn selected_nonzero(run: &mut RunLitexCodeResult) -> &mut SearchProofByKnownForallFact {
    let p = super::named_theorem_mut(&mut run.statement_results[3]);
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!()
    };
    let p = super::fact_statement_mut(&mut body.proof_steps[1]);
    let p = super::atomic_proof_mut(&mut p.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(known) = &mut p.searched_proof
    else {
        panic!("recorded conjunction component")
    };
    known
}

#[test]
fn obtained_template_conjunction_citation_requires_exact_component_and_requirements() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = selected_nonzero(&mut run).as_detailed_mut().unwrap();
        let ForallConclusionLocation::AndFactComponent(location) = &mut p.cite.location else {
            panic!()
        };
        assert_eq!(location.component_index, 1);
        match mutation {
            0 => location.component_index = 0,
            1 => location.component_index = usize::MAX,
            2 => location.then_fact_index = usize::MAX,
            3 => p
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts
                .clear(),
            4 => p.arg_match_proofs.swap(0, 1),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_component")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn obtained_template_witness_publication_does_not_escape_its_source_prefix() {
    let (mut run, compiler) = super::execute(SOURCES[0]);
    compiler.compile_run(&run, "baseline").unwrap();
    let id = template(&mut run).definition_facts[1]
        .store_and_infer
        .primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(before.visible_template_publication(id).is_none());
    assert!(after.visible_template_publication(id).is_some());
}
