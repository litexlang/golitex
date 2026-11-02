use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult, ExecHaveObjByExistFactsStmtResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/template_nonempty_member/statement.lit"),
    include_str!("../../../lean/examples/template_singleton_selection/statement.lit"),
    include_str!("../../../lean/examples/template_function_space_member/statement.lit"),
    include_str!("../../../lean/examples/template_larger_real/statement.lit"),
];

fn template(run: &mut RunLitexCodeResult) -> &mut ExecDefTemplateStmtSuccessResult {
    match &mut run.statement_results[0] {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            ExecDefTemplateStmtResult::Success(p),
        )) => p,
        _ => panic!("checked template"),
    }
}

#[test]
fn have_template_bodies_replay_nonempty_members_and_original_existentials() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "have_template").expect(source);
        assert!(lean.contains("Litex.obtainedObject"));
        assert_eq!(lean, compiler.compile_run(&run, "have_template").unwrap());
    }
}

#[test]
fn have_template_members_require_nonempty_evidence_and_exact_ordered_stores() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(body),
            ),
        )) = p.body.as_mut()
        else {
            panic!("nonempty member declaration")
        };
        match mutation {
            0 => body.groups.clear(),
            1 => body.groups[0].nonempty_check = ParamTypeFactCheckResult::Set,
            2 => body.groups[0].defined_params.stored_fact_ids.clear(),
            3 => body.groups[0].param_type_well_defined = ParamTypeWellDefinedProof::Set,
            4 => p.definition_facts[0].source_fact_id = FactId::new(u64::MAX),
            5 => p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_member")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn have_template_existence_keeps_its_source_predicate_and_formation() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[3]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjByExistFacts(
                ExecHaveObjByExistFactsStmtResult::Success(body),
            ),
        )) = p.body.as_mut()
        else {
            panic!("have by existence")
        };
        match mutation {
            0 => {
                let ExistShapedFact::Exist(fact) = &mut body.verify_exist.fact else {
                    panic!()
                };
                fact.facts.clear();
            }
            1 => body
                .verify_exist
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .assumed_body_facts
                .clear(),
            2 => body
                .store_and_infer_result
                .store_and_infer_results
                .swap(0, 1),
            3 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_existence")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn template_call_from_membership_replays_the_selected_citation_and_argument_wd() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[2]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = super::fact_statement_mut(&mut run.statement_results[2]);
        let p = super::atomic_proof_mut(&mut p.verify_result);
        let wd = &mut p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0];
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = wd.as_detailed_mut().unwrap()
        else {
            panic!("call WD")
        };
        let Some(FnObjDomainFnSetEvidence::InFunctionSet {
            fn_set, fact_id, ..
        }) = &mut call.domain_fn_set
        else {
            panic!("original membership route")
        };
        assert_eq!(
            call.child_obj_well_defined.len(),
            1,
            "membership route has only argument children"
        );
        match mutation {
            0 => *fact_id = FactId::new(u64::MAX),
            1 => fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::N)),
            2 => call.child_obj_well_defined.clear(),
            3 => call.requirement_fact_verified.clear(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_call")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn have_template_publication_requires_its_original_visible_prefix() {
    let (mut run, compiler) = super::execute(SOURCES[0]);
    compiler.compile_run(&run, "baseline").unwrap();
    let id = template(&mut run).definition_facts[0]
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
