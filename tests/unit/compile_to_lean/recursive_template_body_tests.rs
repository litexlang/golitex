use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult, ExecHaveFnByInducStmtResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/template_recursive_constant/statement.lit"),
    include_str!("../../../lean/examples/template_recursive_accumulation/statement.lit"),
    include_str!("../../../lean/examples/template_recursive_reciprocal/statement.lit"),
    include_str!("../../../lean/examples/template_recursive_returned_sequence/statement.lit"),
    include_str!("../../../lean/examples/template_recursive_natural_zero/statement.lit"),
];

fn template(run: &mut RunLitexCodeResult) -> &mut ExecDefTemplateStmtSuccessResult {
    match &mut run.statement_results[0] {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            ExecDefTemplateStmtResult::Success(p),
        )) => p,
        _ => panic!("checked recursive template"),
    }
}

#[test]
fn recursive_template_bodies_replay_original_guards_calls_and_formula_capture() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "recursive_template")
            .expect(source);
        assert!(lean.contains("Litex.recursiveNatFnTarget"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "recursive_template").unwrap()
        );
    }
}

#[test]
fn recursive_template_bodies_reject_changed_original_evidence() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        compiler.compile_run(&run, "baseline").unwrap();
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(body),
        )) = p.body.as_mut()
        else {
            panic!("recursive body")
        };
        match mutation {
            0 => p
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            1 => p.definition_facts[0].source_fact_id = FactId::new(u64::MAX),
            2 => body
                .binder_introduction
                .defined_params
                .store_and_infer_results
                .clear(),
            3 => body.store_and_infer_result.case_defining_fact_ids.reverse(),
            4 => body.case_checks.cases.swap(0, 1),
            5 => body.store_and_infer_result.stored_fact_ids.clear(),
            6 => {
                let StoreFactResult::AtomicFact(stored) =
                    &mut body.restricted_self_membership.store
                else {
                    panic!("self member")
                };
                let AtomicFact::InFact(member) = &mut stored.fact else {
                    panic!("self member")
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &mut member.set else {
                    panic!("self signature")
                };
                signature.dom_facts.clear();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_recursive_template")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn recursive_template_guard_is_not_an_optional_context_assumption() {
    let (mut run, compiler) = super::execute(SOURCES[2]);
    compiler.compile_run(&run, "baseline").unwrap();
    template(&mut run).assumed_dom_facts.clear();
    compiler.compile_run(&run, "missing_guard").unwrap_err();
}

#[test]
fn recursive_template_publication_requires_the_original_visible_prefix() {
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

#[test]
fn recursive_template_unfold_requires_recorded_path_body_and_endpoints() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_template::result::EqualitySearchProofByTemplateObjectDefinition,
    };
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        compiler.compile_run(&run, "baseline").unwrap();
        let fact = super::fact_statement_mut(&mut run.statement_results[1]);
        let equal = super::equality_proof_mut(&mut fact.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByTemplate(
                EqualitySearchProofByTemplateObjectDefinition::HaveFnByInducApplication(proof),
            ),
        ) = &mut equal.searched_proof
        else {
            panic!("actual recursive template unfold")
        };
        match mutation {
            0 => proof.selected_case_path.clear(),
            1 => proof.selected_case_path[0].case_index = usize::MAX,
            2 => proof.selected_case_path[0].case_index = 1,
            3 => proof.expanded_body = super::number_object("99"),
            4 => {
                super::equality_proof_mut(&mut proof.residual_equal)
                    .fact
                    .right = super::number_object("99")
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_recursive_unfold")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn recursive_guard_constructor_requires_completed_original_coverage() {
    let (mut run, compiler) = super::execute(SOURCES[4]);
    let p = template(&mut run);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(body),
    )) = p.body.as_ref()
    else {
        panic!("recursive body")
    };
    let header = SourcePosition::new(None, SourceOwner::Template(p), 1);
    let before = SourcePosition::new(Some(&header), SourceOwner::RecursiveFunction(body), 7);
    let after = SourcePosition {
        before: 8,
        ..before
    };
    let one = super::number_object("1");
    assert!(before
        .with_visible_wd(&one, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    let checked = after
        .with_visible_wd(&one, &mut |wd, site| compiler.compile_wd(wd, site))
        .unwrap();
    assert!(checked.is_some());
}
