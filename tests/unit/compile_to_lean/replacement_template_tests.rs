use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult,
    ExecHaveByReplacementAxiomStmtResult, ExecHaveByReplacementAxiomStmtSuccessResult,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/replacement_template_image/statement.lit"),
    include_str!("../../../lean/examples/guarded_replacement_template/statement.lit"),
    include_str!("../../../lean/examples/replacement_template_parameter_set/statement.lit"),
    include_str!("../../../lean/examples/local_replacement_witness/statement.lit"),
    include_str!("../../../lean/examples/captured_replacement_template/statement.lit"),
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

fn replacement(s: &mut ExecStmtResult) -> &mut ExecHaveByReplacementAxiomStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveByReplacementAxiom(
            ExecHaveByReplacementAxiomStmtResult::Success(p),
        ),
    )) = s
    else {
        panic!("replacement")
    };
    p
}

#[test]
fn replacement_templates_and_local_witnesses_replay_existing_evidence() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "replacement_contexts")
            .expect(source);
        assert!(lean.contains("Litex.replacement"));
        assert!(lean.contains("Litex.IndexedUnionSemantics M"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "replacement_contexts").unwrap()
        );
    }
}

#[test]
fn replacement_template_requires_exact_wd_uniqueness_and_store_capture() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let p = replacement(template(&mut run).body.as_mut());
        match mutation {
            0 => p.uniqueness_fact_id = FactId::new(u64::MAX),
            1 => {
                let VerifyObjWellDefinedResult::Success(wd) = &mut p.source_wd else {
                    panic!()
                };
                super::replace_wd_subject(wd, Obj::StandardSet(StandardSet::R));
            }
            2 => {
                p.stored_fact_ids.pop();
            }
            3 => {
                p.defined_params.store_and_infer_results.clear();
            }
            4 => {
                let StoreFactResult::ForallFact(s) = &mut p.introduction.store else {
                    panic!()
                };
                s.fact.dom_facts.clear();
            }
            5 => {
                let StoreFactResult::ForallFact(s) = &mut p.elimination.store else {
                    panic!()
                };
                s.fact.then_facts.clear();
            }
            6 => p.statement.name.id = IdentifierId::new(u64::MAX),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_replacement")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn replacement_template_publication_keeps_original_source_ids() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let p = template(&mut run);
        match mutation {
            0 => p.definition_facts[1].source_fact_id = p.definition_facts[0].source_fact_id,
            1 => {
                p.definition_facts.pop();
            }
            2 => {
                p.introduced_params
                    .defined_params
                    .store_and_infer_results
                    .clear();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_publication")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn local_replacement_and_stores_are_visible_only_after_the_original_step() {
    let (mut run, compiler) = super::execute(SOURCES[3]);
    let theorem = super::named_theorem_mut(&mut run.statement_results[2]);
    let ExecDefThmBodyProof::NonForall(body) = &mut theorem.body else {
        panic!()
    };
    let p = replacement(&mut body.proof_steps[0]);
    let object_id = p.statement.name.id;
    let fact_id = p.introduction.primary_fact_id();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &run.statement_results[2]
    else {
        panic!()
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let before = SourcePosition::new(Some(&outside), SourceOwner::Named(theorem), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(before.visible_replacement(object_id).is_none());
    assert!(before.visible_fact(fact_id, &compiler.runtime).is_err());
    assert!(after.visible_replacement(object_id).is_some());
    assert!(after.visible_fact(fact_id, &compiler.runtime).is_ok());
    let outside = SourcePosition {
        before: 3,
        ..outside
    };
    assert!(outside.visible_replacement(object_id).is_none());
    assert!(outside.visible_fact(fact_id, &compiler.runtime).is_err());
}

#[test]
fn local_replacement_must_match_the_recorded_source_step() {
    let (mut run, compiler) = super::execute(SOURCES[3]);
    let theorem = super::named_theorem_mut(&mut run.statement_results[2]);
    let ExecDefThmBodyProof::NonForall(body) = &mut theorem.body else {
        panic!()
    };
    replacement(&mut body.proof_steps[0]).statement.source_set = Obj::StandardSet(StandardSet::R);
    let error = compiler.compile_run(&run, "bad_local_step").unwrap_err();
    assert_eq!(error.route, "Theorem/ProofStepCapture");
}
