use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{
    ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByStmtResult,
};
use crate::prelude::*;
use crate::store_fact_and_infer::InferResult;

const FORALL: &str =
    include_str!("../../../lean/examples/universal_contradiction_closing/statement.lit");
const GUARDED: &str =
    include_str!("../../../lean/examples/guarded_universal_contradiction_closing/statement.lit");
const NEGATED: &str =
    include_str!("../../../lean/examples/counterexample_contradiction_closing/statement.lit");
const UNIQUE: &str =
    include_str!("../../../lean/examples/unique_contradiction_closing/statement.lit");
const PAIR: &str =
    include_str!("../../../lean/examples/unique_pair_contradiction_closing/statement.lit");
const NAMED: &str = include_str!("../../../lean/examples/named_counterexample/statement.lit");
const MIXED: &str =
    include_str!("../../../lean/examples/counterexample_after_universal_use/statement.lit");

fn contra(run: &mut RunLitexCodeResult) -> &mut ExecByContraStmtSuccess {
    run.statement_results
        .iter_mut()
        .find_map(|stmt| match stmt {
            ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) => {
                Some(p)
            }
            _ => None,
        })
        .expect("contra")
}

fn named(run: &mut RunLitexCodeResult) -> &mut ExecDefThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem")
    };
    p
}

#[test]
fn quantified_closings_replay_both_orientations_guards_and_unique_coordinates() {
    for source in [FORALL, GUARDED, NEGATED, UNIQUE, PAIR, NAMED, MIXED] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "logical_closing").unwrap();
        assert_eq!(
            output,
            compiler.compile_run(&run, "logical_closing").unwrap()
        );
        assert!(!output.contains("sorry"));
        if source == UNIQUE || source == PAIR {
            assert!(output.contains("_unique_exists"));
            assert!(output.contains("_alternative"));
        } else if source != NAMED {
            assert!(output.contains("_not_universal"));
        }
    }
}

#[test]
fn quantified_closing_requires_both_recorded_proofs_and_exact_citations() {
    for source in [FORALL, NEGATED, UNIQUE, PAIR] {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(source);
            let p = contra(&mut run);
            match mutation {
                0 => p.closing.impossible_fact = p.reverse_assumption.clone(),
                1 => std::mem::swap(&mut p.closing.impossible, &mut p.closing.negated_impossible),
                2 => p.closing.impossible_fact_id = Some(p.reverse_assumption_fact_id),
                3 => p.closing.negated_impossible_fact_id = Some(p.goal.fact_id()),
                _ => unreachable!(),
            }
            assert!(
                compiler.compile_run(&run, "corrupt_closing").is_err(),
                "mutation {mutation}: {source}"
            );
        }
    }
}

#[test]
fn canonical_local_forall_keeps_formation_and_reference_stage_boundaries() {
    let (mut run, compiler) = super::execute(MIXED);
    let p = contra(&mut run);
    let id = p.reverse_assumption_fact_id;
    let scope = SourcePosition::new(None, SourceOwner::Contra(p), 1);
    assert!(compiler.cited_fact_reference(id, &scope).is_err());
    let (_, reference) = compiler
        .cited_fact_reference(id, &SourcePosition { before: 2, ..scope })
        .unwrap();
    assert!(reference.contains(&format!("exact h_{} (Litex.semanticObject", id.value())));
    assert!(reference.contains("show ∀ {_Host_"));
    let after = SourcePosition::new(None, SourceOwner::Run(&run), usize::MAX);
    assert!(compiler.cited_fact_reference(id, &after).is_err());

    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(MIXED);
        let p = contra(&mut run);
        let FactWellDefinedProof::ForallFact(wd) = &mut p.reverse_assumption_wd else {
            panic!()
        };
        match mutation {
            0 => wd.as_detailed_mut().unwrap().then.clear(),
            1 => wd
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .param_type_well_defined
                .clear(),
            2 => wd
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .stored_fact_ids
                .clear(),
            3 => wd
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "missing_local_forall_formation")
            .is_err());
    }
}

#[test]
fn named_counterexample_requires_formation_and_derived_exist_capture() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(NAMED);
        let p = named(&mut run);
        match mutation {
            0 | 1 => {
                let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::NotForall(wd)) =
                    &mut p.goal_wd
                else {
                    panic!()
                };
                if mutation == 0 {
                    wd.as_detailed_mut().unwrap().then.clear();
                } else {
                    wd.as_detailed_mut()
                        .unwrap()
                        .introduced_params
                        .defined_params
                        .stored_fact_ids
                        .clear();
                }
            }
            2 => p.stored.infer = None,
            3 => {
                let Some(InferResult::NotForall(infer)) = &mut p.stored.infer else {
                    panic!()
                };
                let StoreFactResult::ExistShapedFact(stored) = &mut infer.derived_exist.store
                else {
                    panic!()
                };
                let ExistShapedFact::Exist(fact) = &mut stored.fact else {
                    panic!()
                };
                fact.facts.clear();
            }
            4 => {
                let ExecDefThmBodyProof::NonForall(body) = &mut p.body else {
                    panic!()
                };
                body.proof_steps.clear();
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_named_counterexample")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn named_counterexample_publishes_only_the_goal_and_its_inference() {
    let (mut run, compiler) = super::execute(NAMED);
    let p = named(&mut run);
    let goal = p.statement.fact.fact_id();
    let Some(InferResult::NotForall(infer)) = &p.stored.infer else {
        panic!()
    };
    let inferred = infer.derived_exist.store.primary_fact_id();
    let ExecDefThmBodyProof::NonForall(body) = &p.body else {
        panic!()
    };
    let ExecStmtResult::Witness(
        crate::execute::execute_witness_stmt::ExecWitnessStmtResult::WitnessExistFact(
            crate::execute::execute_witness_stmt::ExecWitnessExistFactStmtResult::Success(witness),
        ),
    ) = &body.proof_steps[0]
    else {
        panic!("private witness")
    };
    let private = witness.store_and_infer_result.primary_fact_id();
    let private_member = witness
        .introduced_params
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    for id in [goal, inferred] {
        assert!(compiler.cited_fact_reference(id, &before).is_err());
        assert!(compiler.cited_fact_reference(id, &after).is_ok());
    }
    for id in [private, private_member] {
        assert_ne!(id, goal);
        assert_ne!(id, inferred);
        assert!(compiler.cited_fact_reference(id, &after).is_err());
    }
}

#[test]
fn unsupported_false_closings_do_not_gain_proof_evidence() {
    for source in [
        "by contra:\n    ? forall x R:\n        x = 0\n    impossible forall y R:\n        y = 0\n",
        "by contra:\n    ? forall x R:\n        1 / x = 1 / x\n    impossible forall y R:\n        y = y\n",
        "by contra:\n    ? exist! x R st {x = x}\n    impossible exist! y R st {y = y}\n",
        "thm false_counterexample:\n    ? not forall x R:\n        x = x\n    0 = 0\n",
    ] {
        let mut runtime = Runtime::new_with_result_detail(LaunchCommand::Eval { code: String::new(), session: false,
            strict: true, language: OutputLanguage::English }, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}
