use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{
    ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByStmtResult,
};
use crate::prelude::*;
use crate::store_fact_and_infer::InferResult;

const FORALL: &str = r#"# Close a reflexivity proof with a universal formula and its counterexample.
by contra:
    ? forall x R:
        x = x
    impossible forall y R:
        y = y
"#;
const NEGATED: &str = r#"# Close a negated universal proof using its saved counterexample.
witness exist x {0} st {x != 1} from 0
by contra:
    ? not forall y {0}:
        y = 1
    impossible not forall z {0}:
        z = 1
"#;
const UNIQUE: &str = r#"# Use a unique-existence fact itself to close a contradiction.
witness exist! x {7} st {x = 7} from 7
by contra:
    ? exist! y {7} st {y = 7}
    impossible exist! z {7} st {z = 7}
"#;
const PAIR: &str = r#"# Close a unique-pair proof by contradicting a different alternative coordinate.
witness exist! x R, y R st {x = 0, y = 1} from 0, 1
by contra:
    ? exist! u R, v R st {u = 0, v = 1}
    impossible exist! a R, b R st {a = 0, b = 1}
"#;
const NAMED: &str = r#"# Save a negated universal theorem, invoke it and obtain its counterexample.
thm not_all_one:
    ? not forall x {0}:
        x = 1
    witness exist y {0} st {y != 1} from 0
by thm not_all_one
obtain a from exist y {0} st {y != 1}
a != 1
"#;
const MIXED: &str = r#"# Reuse a universal assumption at a number before closing with a counterexample.
witness exist x R st {x != 0} from 1
by contra:
    ? not forall y R:
        y = 0
    1 = 0
    impossible not forall z R:
        z = 0
"#;

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
