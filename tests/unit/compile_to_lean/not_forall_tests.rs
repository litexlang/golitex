use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{
    ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByStmtResult,
};
use crate::execute::execute_fact_stmt::verify_not_forall_fact::VerifyNotForallFactResult;
use crate::execute::execute_fact_stmt::verify_not_forall_fact::VerifyNotForallFactSuccess;
use crate::prelude::*;
use crate::store_fact_and_infer::InferResult;

const SIMPLE: &str = include_str!("../../../lean/examples/not_every_element_is_one/statement.lit");
const GUARDED: &str =
    include_str!("../../../lean/examples/reciprocal_counterexample/statement.lit");
const CONTRA_GUARDED: &str =
    include_str!("../../../lean/examples/contradiction_with_reciprocal_guard/statement.lit");

fn contra(run: &mut RunLitexCodeResult) -> &mut ExecByContraStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) =
        &mut run.statement_results[0]
    else {
        panic!("contra")
    };
    p
}

fn statement(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecFactStmtSuccessResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[index]
    else {
        panic!("fact")
    };
    p
}
fn negative(statement: &mut ExecFactStmtSuccessResult) -> &mut VerifyNotForallFactSuccess {
    let VerifyFactResult::NotForall(p) = &mut statement.verify_result else {
        panic!("not forall")
    };
    let VerifyNotForallFactResult::Success(p) = p.as_mut() else {
        panic!("success")
    };
    p
}
fn plain(fact: &mut ExistShapedFact) -> &mut PlainExistFact {
    let ExistShapedFact::Exist(fact) = fact else {
        panic!("plain exist")
    };
    fact
}
fn child(proof: &mut VerifyNotForallFactSuccess) -> &mut VerifyPlainExistFactSuccess {
    let VerifyFactResult::ExistShapedFact(p) = &mut proof.prove_derived_exist else {
        panic!("exist")
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
        p.as_mut()
    else {
        panic!("success")
    };
    p
}

#[test]
fn negated_universal_replays_witness_guards_cnf_dnf_and_real_line_routes() {
    for source in [
        SIMPLE,
        GUARDED,
        include_str!("../../../lean/examples/incompatible_universal_equalities/statement.lit"),
        include_str!("../../../lean/examples/alternatives_counterexample/statement.lit"),
        include_str!("../../../lean/examples/real_counterexamples/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "counterexamples").unwrap();
        assert!(output.contains("¬ (∀ (_value_i"));
        assert!(output.contains("_counterexample"));
        assert!(!output.contains("sorry"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "counterexamples").unwrap()
        );
    }
}

#[test]
fn negated_universal_rejects_changed_binders_domains_body_and_child_subject() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(GUARDED);
        let proof = negative(statement(&mut run, 1));
        match mutation {
            0 => {
                plain(&mut proof.derived_exist).typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            1 => {
                plain(&mut proof.derived_exist).facts.remove(0);
            }
            2 => plain(&mut proof.derived_exist).facts.swap(0, 1),
            3 => plain(&mut proof.derived_exist).facts[1] = proof.fact.then_facts[0].clone(),
            4 => proof.fact.then_facts.clear(),
            5 => plain(&mut child(proof).fact).facts.clear(),
            6 => child(proof)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .assumed_body_facts
                .clear(),
            7 => child(proof)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .defined_params
                .stored_fact_ids
                .clear(),
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_counterexample")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn negated_universal_inference_checks_subject_and_publication_scope() {
    let (mut run, compiler) = super::execute(SIMPLE);
    let stored = &statement(&mut run, 1).store_and_infer_result;
    let Some(InferResult::NotForall(infer)) = &stored.infer else {
        panic!("inference")
    };
    let id = infer.derived_exist.store.primary_fact_id();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler.cited_fact_reference(id, &before).is_err());
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    assert!(compiler
        .cited_fact_reference(id, &after)
        .unwrap()
        .1
        .contains(&format!("h_{}", id.value())));
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(SIMPLE);
        let stored = &mut statement(&mut run, 1).store_and_infer_result;
        let Some(InferResult::NotForall(infer)) = &mut stored.infer else {
            panic!("inference")
        };
        let StoreFactResult::ExistShapedFact(p) = &mut infer.derived_exist.store else {
            panic!("exist")
        };
        match mutation {
            0 => plain(&mut p.fact).facts.clear(),
            1 => {
                plain(&mut p.fact).typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R))
            }
            2 => stored.infer = None,
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "corrupt_inference").is_err());
    }
}

#[test]
fn true_universal_and_missing_reciprocal_guard_are_not_counterexamples() {
    for source in [
        "not forall x R:\n    x = x\n",
        "not forall x R:\n    1 / x = 2\n",
    ] {
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
    }
}

#[test]
fn negated_universal_assumptions_and_contra_replay_without_fabricated_exist_wd() {
    for source in [
        CONTRA_GUARDED,
        include_str!("../../../lean/examples/contradiction_to_reflexivity/statement.lit"),
        include_str!("../../../lean/examples/contradiction_to_counterexample/statement.lit"),
        include_str!("../../../lean/examples/negated_universal_premise/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "quantified_contra").unwrap();
        assert!(output.contains("_counterexample"));
        assert!(!output.contains("sorry"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "quantified_contra").unwrap()
        );
    }
}

#[test]
fn quantified_contra_rejects_changed_subject_formation_and_inference() {
    for mutation in 0..9 {
        let (mut run, compiler) = super::execute(CONTRA_GUARDED);
        let p = contra(&mut run);
        match mutation {
            0 => p.reverse_assumption_fact_id = p.goal.fact_id(),
            1 | 2 => {
                let Fact::NotForall(f) = &mut p.reverse_assumption else {
                    panic!()
                };
                if mutation == 1 {
                    f.dom_facts.clear();
                } else {
                    f.then_facts = f.dom_facts.clone();
                }
            }
            3..=6 => {
                let FactWellDefinedProof::NotForall(wd) = &mut p.reverse_assumption_wd else {
                    panic!()
                };
                match mutation {
                    3 => wd.as_detailed_mut().unwrap().then.clear(),
                    4 => wd.as_detailed_mut().unwrap().assumed_dom_facts.clear(),
                    5 => wd
                        .as_detailed_mut()
                        .unwrap()
                        .introduced_params
                        .defined_params
                        .stored_fact_ids
                        .clear(),
                    6 => wd
                        .as_detailed_mut()
                        .unwrap()
                        .introduced_params
                        .param_type_well_defined
                        .clear(),
                    _ => unreachable!(),
                }
            }
            7 => p.negation_assumed.infer = None,
            8 => {
                let Some(InferResult::NotForall(infer)) = &mut p.negation_assumed.infer else {
                    panic!()
                };
                let StoreFactResult::ExistShapedFact(stored) = &mut infer.derived_exist.store
                else {
                    panic!()
                };
                plain(&mut stored.fact).facts.clear();
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_quantified_contra")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn quantified_contra_publishes_goal_but_not_hypothetical_parameters_or_counterexample() {
    let (mut run, compiler) = super::execute(CONTRA_GUARDED);
    let p = contra(&mut run);
    let public_id = p.goal.fact_id();
    let assumption = p.reverse_assumption_fact_id;
    let Some(InferResult::NotForall(infer)) = &p.negation_assumed.infer else {
        panic!()
    };
    let counterexample = infer.derived_exist.store.primary_fact_id();
    let Fact::NotForall(fact) = &p.reverse_assumption else {
        panic!()
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equality)) = &fact.then_facts[0]
    else {
        panic!()
    };
    let private_reciprocal = equality.left.clone();
    let FactWellDefinedProof::NotForall(wd) = &p.reverse_assumption_wd else {
        panic!()
    };
    let member = wd
        .detailed_ref()
        .introduced_params
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id();
    let guard = wd.detailed_ref().assumed_dom_facts[0]
        .store_and_infer
        .primary_fact_id();
    let scope = SourcePosition::new(None, SourceOwner::Contra(p), 1);
    for id in [assumption, counterexample] {
        assert!(compiler.cited_fact_reference(id, &scope).is_err());
        assert!(compiler
            .cited_fact_reference(id, &SourcePosition { before: 2, ..scope })
            .is_ok());
    }
    let formation = SourcePosition::new(Some(&scope), SourceOwner::NotForallWD(fact, wd), 0);
    for (stage, id) in [(1, member), (2, guard)] {
        assert!(compiler
            .cited_fact_reference(
                id,
                &SourcePosition {
                    before: stage - 1,
                    ..formation
                }
            )
            .is_err());
        assert!(compiler
            .cited_fact_reference(
                id,
                &SourcePosition {
                    before: stage,
                    ..formation
                }
            )
            .is_ok());
        assert!(compiler
            .cited_fact_reference(
                id,
                &SourcePosition {
                    before: usize::MAX,
                    ..scope
                }
            )
            .is_err());
    }
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(compiler.cited_fact_reference(public_id, &before).is_err());
    assert!(compiler.cited_fact_reference(public_id, &after).is_ok());
    for id in [assumption, counterexample, member, guard] {
        assert!(compiler.cited_fact_reference(id, &after).is_err());
    }
    assert!(compiler
        .compile_object_reference(&private_reciprocal, &after)
        .is_err());
}

#[test]
fn negated_universal_matching_rejects_free_input_capture_and_changed_carrier() {
    let (run, _) = super::execute(include_str!(
        "../../../lean/examples/negated_universal_premise/statement.lit"
    ));
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &run.statement_results[0]
    else {
        panic!()
    };
    let Fact::ForallFact(fact) = &p.statement.fact else {
        panic!()
    };
    let Fact::NotForall(source) = &fact.dom_facts[0] else {
        panic!()
    };
    let input = &fact.typed_parameters.groups[0].params[0];
    let original = Fact::NotForall(source.clone());
    let substitution = std::collections::HashMap::from([(
        input.id,
        Obj::Identifier(IdentifierObj::from_bound_name(input)),
    )]);
    assert!(super::super::helper::instantiated_fact_matches(
        &original,
        &original,
        &substitution
    ));
    let mut captured = source.clone();
    captured.typed_parameters.groups[0].params[0] = input.clone();
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut captured.then_facts[0]
    else {
        panic!()
    };
    eq.left = Obj::Identifier(IdentifierObj::from_bound_name(input));
    assert!(!super::super::helper::instantiated_fact_matches(
        &original,
        &Fact::NotForall(captured),
        &substitution
    ));
    let mut changed = source.clone();
    changed.typed_parameters.groups[0].param_type =
        ParamType::Obj(Obj::StandardSet(StandardSet::R));
    assert!(!super::super::helper::instantiated_fact_matches(
        &original,
        &Fact::NotForall(changed),
        &substitution
    ));
}

#[test]
fn quantified_contra_does_not_admit_false_goals_or_missing_guards() {
    for source in [
        "by contra:\n    ? forall x R:\n        x != x\n    impossible 0 = 1\n",
        "by contra:\n    ? not forall x R:\n        x = x\n    impossible 0 = 1\n",
        "by contra:\n    ? forall x R:\n        1 / x = 1 / x\n    impossible 0 = 1\n",
    ] {
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}
