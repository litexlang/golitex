use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_by_stmt::{
    ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByStmtResult,
};
use crate::prelude::*;

const SINGLE: &str =
    include_str!("../../../lean/examples/unique_singleton_by_contradiction/statement.lit");
const PAIR: &str =
    include_str!("../../../lean/examples/unique_pair_by_contradiction/statement.lit");
const GUARDED: &str =
    include_str!("../../../lean/examples/unique_guarded_value_by_contradiction/statement.lit");
const DEPENDENT: &str =
    include_str!("../../../lean/examples/unique_dependent_pair_by_contradiction/statement.lit");
const GENERIC: &str =
    include_str!("../../../lean/examples/unique_copy_by_contradiction/statement.lit");

fn contra(run: &mut RunLitexCodeResult) -> &mut ExecByContraStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) =
        &mut run.statement_results[0]
    else {
        panic!("contra")
    };
    p
}

#[test]
fn unique_contra_replays_single_pair_guard_and_generic_theorem() {
    for source in [
        SINGLE,
        PAIR,
        GUARDED,
        DEPENDENT,
        GENERIC,
        include_str!("../../../lean/examples/unique_set_copy_by_contradiction/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "unique_contra").unwrap();
        assert!(output.contains("_no_alternative"));
        assert!(output.contains("Litex.semanticObject"));
        assert!(!output.contains("sorry"));
        assert_eq!(output, compiler.compile_run(&run, "unique_contra").unwrap());
        if source == PAIR {
            assert!(output.contains("Litex.FiniteFunction.tupleValue"));
            assert!(output.contains("Or.inl _different"));
            assert!(output.contains("Or.inr _different"));
        }
    }
}

#[test]
fn unique_contra_preserves_dependent_carriers_and_free_inputs() {
    let (mut run, compiler) = super::execute(DEPENDENT);
    let p = contra(&mut run);
    let Fact::ExistUniqueFact(source) = &p.goal else {
        panic!()
    };
    let Fact::ForallFact(reverse) = &mut p.reverse_assumption else {
        panic!()
    };
    let ExistOrAndChainAtomicFact::ExistFact(other) = &mut reverse.then_facts[0] else {
        panic!()
    };
    // The second candidate's carrier must refer to its own first coordinate.
    other.typed_parameters.groups[1].param_type =
        source.typed_parameters.groups[1].param_type.clone();
    assert!(compiler
        .compile_run(&run, "wrong_dependent_carrier")
        .is_err());

    let (mut run, compiler) = super::execute(GENERIC);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let Fact::ForallFact(fact) = &named.statement.fact else {
        panic!()
    };
    let input = &fact.typed_parameters.groups[0].params[0];
    let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
        panic!()
    };
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(p))) =
        &mut body.proof_steps[0]
    else {
        panic!()
    };
    let Fact::ForallFact(reverse) = &mut p.reverse_assumption else {
        panic!()
    };
    let ExistOrAndChainAtomicFact::ExistFact(other) = &mut reverse.then_facts[0] else {
        panic!()
    };
    other.typed_parameters.groups[0].params[0] = input.clone();
    let input = Obj::Identifier(IdentifierObj::from_bound_name(input));
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut other.facts[0] else {
        panic!()
    };
    eq.left = input.clone();
    let QuantifierFreeFact::AtomicFact(AtomicFact::NotEqualFact(ne)) =
        other.facts.last_mut().unwrap()
    else {
        panic!()
    };
    ne.left = input;
    assert!(compiler.compile_run(&run, "captured_free_input").is_err());
}

#[test]
fn unique_contra_rejects_changed_alternative_binders_carriers_body_or_difference() {
    for mutation in 0..9 {
        let (mut run, compiler) = super::execute(PAIR);
        let p = contra(&mut run);
        let Fact::ForallFact(reverse) = &mut p.reverse_assumption else {
            panic!()
        };
        match mutation {
            0 => reverse.dom_facts.clear(),
            1 => {
                reverse.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            2..=8 => {
                let ExistOrAndChainAtomicFact::ExistFact(other) = &mut reverse.then_facts[0] else {
                    panic!()
                };
                match mutation {
                    2 => {
                        other.typed_parameters.groups[0].params[0].id =
                            reverse.typed_parameters.groups[0].params[0].id
                    }
                    3 => {
                        other.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::C))
                    }
                    4 => {
                        other.facts.remove(0);
                    }
                    5 => other.facts.swap(0, 1),
                    6 => other.fact_id = reverse.fact_id,
                    7 | 8 => {
                        let QuantifierFreeFact::OrFact(or) = other.facts.last_mut().unwrap() else {
                            panic!()
                        };
                        if mutation == 7 {
                            or.facts.swap(0, 1);
                        } else {
                            let AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(ne)) =
                                &mut or.facts[0]
                            else {
                                panic!()
                            };
                            std::mem::swap(&mut ne.left, &mut ne.right);
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "corrupt_unique_contra").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn unique_contra_requires_original_goal_and_alternative_formation() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(GUARDED);
        let p = contra(&mut run);
        match mutation {
            0 => {
                let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ExistFact(wd)) =
                    &mut p.goal_wd
                else {
                    panic!()
                };
                wd.assumed_body_facts.clear();
            }
            1..=3 => {
                let FactWellDefinedProof::ForallFact(wd) = &mut p.reverse_assumption_wd else {
                    panic!()
                };
                match mutation {
                    1 => wd.assumed_dom_facts.clear(),
                    2 => wd.introduced_params.defined_params.stored_fact_ids.clear(),
                    3 => wd.then.clear(),
                    _ => unreachable!(),
                }
            }
            4 => p.reverse_assumption_fact_id = p.goal.fact_id(),
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupt_unique_formation")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn unique_contra_keeps_candidate_assumptions_private() {
    let (mut run, compiler) = super::execute(GUARDED);
    let p = contra(&mut run);
    let goal = p.goal.fact_id();
    let assumption = p.reverse_assumption_fact_id;
    let Fact::ForallFact(fact) = &p.reverse_assumption else {
        panic!()
    };
    let FactWellDefinedProof::ForallFact(wd) = &p.reverse_assumption_wd else {
        panic!()
    };
    let member = wd.introduced_params.defined_params.store_and_infer_results[0].primary_fact_id();
    let guard = fact.dom_facts[0].fact_id();
    let scope = SourcePosition::new(None, SourceOwner::Contra(p), 1);
    assert!(compiler.cited_fact_reference(assumption, &scope).is_err());
    assert!(compiler
        .cited_fact_reference(assumption, &SourcePosition { before: 2, ..scope })
        .is_ok());
    let formation = SourcePosition::new(Some(&scope), SourceOwner::ForallWD(fact, wd), 0);
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
    assert!(compiler.cited_fact_reference(goal, &before).is_err());
    assert!(compiler.cited_fact_reference(goal, &after).is_ok());
    for id in [assumption, member, guard] {
        assert!(compiler.cited_fact_reference(id, &after).is_err());
    }
}

#[test]
fn unique_contra_rejects_absent_nonunique_and_undefined_candidates() {
    for source in [
        "by contra:\n    ? exist! x {0} st {x = 1}\n    impossible 0 = 0\n",
        "by contra:\n    ? exist! x {0, 1} st {x = x}\n    impossible 0 = 0\n",
        "by contra:\n    ? exist! x R st {1 / x = 1}\n    impossible 0 = 0\n",
    ] {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        assert!(!runtime.run_litex_code(source).unwrap().success);
    }
}

#[test]
fn obtained_dependent_carrier_reuses_only_the_available_parameter_prefix() {
    let (mut run, compiler) = super::execute(DEPENDENT);
    let p = contra(&mut run);
    let statement = &p.proof_steps[0];
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::ObtainObjFromExistFact(
            crate::execute::ExecObtainObjFromExistFactStmtResult::Success(obtain),
        ),
    )) = statement
    else {
        panic!("obtain")
    };
    let StoreFactResult::AtomicFact(stored) =
        &obtain.store_and_infer_result.store_and_infer_results[1].store
    else {
        panic!()
    };
    let AtomicFact::InFact(member) = &stored.fact else {
        panic!()
    };
    let carrier = member.set.clone();
    let scope = SourcePosition::new(None, SourceOwner::Contra(p), 2);
    for before in [1, 2, 3] {
        let at = SourcePosition::new(Some(&scope), SourceOwner::Statement(statement), before);
        assert_eq!(
            compiler
                .compile_obtain_constructor_reference(&carrier, &at)
                .unwrap()
                .is_some(),
            before == 3
        );
    }
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler
        .compile_obtain_constructor_reference(&carrier, &outside)
        .unwrap()
        .is_none());
}
