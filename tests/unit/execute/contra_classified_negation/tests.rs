use super::negate_fact_for_contra;
use crate::ast::fact::{AtomicFact, ExistOrAndChainAtomicFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_by_stmt::{ExecByContraStmtResult, ExecByStmtResult};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[test]
fn classified_negations_obey_the_boolean_truth_table() {
    for mask in 0..16 {
        let mut rt = runtime();
        let bits: Vec<_> = (0..4).map(|i| (mask >> i) & 1).collect();
        let code = format!(
            "{} = 1 and {} = 1 or {} = 1 and {} = 1",
            bits[0], bits[1], bits[2], bits[3]
        );
        let goal = fact(&mut rt, &code);
        let negated = negate_fact_for_contra(&mut rt, &goal).unwrap();
        let expected = !((bits[0] == 1 && bits[1] == 1) || (bits[2] == 1 && bits[3] == 1));
        let proof = rt.verify_fact(&negated, VerifyState::top_level()).unwrap();
        assert_eq!(!proof.is_failed(), expected, "{code}");
        assert_ne!(goal.fact_id(), negated.fact_id());
        let twice = negate_fact_for_contra(&mut rt, &negated).unwrap();
        let proof = rt.verify_fact(&twice, VerifyState::top_level()).unwrap();
        assert_eq!(!proof.is_failed(), !expected, "double negation: {code}");
    }
}

#[test]
fn conjunctions_and_chains_negate_every_component() {
    for first in 0..2 {
        for second in 0..2 {
            let mut rt = runtime();
            let source = format!("{first} = 1 and {second} = 1");
            let goal = fact(&mut rt, &source);
            let negated = negate_fact_for_contra(&mut rt, &goal).unwrap();
            let proof = rt.verify_fact(&negated, VerifyState::top_level()).unwrap();
            assert_eq!(!proof.is_failed(), first != 1 || second != 1, "{source}");
        }
    }
    for source in ["0 = 0 = 0", "0 = 0 = 1", "0 = 1 = 1", "0 = 1 = 0"] {
        let mut rt = runtime();
        let goal = fact(&mut rt, source);
        let negated = negate_fact_for_contra(&mut rt, &goal).unwrap();
        let proof = rt.verify_fact(&negated, VerifyState::top_level()).unwrap();
        assert_eq!(!proof.is_failed(), source != "0 = 0 = 0", "{source}");
    }
}

#[test]
fn existence_goal_uses_negative_existence_as_its_reverse_assumption() {
    check(
        &mut runtime(),
        "by contra:\n    ? exist x {0} st {x = 0}\n    impossible 0 = 0",
        &[true],
    );
    check(
        &mut runtime(),
        "by contra:\n    ? exist x {0} st {x = 1}\n    impossible 0 = 1",
        &[false],
    );
}

#[test]
fn whole_not_forall_body_uses_one_counterexample_disjunction() {
    check(
        &mut runtime(),
        "witness exist x {0} st {x != 0 or x != 1} from 0\nnot forall x {0}:\n    x = 0\n    x = 1",
        &[true, true],
    );
    check(
        &mut runtime(),
        "witness exist x {0} st {x != 1} from 0\nnot forall x {0}:\n    x = 0",
        &[true, false],
    );
}

#[test]
fn previously_accepted_counterexample_clause_shapes_remain_usable() {
    check(&mut runtime(), "witness exist x {0} st {x != 1 or x != 2, x != 3 or x != 4} from 0\nnot forall x {0}:\n    x = 1 and x = 2 or x = 3 and x = 4", &[true, true]);
}

#[test]
fn enumeration_then_contra_proves_k005_and_retains_scoped_evidence() {
    let mut rt = runtime();
    let run = rt.run_litex_code("by enumerate finite_set:\n    ? forall x {0}:\n        x != 1\nby contra:\n    ? not exist x {0} st {x = 1}\n    obtain a from exist x {0} st {x = 1}\n    a != 1\n    impossible a = 1").unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(s))) =
        &run.statement_results[1]
    else {
        panic!("contra success");
    };
    assert!(matches!(s.reverse_assumption, Fact::ExistFact(_)));
    assert_ne!(s.goal.fact_id(), s.reverse_assumption_fact_id);
    assert!(s
        .local_env
        .facts
        .facts_by_id
        .contains_key(&s.reverse_assumption_fact_id));
    assert!(!rt.execution_environments_stack[0]
        .facts
        .facts_by_id
        .contains_key(&s.reverse_assumption_fact_id));
    check(&mut rt, "not exist x {0} st {x = 1}", &[true]);
    let leaked = rt.run_litex_code("a = 1").unwrap();
    assert!(!leaked.success);
    check(&mut rt, "have a R = 2", &[true]);
}

#[test]
fn false_not_exist_and_failed_witness_steps_do_not_commit_assumptions() {
    let mut rt = runtime();
    check(&mut rt, "by contra:\n    ? not exist x {0} st {x = 0}\n    obtain a from exist x {0} st {x = 0}\n    impossible a = 0", &[false]);
    check(&mut rt, "not exist x {0} st {x = 0}", &[false]);
    check(&mut rt, "have a R = 2", &[true]);
    let mut rt = runtime();
    check(&mut rt, "by contra:\n    ? not exist x {0} st {x = 1}\n    obtain b from exist x {1} st {x = 1}\n    impossible b = 1", &[false]);
    check(&mut rt, "have b R = 2", &[true]);
}

#[test]
fn forall_and_not_forall_reverse_assumptions_preserve_whole_formulas() {
    check(&mut runtime(), "forall z {0}:\n    z = 0\nby contra:\n    ? forall x {0}:\n        x = 0\n    obtain a from exist y {0} st {y != 0}\n    a = 0\n    impossible a != 0", &[true, true]);
    check(
        &mut runtime(),
        "by contra:\n    ? not forall x {0}:\n        x = 1\n    impossible 0 = 1",
        &[true],
    );
    check(&mut runtime(), "by contra:\n    ? forall x {0}:\n        x = 0\n        x = 1\n    obtain a from exist y {0} st {y != 0}\n    impossible a != 0", &[false]);
}

#[test]
fn disjunction_goals_assume_every_negated_branch() {
    check(
        &mut runtime(),
        "by contra:\n    ? 1 = 1 or 0 = 1\n    impossible 1 != 1",
        &[true],
    );
    check(
        &mut runtime(),
        "by contra:\n    ? 1 = 2 or 0 = 1\n    impossible 1 != 2",
        &[false],
    );
}

#[test]
fn missing_classified_shapes_are_rejected_without_a_generic_not() {
    for source in [
        "forall x {0}:\n    exist y {0} st {y = x}",
        "forall x {0}:\n    =>:\n        exist y {0} st {y = x}\n    <=>:\n        x = 0",
    ] {
        let mut rt = runtime();
        let goal = fact(&mut rt, source);
        assert!(negate_fact_for_contra(&mut rt, &goal).is_err(), "{source}");
    }
}

#[test]
fn unique_existence_contra_rejects_zero_and_multiple_witnesses() {
    check(&mut runtime(), "by contra:\n    ? exist! x {0} st {x = 0}\n    obtain a from exist y {0} st {y = 0, y != 0}\n    impossible a != 0", &[true]);
    check(
        &mut runtime(),
        "by contra:\n    ? exist! x {0} st {x = 1}\n    impossible 0 = 0",
        &[false],
    );
    check(
        &mut runtime(),
        "by contra:\n    ? exist! x {0, 1} st {x = x}\n    impossible 0 = 0",
        &[false],
    );
}

#[test]
fn unique_negation_has_the_correct_finite_model_and_fresh_second_binder() {
    for (predicate, expected) in [("x = 2", true), ("x = 0", false), ("x = x", true)] {
        let mut rt = runtime();
        let goal = fact(&mut rt, &format!("exist! x {{0, 1}} st {{{predicate}}}"));
        let negated = negate_fact_for_contra(&mut rt, &goal).unwrap();
        let Fact::ForallFact(forall) = &negated else {
            panic!("classified forall");
        };
        let ExistOrAndChainAtomicFact::ExistFact(other) = &forall.then_facts[0] else {
            panic!("second candidate");
        };
        let original = forall.typed_parameters.groups[0].params[0].id;
        let fresh = other.typed_parameters.groups[0].params[0].id;
        assert_ne!(original, fresh);
        let mut holds = true;
        for candidate in 0..2 {
            let mut subst = std::collections::HashMap::new();
            subst.insert(original, number(&mut rt, candidate));
            let mut satisfies = true;
            for premise in &forall.dom_facts {
                let inst = rt.inst_fact(premise, &subst).unwrap();
                satisfies &= !rt
                    .verify_fact(&inst, VerifyState::top_level())
                    .unwrap()
                    .is_failed();
            }
            if !satisfies {
                continue;
            }
            let mut has_alternative = false;
            for value in 0..2 {
                subst.insert(fresh, number(&mut rt, value));
                let mut valid = true;
                for body in &other.facts {
                    let inst = rt.inst_quantifier_free_fact(body, &subst).unwrap();
                    let inst = crate::instantiate::quantifier_free_fact_to_fact(inst);
                    valid &= !rt
                        .verify_fact(&inst, VerifyState::top_level())
                        .unwrap()
                        .is_failed();
                }
                has_alternative |= valid;
            }
            holds &= has_alternative;
        }
        assert_eq!(holds, expected, "{predicate}");
    }
}

fn number(rt: &mut Runtime, value: u8) -> crate::ast::obj::Obj {
    let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = fact(rt, &format!("{value} = {value}"))
    else {
        panic!("number");
    };
    equal.left
}

#[test]
fn unique_negation_preserves_dependent_carriers_and_any_different_component() {
    let mut rt = runtime();
    let goal = fact(&mut rt, "exist! a {0}, b {a} st {b = a}");
    let Fact::ExistUniqueFact(original) = &goal else {
        panic!("unique");
    };
    let negated = negate_fact_for_contra(&mut rt, &goal).unwrap();
    let Fact::ForallFact(forall) = negated else {
        panic!("forall");
    };
    let ExistOrAndChainAtomicFact::ExistFact(other) = &forall.then_facts[0] else {
        panic!("alternative");
    };
    let mut subst = std::collections::HashMap::new();
    subst.insert(
        original.typed_parameters.groups[0].params[0].id,
        crate::ast::obj::Obj::Identifier(crate::ast::obj::IdentifierObj::from_bound_name(
            &other.typed_parameters.groups[0].params[0],
        )),
    );
    assert_eq!(
        other.typed_parameters.groups[1].param_type,
        rt.inst_param_type(&original.typed_parameters.groups[1].param_type, &subst)
            .unwrap()
    );
    let different = other.facts.last().unwrap();
    for (first, expected) in [(0, false), (1, true)] {
        let mut values = std::collections::HashMap::new();
        for group in &original.typed_parameters.groups {
            for binder in &group.params {
                values.insert(binder.id, number(&mut rt, 0));
            }
        }
        values.insert(
            other.typed_parameters.groups[0].params[0].id,
            number(&mut rt, first),
        );
        values.insert(
            other.typed_parameters.groups[1].params[0].id,
            number(&mut rt, 0),
        );
        let inst = rt.inst_quantifier_free_fact(different, &values).unwrap();
        let inst = crate::instantiate::quantifier_free_fact_to_fact(inst);
        assert_eq!(
            !rt.verify_fact(&inst, VerifyState::top_level())
                .unwrap()
                .is_failed(),
            expected
        );
    }
}

#[test]
fn iff_negation_checks_the_complete_equivalence_truth_table() {
    for mask in 0..16 {
        let mut rt = runtime();
        let bits: Vec<_> = (0..4).map(|i| (mask >> i) & 1).collect();
        let source = format!("forall x {{0}}:\n    =>:\n        {} = 1\n        {} = 1\n    <=>:\n        {} = 1\n        {} = 1", bits[0], bits[1], bits[2], bits[3]);
        let goal = fact(&mut rt, &source);
        let negated = negate_fact_for_contra(&mut rt, &goal).unwrap();
        let Fact::ExistFact(counterexample) = negated else {
            panic!("classified iff counterexample");
        };
        let mut holds = true;
        for body in &counterexample.facts {
            let body = crate::instantiate::quantifier_free_fact_to_fact(body.clone());
            holds &= !rt
                .verify_fact(&body, VerifyState::top_level())
                .unwrap()
                .is_failed();
        }
        let left = bits[0] == 1 && bits[1] == 1;
        let right = bits[2] == 1 && bits[3] == 1;
        assert_eq!(holds, left != right, "{source}");
    }
}

#[test]
fn forall_iff_goal_parses_and_closes_with_classified_counterexample() {
    check(&mut runtime(), "by contra:\n    ? forall x {0}:\n        =>:\n            0 = 0\n        <=>:\n            0 = 0\n    obtain a from exist y {0} st {0 != 0 or 0 != 0, 0 = 0 or 0 = 0}\n    by cases:\n        ? 0 != 0\n        case 0 != 0\n        case 0 != 0\n    impossible 0 != 0", &[true]);
    check(&mut runtime(), "by contra:\n    ? forall x {0}:\n        =>:\n            0 = 0\n        <=>:\n            0 = 1\n    impossible 0 = 0", &[false]);
    let run = runtime()
        .run_litex_code("by contra:\n    ? 0 = 0:\n        0 = 0\n    impossible 0 != 0")
        .unwrap();
    assert!(!run.success);
    assert!(run.session_error.is_some());
    assert!(run.statement_results.is_empty());
}

#[test]
fn conjunction_of_disjunctions_does_not_expand_through_both_normal_forms() {
    let mut rt = runtime();
    let mut parts = Vec::new();
    for i in 0..8 {
        let goal = fact(&mut rt, &format!("{i} = 0 or {i} = 1"));
        parts.push(super::as_quantifier_free(&goal).unwrap());
    }
    let negated = rt
        .negate_quantifier_free_conjunction(&parts, None)
        .unwrap()
        .unwrap();
    let Fact::OrFact(or) = crate::instantiate::quantifier_free_fact_to_fact(negated.clone()) else {
        panic!("DNF");
    };
    assert_eq!(or.facts.len(), 8);
    assert!(!rt
        .verify_fact(
            &crate::instantiate::quantifier_free_fact_to_fact(negated),
            VerifyState::top_level()
        )
        .unwrap()
        .is_failed());
    let body = rt
        .negate_quantifier_free_conjunction_to_conjuncts(&parts, None)
        .unwrap()
        .unwrap();
    assert_eq!(body.len(), 1);
}

#[test]
fn iff_counterexample_keeps_many_conjuncts_compact() {
    let mut rt = runtime();
    let clauses = (0..8)
        .map(|_| "            0 = 0 or 0 = 1")
        .collect::<Vec<_>>()
        .join("\n");
    let source = format!("forall x {{0}}:\n    =>:\n{clauses}\n    <=>:\n{clauses}");
    let goal = fact(&mut rt, &source);
    let Fact::ExistFact(counterexample) = negate_fact_for_contra(&mut rt, &goal).unwrap() else {
        panic!("counterexample");
    };
    assert!(counterexample.facts.len() <= 65);
    let mut holds = true;
    for body in counterexample.facts {
        let body = crate::instantiate::quantifier_free_fact_to_fact(body);
        holds &= !rt
            .verify_fact(&body, VerifyState::top_level())
            .unwrap()
            .is_failed();
    }
    assert!(!holds);
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn fact(rt: &mut Runtime, source: &str) -> Fact {
    let tokens = Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(f) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact");
    };
    f
}

fn check(rt: &mut Runtime, code: &str, expected: &[bool]) {
    let run = rt.run_litex_code(code).unwrap();
    assert!(
        run.session_error.is_none(),
        "{code}: {:?}",
        run.session_error
    );
    assert_eq!(
        run.statement_results
            .iter()
            .map(|s| !s.is_failed())
            .collect::<Vec<_>>(),
        expected,
        "{code}"
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}
