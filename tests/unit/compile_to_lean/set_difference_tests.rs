use crate::prelude::*;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::NotInFactSearchProofByBuiltinRule;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

const MEMBER: &str = include_str!("../../../lean/examples/set_difference_membership/statement.lit");
const NEGATIVE: &str =
    include_str!("../../../lean/examples/set_difference_exclusion/statement.lit");
const THEOREM: &str = include_str!("../../../lean/examples/set_difference_theorem/statement.lit");

#[test]
fn set_difference_replays_membership_exclusion_and_stored_projections() {
    for (source, laws) in [
        (MEMBER, vec!["inSetMinus_iff", "inInsert_iff"]),
        (
            NEGATIVE,
            vec![
                "notInSetMinusOfRight",
                "notInSetMinusOfLeft",
                "setMinusSubsetLeft",
            ],
        ),
        (THEOREM, vec!["inSetMinus_iff"]),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "difference").unwrap();
        assert!(lean.contains("Litex.setMinus "));
        for law in laws {
            assert!(lean.contains(&format!("Litex.{law} ")), "{law}");
        }
        assert_eq!(lean, compiler.compile_run(&run, "difference").unwrap());
    }
}

#[test]
fn set_difference_function_preserves_formation_and_expansion() {
    let source = include_str!("../../../lean/examples/set_difference_function/statement.lit");
    let (run, compiler) = super::execute(source);
    let lean = compiler.compile_run(&run, "difference_function").unwrap();
    assert!(lean.contains("Litex.setMinus "));
    // The recorded return proof now uses the known left-carrier equality.
    assert!(lean.contains("Litex.setMinusSubsetOfLeft "));
    assert!(lean.contains("Litex.subsetRefl "));
}

#[test]
fn set_difference_rejects_missing_reordered_or_extra_wd() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(MEMBER);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::SetMinus(p)),
            ..
        } = &mut p.well_defined_proof.well_defined_of_each_parameter[1]
        else {
            panic!()
        };
        match mutation {
            0 => {
                p.child_obj_well_defined.pop();
            }
            1 => p.child_obj_well_defined.swap(0, 1),
            2 => {
                let (mut extra, _) = super::execute("1 = 1");
                let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) =
                    extra.statement_results.remove(0)
                else {
                    panic!()
                };
                p.requirement_fact_verified.push(step.verify_result);
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_difference_wd").is_err());
    }
}

#[test]
fn set_difference_rejects_swapped_membership_children_and_future_citation() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(MEMBER);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let future = p.proved_then_facts[0].store_and_infer.primary_fact_id();
        let p = super::atomic_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::SetMinusMembership(p),
            ),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        match mutation {
            0 => std::mem::swap(
                &mut p.left_membership_proof,
                &mut p.right_non_membership_proof,
            ),
            1 => {
                let p = super::atomic_proof_mut(&mut p.right_non_membership_proof);
                let AtomicFact::NotInFact(p) = &mut p.fact else {
                    panic!()
                };
                p.element = super::number_object("17");
            }
            2 => {
                let p = super::atomic_proof_mut(&mut p.left_membership_proof);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
                    &mut p.searched_proof
                else {
                    panic!()
                };
                p.cite_fact_id = future;
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "bad_difference_children")
            .is_err());
    }
}

#[test]
fn set_difference_rejects_changed_negative_membership_premises() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(NEGATIVE);
        let p = super::forall_proof_mut(&mut run.statement_results[index]);
        let p = super::atomic_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let child = match &mut p.searched_proof {
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(
                    NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromRight(p),
                ),
            ) => &mut p.right_membership_proof,
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(
                    NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromLeft(p),
                ),
            ) => &mut p.left_non_membership_proof,
            _ => panic!(),
        };
        match &mut super::atomic_proof_mut(child).fact {
            AtomicFact::InFact(p) => p.set = super::number_object("17"),
            AtomicFact::NotInFact(p) => p.set = super::number_object("17"),
            _ => panic!(),
        }
        assert!(compiler
            .compile_run(&run, "bad_difference_exclusion")
            .is_err());
    }
}

#[test]
fn set_difference_rejects_swapped_inferred_stores_and_reused_ids() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(MEMBER);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
            &mut p.proved_then_facts[0].store_and_infer.infer
        else {
            panic!()
        };
        let p = rules
            .iter_mut()
            .find_map(|r| {
                if let InferInFactResult::SetMinusSplit(p) = r {
                    Some(p)
                } else {
                    None
                }
            })
            .unwrap();
        if mutation == 0 {
            std::mem::swap(&mut p.base_membership, &mut p.excluded_membership);
        } else {
            let reused = p.base_membership.primary_fact_id();
            let crate::store_fact_and_infer::StoreFactResult::AtomicFact(stored) =
                &mut p.excluded_membership.store
            else {
                panic!()
            };
            stored.fact_id = reused;
        }
        assert!(compiler.compile_run(&run, "bad_difference_stores").is_err());
    }
}

#[test]
fn set_difference_rejects_lost_singleton_projection() {
    let (mut run, compiler) = super::execute(
        "forall A set, b R, x A:\n    x != b\n    =>:\n        x $in set_minus(A, {b})\n",
    );
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
        &mut p.proved_then_facts[0].store_and_infer.infer
    else {
        panic!()
    };
    let p = rules
        .iter_mut()
        .find_map(|r| {
            if let InferInFactResult::SetMinusSplit(p) = r {
                Some(p)
            } else {
                None
            }
        })
        .unwrap();
    assert!(p.singleton_inequality.take().is_some());
    assert!(compiler
        .compile_run(&run, "missing_difference_inequality")
        .is_err());
}

#[test]
fn set_difference_strategy_rejects_missing_or_reordered_requirements() {
    use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(THEOREM);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[2]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
            panic!()
        };
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut body.proof_steps[0]
        else {
            panic!()
        };
        let p = super::atomic_proof_mut(&mut step.verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusMembership(p),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        match mutation {
            0 => {
                p.requirement_facts.pop();
            }
            1 => {
                p.proof_of_requirement_facts.pop();
            }
            2 => {
                p.requirement_facts.swap(0, 1);
                p.proof_of_requirement_facts.swap(0, 1);
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "bad_difference_strategy")
            .is_err());
    }
}

#[test]
fn set_difference_equalities_replay_both_orientations() {
    let cases = [
        ("set_minus(A, A) = {}", "setMinusSelf"),
        ("set_minus(A, {}) = A", "setMinusEmptyRight"),
        ("set_minus({}, A) = {}", "setMinusEmptyLeft"),
        (
            "set_minus(A, union(B, D)) = intersect(set_minus(A, B), set_minus(A, D))",
            "setMinusUnion",
        ),
        (
            "set_minus(A, intersect(B, D)) = union(set_minus(A, B), set_minus(A, D))",
            "setMinusIntersect",
        ),
        (
            "intersect(A, set_minus(B, A)) = {}",
            "intersectSetMinusEmpty",
        ),
        (
            "intersect(set_minus(B, A), A) = {}",
            "setMinusIntersectEmpty",
        ),
    ];
    for (source, law) in cases {
        let (left, right) = source.split_once(" = ").unwrap();
        for (left, right) in [(left, right), (right, left)] {
            let (run, compiler) =
                super::execute(&format!("forall A, B, D set:\n    {left} = {right}\n"));
            let lean = compiler.compile_run(&run, "difference_law").unwrap();
            assert!(lean.contains(&format!("Litex.{law} ")), "{source}");
        }
    }
}

#[test]
fn union_distribution_replays_all_operand_permutations_and_orientations() {
    for source_swap in [false, true] {
        for factors_swap in [false, true] {
            for first_swap in [false, true] {
                for second_swap in [false, true] {
                    let source = if source_swap {
                        "union(intersect(B, D), A)"
                    } else {
                        "union(A, intersect(B, D))"
                    };
                    let first = if first_swap {
                        "union(B, A)"
                    } else {
                        "union(A, B)"
                    };
                    let second = if second_swap {
                        "union(D, A)"
                    } else {
                        "union(A, D)"
                    };
                    let target = if factors_swap {
                        format!("intersect({second}, {first})")
                    } else {
                        format!("intersect({first}, {second})")
                    };
                    for (left, right) in [(source, target.as_str()), (target.as_str(), source)] {
                        let (run, compiler) =
                            super::execute(&format!("forall A, B, D set:\n    {left} = {right}\n"));
                        let lean = compiler.compile_run(&run, "union_distribution").unwrap();
                        assert!(lean.contains("Litex.unionIntersectDistrib "));
                        assert!(lean.contains("Litex.intersectCongr "));
                    }
                }
            }
        }
    }
}

#[test]
fn union_distribution_rejects_missing_factor_even_when_verifier_accepts_it() {
    // A = {}, B = {1}: the left side is {}, the right side is {1}.
    // The producer currently counts the common A as the missing second factor.
    // The compiler must not convert this accepted result into a theorem.
    for (left, right) in [
        (
            "union(A, intersect(B, A))",
            "intersect(union(A, B), union(A, B))",
        ),
        (
            "intersect(union(A, B), union(A, B))",
            "union(A, intersect(B, A))",
        ),
    ] {
        let source = format!("forall A, B set:\n    {left} = {right}\n");
        let command =
            super::parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(&source).unwrap();
        let compiler = super::LitexToLeanCompiler::new(runtime);
        let err = compiler
            .compile_run(&run, "invalid_distribution")
            .unwrap_err();
        // A future verifier repair may reject this at the source gate instead.
        if run.success {
            assert_eq!(err.route, "UnionOverIntersect/Factors");
        }
    }
}

#[test]
fn union_distribution_accepts_genuine_repeated_factors() {
    for source in [
        "union(A, intersect(B, B)) = intersect(union(A, B), union(A, B))",
        "union(A, intersect(B, A)) = intersect(union(A, B), union(A, A))",
    ] {
        let (run, compiler) = super::execute(&format!("forall A, B set:\n    {source}\n"));
        let lean = compiler.compile_run(&run, "repeated_distribution").unwrap();
        assert!(lean.contains("Litex.unionIntersectDistrib "));
    }
}
