use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule as SubsetRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::NotInFactSearchProofByBuiltinRule as NotInRule;

const NONMEMBER: &str =
    include_str!("../../../lean/examples/set_operator_nonmembership/statement.lit");
const MONOTONE: &str =
    include_str!("../../../lean/examples/set_containment_monotonicity/statement.lit");
const UNION: &str = include_str!("../../../lean/examples/union_containment_bounds/statement.lit");
const NESTED: &str = include_str!("../../../lean/examples/nested_set_containment/statement.lit");
const COMPONENTS: &str = "forall A, B, D, E set:\n    A $subset D\n    B $subset E\n    =>:\n        union(A, B) $subset union(D, E)\n";

fn subset_rule(result: &mut VerifyFactResult) -> &mut SubsetRule {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(p),
    ) = &mut super::atomic_proof_mut(result).searched_proof
    else {
        panic!("selected subset builtin")
    };
    p
}

#[test]
fn set_chains_replay_bounds_exclusions_and_named_proofs() {
    for (source, laws) in [
        (
            NONMEMBER,
            vec![
                "notInIntersectOfLeft",
                "notInIntersectOfRight",
                "notInUnion",
            ],
        ),
        (MONOTONE, vec!["setMinusMono", "powerSetMono"]),
        (
            UNION,
            vec![
                "unionSubsetOfBoth",
                "unionMono",
                "unionMonoSwap",
                "subsetRefl",
            ],
        ),
        (
            NESTED,
            vec![
                "unionSubsetOfBoth",
                "intersectSubsetOfLeft",
                "intersectSubsetOfRight",
                "setMinusSubsetOfLeft",
                "subsetTrans",
            ],
        ),
        (
            include_str!("../../../lean/examples/union_difference_bound/statement.lit"),
            vec!["unionSubsetOfBoth", "setMinusSubsetOfLeft"],
        ),
        (
            include_str!("../../../lean/examples/outside_union_intersection/statement.lit"),
            vec!["notInUnion", "notInIntersectOfLeft"],
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "set_chain").unwrap();
        for law in laws {
            assert!(lean.contains(&format!("Litex.{law} ")), "{law}");
        }
        assert_eq!(lean, compiler.compile_run(&run, "set_chain").unwrap());
    }
}

#[test]
fn consecutive_difference_replays_removed_order_and_equality_direction() {
    for (right, law) in [
        ("set_minus(A, union(B, D))", "setMinusChain"),
        ("set_minus(A, union(D, B))", "setMinusChainSwap"),
    ] {
        for (left, right) in [
            ("set_minus(set_minus(A, B), D)", right),
            (right, "set_minus(set_minus(A, B), D)"),
        ] {
            let (run, compiler) =
                super::execute(&format!("forall A, B, D set:\n    {left} = {right}\n"));
            let lean = compiler.compile_run(&run, "difference_chain").unwrap();
            assert!(lean.contains(&format!("Litex.{law} ")));
        }
    }
}

#[test]
fn nonmembership_rejects_changed_elements_swapped_children_and_future_citations() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(NONMEMBER);
        let p = super::forall_proof_mut(&mut run.statement_results[2]);
        let future = p.proved_then_facts[0].store_and_infer.primary_fact_id();
        let p = super::atomic_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(
                NotInRule::NonMembershipOfUnion(p),
            ),
        ) = &mut p.searched_proof
        else {
            panic!()
        };
        match mutation {
            0 => std::mem::swap(
                &mut p.left_non_membership_proof,
                &mut p.right_non_membership_proof,
            ),
            1 => {
                let AtomicFact::NotInFact(p) =
                    &mut super::atomic_proof_mut(&mut p.left_non_membership_proof).fact
                else {
                    panic!()
                };
                p.element = super::number_object("17");
            }
            2 => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
                    &mut super::atomic_proof_mut(&mut p.right_non_membership_proof).searched_proof
                else {
                    panic!()
                };
                p.cite_fact_id = future;
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "invalid_union_nonmember")
            .is_err());
    }
}

#[test]
fn intersection_nonmembership_rejects_wrong_factor() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(NONMEMBER);
        let p = super::forall_proof_mut(&mut run.statement_results[index]);
        let p = super::atomic_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let child = match &mut p.searched_proof {
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(
                    NotInRule::NonMembershipOfIntersectFromLeft(p),
                ),
            ) => &mut p.left_non_membership_proof,
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(
                    NotInRule::NonMembershipOfIntersectFromRight(p),
                ),
            ) => &mut p.right_non_membership_proof,
            _ => panic!(),
        };
        let AtomicFact::NotInFact(p) = &mut super::atomic_proof_mut(child).fact else {
            panic!()
        };
        p.set = super::number_object("17");
        assert!(compiler
            .compile_run(&run, "invalid_intersection_exclusion")
            .is_err());
    }
}

#[test]
fn subset_monotonicity_rejects_reversed_or_future_premise() {
    for index in 0..2 {
        for future in [false, true] {
            let (mut run, compiler) = super::execute(MONOTONE);
            let p = super::forall_proof_mut(&mut run.statement_results[index]);
            let output = p.proved_then_facts[0].store_and_infer.primary_fact_id();
            let child = match subset_rule(&mut p.proved_then_facts[0].verify_result) {
                SubsetRule::SubsetSetMinusCommonRightMonotone(p) => {
                    &mut p.left_operand_subset_proof
                }
                SubsetRule::SubsetPowerSetMonotone(p) => &mut p.base_subset_proof,
                _ => panic!(),
            };
            let p = super::atomic_proof_mut(child);
            if future {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
                    &mut p.searched_proof
                else {
                    panic!()
                };
                p.cite_fact_id = output;
            } else {
                let AtomicFact::SubsetFact(p) = &mut p.fact else {
                    panic!()
                };
                std::mem::swap(&mut p.left, &mut p.right);
            }
            assert!(compiler
                .compile_run(&run, "invalid_monotone_premise")
                .is_err());
        }
    }
}

#[test]
fn subset_transitivity_rejects_changed_middle_and_swapped_children() {
    for swapped in [false, true] {
        let (mut run, compiler) = super::execute(
            "forall A, B, D set:\n    A $subset B\n    B $subset D\n    =>:\n        A $subset D\n",
        );
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let SubsetRule::SubsetTransitivity(p) =
            subset_rule(&mut p.proved_then_facts[0].verify_result)
        else {
            panic!()
        };
        if swapped {
            std::mem::swap(&mut p.left_to_middle_proof, &mut p.middle_to_right_proof);
        } else {
            let AtomicFact::SubsetFact(p) =
                &mut super::atomic_proof_mut(&mut p.middle_to_right_proof).fact
            else {
                panic!()
            };
            p.left = super::number_object("17");
        }
        assert!(compiler.compile_run(&run, "invalid_subset_chain").is_err());
    }
}

#[test]
fn union_componentwise_uses_exactly_zero_one_or_two_recorded_children() {
    for (goal, requirements, expected) in [
        ("union(A, B) $subset union(B, A)", "", 0),
        (
            "union(A, D) $subset union(B, D)",
            "    A $subset B\n    =>:\n    ",
            1,
        ),
        (
            "union(D, A) $subset union(B, D)",
            "    A $subset B\n    =>:\n    ",
            1,
        ),
        (
            "union(A, B) $subset union(D, E)",
            "    A $subset D\n    B $subset E\n    =>:\n    ",
            2,
        ),
    ] {
        let (mut run, compiler) = super::execute(&format!(
            "forall A, B, D, E set:\n{requirements}    {goal}\n"
        ));
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let SubsetRule::UnionSubsetFromComponentwise(p) =
            subset_rule(&mut p.proved_then_facts[0].verify_result)
        else {
            panic!()
        };
        assert_eq!(p.proof_of_requirement_facts.len(), expected);
        assert!(compiler
            .compile_run(&run, "captured_union_components")
            .is_ok());
    }
}

#[test]
fn union_componentwise_rejects_missing_extra_or_reordered_children() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(COMPONENTS);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let SubsetRule::UnionSubsetFromComponentwise(p) =
            subset_rule(&mut p.proved_then_facts[0].verify_result)
        else {
            panic!()
        };
        match mutation {
            0 => {
                p.proof_of_requirement_facts.pop();
            }
            1 => {
                let (mut extra, _) = super::execute(COMPONENTS);
                let q = super::forall_proof_mut(&mut extra.statement_results[0]);
                let SubsetRule::UnionSubsetFromComponentwise(q) =
                    subset_rule(&mut q.proved_then_facts[0].verify_result)
                else {
                    panic!()
                };
                p.proof_of_requirement_facts
                    .push(q.proof_of_requirement_facts.pop().unwrap());
            }
            2 => p.proof_of_requirement_facts.swap(0, 1),
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "invalid_union_components")
            .is_err());
    }
}

#[test]
fn upper_bound_strategies_reject_missing_or_changed_original_requirements() {
    for (statement, conclusion) in [(0, 0), (1, 0), (1, 1), (2, 0)] {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(NESTED);
            let p = super::forall_proof_mut(&mut run.statement_results[statement]);
            let p = super::atomic_proof_mut(&mut p.proved_then_facts[conclusion].verify_result);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(p) = &mut p.searched_proof
            else {
                panic!()
            };
            let (requirements,proofs)=match p {
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionSubsetFromBothOperands(p)=>(&mut p.requirement_facts,&mut p.proof_of_requirement_facts),
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromLeftOperand(p)=>(&mut p.requirement_facts,&mut p.proof_of_requirement_facts),
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromRightOperand(p)=>(&mut p.requirement_facts,&mut p.proof_of_requirement_facts),
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusSubsetFromLeft(p)=>(&mut p.requirement_facts,&mut p.proof_of_requirement_facts),
                _=>panic!(),
            };
            match mutation {
                0 => {
                    requirements.pop();
                }
                1 => {
                    proofs.pop();
                }
                2 => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(p)) = &mut requirements[0] else {
                        panic!()
                    };
                    p.right = super::number_object("17");
                }
                _ => unreachable!(),
            }
            assert!(compiler
                .compile_run(&run, "invalid_upper_bound_strategy")
                .is_err());
        }
    }
}

#[test]
fn union_upper_bound_rejects_swapped_child_sources() {
    let (mut run, compiler) = super::execute(UNION);
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let SubsetRule::UnionSubsetFromBothOperands(p) =
        subset_rule(&mut p.proved_then_facts[0].verify_result)
    else {
        panic!()
    };
    std::mem::swap(
        &mut p.left_operand_subset_proof,
        &mut p.right_operand_subset_proof,
    );
    assert!(compiler
        .compile_run(&run, "invalid_union_upper_bound")
        .is_err());
}
