use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

const MEMBERS: &str = include_str!("../../../lean/examples/intersection_membership/statement.lit");
const BOUNDS: &str =
    include_str!("../../../lean/examples/intersection_subset_bounds/statement.lit");

#[test]
fn intersection_replays_membership_projections_and_subset_routes() {
    for (source, laws) in [
        (MEMBERS, vec!["inIntersect_iff"]),
        (
            BOUNDS,
            vec![
                "intersectSubsetLeft",
                "intersectSubsetRight",
                "intersectSubsetOfLeft",
                "intersectSubsetOfRight",
                "subsetIntersect",
            ],
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "intersection").unwrap();
        assert!(lean.contains("Litex.SetSemantics M"));
        assert!(lean.contains("Litex.intersect "));
        for law in laws {
            assert!(lean.contains(&format!("Litex.{law} ")));
        }
        assert_eq!(lean, compiler.compile_run(&run, "intersection").unwrap());
    }
}

#[test]
fn intersection_rejects_missing_or_reordered_constructor_wd() {
    for reordered in [false, true] {
        let (mut run, compiler) = super::execute(MEMBERS);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::Intersect(
                    wd,
                )),
            ..
        } = (&mut proof
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[1])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("intersection WD")
        };
        if reordered {
            wd.child_obj_well_defined.swap(0, 1);
        } else {
            wd.child_obj_well_defined.pop();
        }
        assert!(compiler
            .compile_run(&run, "invalid_intersection_wd")
            .is_err());
    }
}

#[test]
fn intersection_rejects_reordered_memberships_and_future_citations() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(MEMBERS);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let future = forall.proved_then_facts[0]
            .store_and_infer
            .primary_fact_id();
        let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::IntersectMembership(p),
            ),
        ) = &mut proof.searched_proof
        else {
            panic!("selected intersection builtin")
        };
        match change {
            0 => std::mem::swap(&mut p.left_membership_proof, &mut p.right_membership_proof),
            1 => {
                let AtomicFact::InFact(f) =
                    &mut super::atomic_proof_mut(&mut p.right_membership_proof).fact
                else {
                    panic!()
                };
                f.element = super::number_object("17");
            }
            2 => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
                    &mut super::atomic_proof_mut(&mut p.left_membership_proof).searched_proof
                else {
                    panic!()
                };
                c.cite_fact_id = future;
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&run, "invalid_intersection_members")
            .is_err());
    }
}

#[test]
fn intersection_rejects_reordered_projection_stores() {
    let (mut run, compiler) = super::execute(MEMBERS);
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
        &mut forall.proved_then_facts[0].store_and_infer.infer
    else {
        panic!()
    };
    let p = rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferInFactResult::IntersectBoth(p) => Some(p),
            _ => None,
        })
        .expect("original intersection projections");
    std::mem::swap(&mut p.left_membership, &mut p.right_membership);
    assert!(compiler
        .compile_run(&run, "invalid_intersection_projections")
        .is_err());
}

#[test]
fn intersection_rejects_reused_projection_identity() {
    let (mut run, compiler) = super::execute(MEMBERS);
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
        &mut forall.proved_then_facts[0].store_and_infer.infer
    else {
        panic!()
    };
    let p = rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferInFactResult::IntersectBoth(p) => Some(p),
            _ => None,
        })
        .unwrap();
    let left_id = p.left_membership.primary_fact_id();
    let crate::store_fact_and_infer::StoreFactResult::AtomicFact(right) =
        &mut p.right_membership.store
    else {
        panic!()
    };
    right.fact_id = left_id;
    assert!(compiler.compile_run(&run, "reused_projection_id").is_err());
}

#[test]
fn intersection_rejects_changed_upper_bound_child() {
    for index in 1..3 {
        let (mut run, compiler) = super::execute(BOUNDS);
        let forall = super::forall_proof_mut(&mut run.statement_results[index]);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(rule),
        ) = &mut super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result)
            .searched_proof
        else {
            panic!()
        };
        let child = match rule {
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromLeftUpperBound(p) => {
                &mut p.left_operand_subset_proof
            }
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromRightUpperBound(p) => {
                &mut p.right_operand_subset_proof
            }
            _ => panic!(),
        };
        let AtomicFact::SubsetFact(p) = &mut super::atomic_proof_mut(child).fact else {
            panic!()
        };
        std::mem::swap(&mut p.left, &mut p.right);
        assert!(compiler
            .compile_run(&run, "changed_intersection_bound")
            .is_err());
    }
}

#[test]
fn intersection_rejects_missing_or_reordered_subset_requirements() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(BOUNDS);
        let forall = super::forall_proof_mut(&mut run.statement_results[3]);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfIntersectFromBothBounds(
                p,
            ),
        ) = &mut super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result)
            .searched_proof
        else {
            panic!("selected intersection lower bound")
        };
        match change {
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
            .compile_run(&run, "invalid_intersection_bounds")
            .is_err());
    }
}

#[test]
fn intersection_nested_memberships_and_named_theorem_replay() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/intersection_reassociation/statement.lit"
    ));
    let lean = compiler
        .compile_run(&run, "intersection_association")
        .unwrap();
    assert!(lean.contains("Litex.inIntersect_iff "));
}

#[test]
fn intersection_alias_membership_and_sethood_compile() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/named_intersection/statement.lit"
    ));
    let lean = compiler.compile_run(&run, "named_intersection").unwrap();
    assert!(lean.contains("Litex.intersect "));
    assert!(lean.contains("Litex.inIntersect_iff "));
}

#[test]
fn intersection_nested_strategy_rejects_missing_or_reordered_requirements() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/intersection_reassociation/statement.lit"
        ));
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
            panic!()
        };
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut body.proof_steps[1]
        else {
            panic!()
        };
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectMembership(p),
        ) = &mut super::atomic_proof_mut(&mut step.verify_result).searched_proof
        else {
            panic!()
        };
        match change {
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
            .compile_run(&run, "invalid_nested_intersection")
            .is_err());
    }
}
