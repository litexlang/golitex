use crate::prelude::*;

const LOWER: &str = include_str!("../../../lean/examples/weak_additive_lower_bounds/statement.lit");
const UPPER: &str = include_str!("../../../lean/examples/weak_additive_upper_bounds/statement.lit");

fn children(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> (&mut Vec<Fact>, &mut Vec<VerifyFactResult>) {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy) =
        &mut proof.searched_proof
    else {
        panic!("the original selected strategy")
    };
    match strategy {
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftLeft(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftRight(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftLeft(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftRight(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        _ => panic!("weak additive shift"),
    }
}

#[test]
fn weak_additive_shifts_replay_all_four_selected_variants_and_original_citations() {
    for (source, laws) in [
        (LOWER, ["leAddOfLeOfNonneg", "leAddOfLeOfNonnegSwap"]),
        (UPPER, ["addLeOfLeOfNonpos", "addLeOfLeOfNonposSwap"]),
    ] {
        let (mut run, compiler) = super::execute(source);
        let mut ids = Vec::new();
        for statement in &mut run.statement_results {
            let forall = super::forall_proof_mut(statement);
            ids.extend(
                forall
                    .assumed_dom_facts
                    .iter()
                    .map(|p| p.store_and_infer.primary_fact_id()),
            );
            let (requirements, proofs) = children(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result,
            ));
            assert_eq!((requirements.len(), proofs.len()), (2, 2));
        }
        let lean = compiler.compile_run(&run, "weak_additive_bounds").unwrap();
        for law in laws {
            assert!(lean.contains(&format!("Litex.{law} ")));
        }
        for id in ids {
            assert!(lean.contains(&format!("h_{}", id.value())));
        }
        assert_eq!(
            lean,
            compiler.compile_run(&run, "weak_additive_bounds").unwrap()
        );
    }
}

#[test]
fn weak_additive_shifts_reject_missing_reordered_and_mismatched_children() {
    for source in [LOWER, UPPER] {
        for index in 0..2 {
            for change in 0..5 {
                let (mut run, compiler) = super::execute(source);
                let forall = super::forall_proof_mut(&mut run.statement_results[index]);
                let (requirements, proofs) = children(super::atomic_proof_mut(
                    &mut forall.proved_then_facts[0].verify_result,
                ));
                match change {
                    0 => {
                        requirements.pop();
                    }
                    1 => {
                        proofs.pop();
                    }
                    2 => proofs.swap(0, 1),
                    3 => {
                        requirements.swap(0, 1);
                        proofs.swap(0, 1);
                    }
                    4 => {
                        let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut requirements[0]
                        else {
                            panic!()
                        };
                        f.left = super::number_object("17");
                    }
                    _ => unreachable!(),
                }
                assert!(
                    compiler
                        .compile_run(&run, "invalid_shift_children")
                        .is_err(),
                    "index {index}, change {change}"
                );
            }
        }
    }
}

#[test]
fn weak_additive_shifts_reject_changed_sign_even_with_matching_child_subject() {
    for source in [LOWER, UPPER] {
        for index in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let forall = super::forall_proof_mut(&mut run.statement_results[index]);
            let (requirements, proofs) = children(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result,
            ));
            let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut requirements[1] else {
                panic!()
            };
            std::mem::swap(&mut f.left, &mut f.right);
            let Fact::AtomicFact(changed) = &requirements[1] else {
                panic!()
            };
            super::atomic_proof_mut(&mut proofs[1]).fact = changed.clone();
            assert_eq!(
                compiler.compile_run(&run, "wrong_sign").unwrap_err().route,
                "WeakAddShift/ChildSubject"
            );
        }
    }
}

#[test]
fn weak_additive_shifts_reject_future_and_sibling_assumption_citations() {
    for sibling in [false, true] {
        let (mut run, compiler) = super::execute(LOWER);
        let foreign = super::forall_proof_mut(&mut run.statement_results[1]).assumed_dom_facts[0]
            .store_and_infer
            .primary_fact_id();
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let future = forall.proved_then_facts[0]
            .store_and_infer
            .primary_fact_id();
        let (_, proofs) = children(super::atomic_proof_mut(
            &mut forall.proved_then_facts[0].verify_result,
        ));
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
            &mut super::atomic_proof_mut(&mut proofs[0]).searched_proof
        else {
            panic!("cited premise")
        };
        p.cite_fact_id = if sibling { foreign } else { future };
        assert!(compiler
            .compile_run(&run, "escaped_shift_citation")
            .is_err());
    }
}

#[test]
fn weak_additive_shifts_compile_recorded_enumeration_and_theorem_routes() {
    for (index, source) in [
        include_str!("../../../lean/examples/integer_rectangle_sum_bound/statement.lit"),
        include_str!("../../../lean/examples/mixed_finite_rectangle_sum_bound/statement.lit"),
        include_str!("../../../lean/examples/binary_cube_sum_bound/statement.lit"),
        include_str!("../../../lean/examples/named_integer_rectangle_sum/statement.lit"),
    ]
    .into_iter()
    .enumerate()
    {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "enumerated_sum").unwrap();
        if index == 0 {
            assert!(lean.contains("Litex.addLeOfLeOfNonpos"));
        }
    }
}
