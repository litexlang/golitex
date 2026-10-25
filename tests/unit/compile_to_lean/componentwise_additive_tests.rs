use crate::prelude::*;

const WEAK: &str = include_str!("../../../lean/examples/componentwise_sum_bounds/statement.lit");
const MIXED: &str = include_str!("../../../lean/examples/mixed_strict_sum_bounds/statement.lit");

fn children(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> (&mut Vec<Fact>, &mut Vec<VerifyFactResult>) {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy) =
        &mut proof.searched_proof
    else {
        panic!("the original selected sum strategy")
    };
    match strategy {
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseLessEqual(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddCrossedLessEqual(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictLeft(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictRight(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        _ => panic!("componentwise sum"),
    }
}

#[test]
fn componentwise_addition_replays_all_four_variants_and_original_citations() {
    for (source, laws) in [
        (WEAK, ["addLeAdd", "addLeAddSwap"]),
        (MIXED, ["addLtAddOfLtOfLe", "addLtAddOfLeOfLt"]),
    ] {
        let (mut run, compiler) = super::execute(source);
        let mut ids = Vec::new();
        for stmt in &mut run.statement_results {
            let forall = super::forall_proof_mut(stmt);
            ids.extend(
                forall
                    .assumed_dom_facts
                    .iter()
                    .map(|p| p.store_and_infer.primary_fact_id()),
            );
            let (facts, proofs) = children(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result,
            ));
            assert_eq!((facts.len(), proofs.len()), (2, 2));
        }
        let lean = compiler.compile_run(&run, "sum_bounds").unwrap();
        for law in laws {
            assert!(lean.contains(&format!("Litex.{law} ")));
        }
        for id in ids {
            assert!(lean.contains(&format!("h_{}", id.value())));
        }
        assert_eq!(lean, compiler.compile_run(&run, "sum_bounds").unwrap());
    }
}

#[test]
fn componentwise_addition_rejects_missing_reordered_and_mismatched_children() {
    for source in [WEAK, MIXED] {
        for index in 0..2 {
            for change in 0..5 {
                let (mut run, compiler) = super::execute(source);
                let forall = super::forall_proof_mut(&mut run.statement_results[index]);
                let (facts, proofs) = children(super::atomic_proof_mut(
                    &mut forall.proved_then_facts[0].verify_result,
                ));
                match change {
                    0 => {
                        facts.pop();
                    }
                    1 => {
                        proofs.pop();
                    }
                    2 => proofs.swap(0, 1),
                    3 => {
                        facts.swap(0, 1);
                        proofs.swap(0, 1);
                    }
                    4 => match &mut facts[0] {
                        Fact::AtomicFact(AtomicFact::LessFact(p)) => {
                            p.left = super::number_object("17")
                        }
                        Fact::AtomicFact(AtomicFact::LessEqualFact(p)) => {
                            p.left = super::number_object("17")
                        }
                        _ => panic!(),
                    },
                    _ => unreachable!(),
                }
                assert!(
                    compiler.compile_run(&run, "invalid_sum_children").is_err(),
                    "index {index}, change {change}"
                );
            }
        }
    }
}

#[test]
fn componentwise_addition_rejects_changed_pairing_with_matching_child_subject() {
    for source in [WEAK, MIXED] {
        for index in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let forall = super::forall_proof_mut(&mut run.statement_results[index]);
            let (facts, proofs) = children(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result,
            ));
            match &mut facts[0] {
                Fact::AtomicFact(AtomicFact::LessFact(p)) => {
                    std::mem::swap(&mut p.left, &mut p.right)
                }
                Fact::AtomicFact(AtomicFact::LessEqualFact(p)) => {
                    std::mem::swap(&mut p.left, &mut p.right)
                }
                _ => panic!(),
            }
            let Fact::AtomicFact(changed) = &facts[0] else {
                panic!()
            };
            super::atomic_proof_mut(&mut proofs[0]).fact = changed.clone();
            assert_eq!(
                compiler
                    .compile_run(&run, "wrong_sum_pairing")
                    .unwrap_err()
                    .route,
                "ComponentwiseAdd/ChildSubject"
            );
        }
    }
}

#[test]
fn componentwise_addition_rejects_future_and_sibling_citations() {
    for source in [WEAK, MIXED] {
        for sibling in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let foreign = super::forall_proof_mut(&mut run.statement_results[1]).assumed_dom_facts
                [0]
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
                panic!()
            };
            p.cite_fact_id = if sibling { foreign } else { future };
            assert!(compiler.compile_run(&run, "escaped_sum_citation").is_err());
        }
    }
}

#[test]
fn componentwise_addition_rejects_changed_strength_with_matching_child_subject() {
    for source in [WEAK, MIXED] {
        for index in 0..2 {
            for child in 0..2 {
                let (mut run, compiler) = super::execute(source);
                let forall = super::forall_proof_mut(&mut run.statement_results[index]);
                let (facts, proofs) = children(super::atomic_proof_mut(
                    &mut forall.proved_then_facts[0].verify_result,
                ));
                let changed = match &facts[child] {
                    Fact::AtomicFact(AtomicFact::LessFact(p)) => {
                        AtomicFact::LessEqualFact(LessEqualFact {
                            fact_id: p.fact_id,
                            left: p.left.clone(),
                            right: p.right.clone(),
                            line_file: p.line_file.clone(),
                        })
                    }
                    Fact::AtomicFact(AtomicFact::LessEqualFact(p)) => {
                        AtomicFact::LessFact(LessFact {
                            fact_id: p.fact_id,
                            left: p.left.clone(),
                            right: p.right.clone(),
                            line_file: p.line_file.clone(),
                        })
                    }
                    _ => panic!(),
                };
                facts[child] = Fact::AtomicFact(changed.clone());
                super::atomic_proof_mut(&mut proofs[child]).fact = changed;
                assert_eq!(
                    compiler
                        .compile_run(&run, "changed_sum_strength")
                        .unwrap_err()
                        .route,
                    "ComponentwiseAdd/ChildSubject"
                );
            }
        }
    }
}

#[test]
fn componentwise_addition_composes_and_reuses_a_named_theorem() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/three_term_sum_bound/statement.lit"
    ));
    let lean = compiler.compile_run(&run, "three_term_sum").unwrap();
    assert!(lean.contains("Litex.addLeAdd "));
    assert!(lean.contains("Litex.addLtAddOfLeOfLt "));
}
