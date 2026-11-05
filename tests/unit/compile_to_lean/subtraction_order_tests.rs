use crate::prelude::*;

const RIGHT: &str = r#"# Subtracting the same real value preserves weak and strict inequalities.
forall next_sub_a, next_sub_b, next_sub_c R:
    next_sub_a <= next_sub_b
    =>:
        next_sub_a - next_sub_c <= next_sub_b - next_sub_c

forall sub_strict_a, sub_strict_b, sub_strict_c R:
    sub_strict_a < sub_strict_b
    =>:
        sub_strict_a - sub_strict_c < sub_strict_b - sub_strict_c

forall nested_sub_a, nested_sub_b, nested_sub_c, nested_sub_d R:
    nested_sub_a <= nested_sub_b
    =>:
        nested_sub_a - (nested_sub_c + nested_sub_d) <= nested_sub_b - (nested_sub_c + nested_sub_d)
"#;
const LEFT: &str = r#"# Subtracting ordered values from a shared real value reverses their order.
forall sub_left_a, sub_left_b, sub_left_c R:
    sub_left_a <= sub_left_b
    =>:
        sub_left_c - sub_left_b <= sub_left_c - sub_left_a

forall sub_left_strict_a, sub_left_strict_b, sub_left_strict_c R:
    sub_left_strict_a < sub_left_strict_b
    =>:
        sub_left_strict_c - sub_left_strict_b < sub_left_strict_c - sub_left_strict_a
"#;

fn children(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> (&mut Vec<Fact>, &mut Vec<VerifyFactResult>) {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy) =
        &mut proof.searched_proof
    else {
        panic!("the original subtraction strategy")
    };
    match strategy {
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLessEqual(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLessEqual(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLess(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLess(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        _ => panic!("shared subtraction"),
    }
}

#[test]
fn subtraction_order_replays_all_four_variants_and_original_citations() {
    for (source, laws) in [
        (RIGHT, ["subStructuralLeRight", "subStructuralLtRight"]),
        (LEFT, ["subStructuralLeLeft", "subStructuralLtLeft"]),
    ] {
        let (mut run, compiler) = super::execute(source);
        let mut ids = Vec::new();
        for stmt in &mut run.statement_results {
            let forall = super::forall_proof_mut(stmt);
            ids.push(
                forall.assumed_dom_facts[0]
                    .store_and_infer
                    .primary_fact_id(),
            );
            let (facts, proofs) = children(super::atomic_proof_mut(
                &mut forall.proved_then_facts[0].verify_result,
            ));
            assert_eq!((facts.len(), proofs.len()), (1, 1));
        }
        let lean = compiler.compile_run(&run, "subtraction_bounds").unwrap();
        for law in laws {
            assert!(lean.contains(&format!("Litex.{law} ")));
        }
        for id in ids {
            assert!(lean.contains(&format!("h_{}", id.value())));
        }
        assert_eq!(
            lean,
            compiler.compile_run(&run, "subtraction_bounds").unwrap()
        );
    }
}

#[test]
fn subtraction_order_rejects_missing_extra_and_mismatched_children() {
    for source in [RIGHT, LEFT] {
        for index in 0..2 {
            for change in 0..4 {
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
                    2 => facts.push(facts[0].clone()),
                    3 => match &mut facts[0] {
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
                assert!(compiler
                    .compile_run(&run, "invalid_subtraction_child")
                    .is_err());
            }
        }
    }
}

#[test]
fn subtraction_order_rejects_reversed_or_changed_strength_with_matching_child() {
    for source in [RIGHT, LEFT] {
        for index in 0..2 {
            for reverse in [false, true] {
                let (mut run, compiler) = super::execute(source);
                let forall = super::forall_proof_mut(&mut run.statement_results[index]);
                let (facts, proofs) = children(super::atomic_proof_mut(
                    &mut forall.proved_then_facts[0].verify_result,
                ));
                let changed = match &facts[0] {
                    Fact::AtomicFact(AtomicFact::LessFact(p)) if reverse => {
                        let mut p = p.clone();
                        std::mem::swap(&mut p.left, &mut p.right);
                        AtomicFact::LessFact(p)
                    }
                    Fact::AtomicFact(AtomicFact::LessEqualFact(p)) if reverse => {
                        let mut p = p.clone();
                        std::mem::swap(&mut p.left, &mut p.right);
                        AtomicFact::LessEqualFact(p)
                    }
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
                facts[0] = Fact::AtomicFact(changed.clone());
                super::atomic_proof_mut(&mut proofs[0]).fact = changed;
                assert_eq!(
                    compiler
                        .compile_run(&run, "wrong_subtraction_premise")
                        .unwrap_err()
                        .route,
                    "SharedSubtraction/ChildSubject"
                );
            }
        }
    }
}

#[test]
fn subtraction_order_rejects_future_and_sibling_citations() {
    for source in [RIGHT, LEFT] {
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
            assert!(compiler
                .compile_run(&run, "escaped_subtraction_citation")
                .is_err());
        }
    }
}

#[test]
fn subtraction_order_rejects_changed_common_operand() {
    for (source, common_left) in [(RIGHT, false), (LEFT, true)] {
        for index in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let forall = super::forall_proof_mut(&mut run.statement_results[index]);
            let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
            let high = match &mut proof.fact {
                AtomicFact::LessFact(p) => &mut p.right,
                AtomicFact::LessEqualFact(p) => &mut p.right,
                _ => panic!(),
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) = high else {
                panic!()
            };
            if common_left {
                p.left = Box::new(super::number_object("17"));
            } else {
                p.right = Box::new(super::number_object("17"));
            }
            assert!(compiler
                .compile_run(&run, "changed_shared_operand")
                .is_err());
        }
    }
}

#[test]
fn subtraction_order_rejects_missing_predicate_domain_evidence() {
    let (mut run, compiler) = super::execute(RIGHT);
    let forall = super::forall_proof_mut(&mut run.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .predicate_domain = PredicateDomainProof::ByRequirements(Vec::new());
    assert!(compiler
        .compile_run(&run, "missing_subtraction_domain")
        .is_err());
}
