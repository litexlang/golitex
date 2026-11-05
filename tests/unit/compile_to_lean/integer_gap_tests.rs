use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule as Rule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::scalar_order_relations::IntegerSuccessorGapProof;

const SUCCESSOR: &str = r#"# Strict integer order retains a full unit of separation.
forall gap_a, gap_b Z:
    gap_a < gap_b
    =>:
        gap_a + 1 <= gap_b
"#;
const PREDECESSOR: &str = r#"# The original greater-than premise is transposed without a new search.
forall gap_left, gap_right Z:
    gap_right > gap_left
    =>:
        gap_left <= gap_right - 1
"#;

fn selected(run: &mut RunLitexCodeResult) -> &mut IntegerSuccessorGapProof {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(Rule::IntegerSuccessorGap(
            p,
        )),
    ) = &mut atomic.searched_proof
    else {
        panic!("original selected integer gap")
    };
    p
}

#[test]
fn integer_gap_replays_both_unit_endpoints_and_the_original_strict_orientation() {
    for source in [SUCCESSOR, PREDECESSOR] {
        let (mut run, compiler) = super::execute(source);
        if source == PREDECESSOR {
            selected(&mut run);
        } else {
            let root = super::forall_proof_mut(&mut run.statement_results[0]);
            let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
            assert!(matches!(
                &atomic.searched_proof,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                        Rule::IntegerSuccessorLe(_)
                    )
                )
            ));
        }
        let out = compiler.compile_run(&run, "integer_gap").unwrap();
        assert!(out.contains(if source == PREDECESSOR {
            "Litex.integerGapLe"
        } else {
            "Litex.integerSuccessorGapValue"
        }));
        assert_eq!(out, compiler.compile_run(&run, "integer_gap").unwrap());
    }
}

#[test]
fn integer_gap_rejects_real_carriers_reordered_endpoints_and_future_citations() {
    for change in ["carrier", "order", "future"] {
        let (mut run, compiler) = super::execute(PREDECESSOR);
        let p = selected(&mut run);
        match change {
            "carrier" => {
                let VerifyFactResult::AtomicExceptEquality(v) = &mut p.left_integer else {
                    panic!()
                };
                let VerifyAtomicExceptEqualityFactResult::Success(v) = v.as_mut() else {
                    panic!()
                };
                let AtomicFact::InFact(f) = &mut v.fact else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            "order" => std::mem::swap(&mut p.left_integer, &mut p.right_integer),
            _ => {
                let root = super::forall_proof_mut(&mut run.statement_results[0]);
                let future = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result)
                    .fact
                    .fact_id();
                let p = selected(&mut run);
                p.strict_order.searched_proof =
                    Box::new(AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                        AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                            cite_fact_id: future,
                            why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
                        },
                    ));
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "both original integer carriers, endpoints and preceding strict citation are required",
        );
    }
}

#[test]
fn integer_gap_successor_requires_all_three_original_verified_stages() {
    for change in ["carrier", "strict", "future"] {
        let (mut run, compiler) = super::execute(SUCCESSOR);
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        let future = atomic.fact.fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                Rule::IntegerSuccessorLe(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!()
        };
        if change == "carrier" {
            std::mem::swap(&mut p.left_in_z_proof, &mut p.right_in_z_proof);
        } else {
            let v = super::atomic_proof_mut(&mut p.strict_proof);
            if change == "strict" {
                let AtomicFact::LessFact(f) = &mut v.fact else {
                    panic!()
                };
                f.left = super::number_object("0");
            } else {
                v.searched_proof = AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                    AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                        cite_fact_id: future,
                        why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
                    },
                );
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("successor membership and strict proof stages remain original and scoped");
    }
}
