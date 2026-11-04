use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const NONZERO: &str =
    include_str!("../../../lean/examples/matrix_invertible_candidate/statement.lit");
const INVERSE: &str = include_str!("../../../lean/examples/matrix_inverse_candidate/statement.lit");

#[test]
fn matrix_candidates_replay_both_schemas_zero_literal_real_and_chained_profiles() {
    for source in [
        NONZERO,
        INVERSE,
        include_str!("../../../lean/examples/matrix_candidate_empty/statement.lit"),
        include_str!("../../../lean/examples/matrix_candidate_identity/statement.lit"),
        include_str!("../../../lean/examples/matrix_candidate_real/statement.lit"),
        include_str!("../../../lean/examples/matrix_candidate_chain/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "matrix_candidates")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(
            output.contains("Litex.matrixCandidateDeterminantNonzero")
                || output.contains("Litex.matrixInverseOfCandidate")
        );
        assert_eq!(
            output,
            compiler.compile_run(&run, "matrix_candidates").unwrap()
        );
    }
}

#[test]
fn matrix_candidates_require_every_original_stage_including_repeated_natural_contexts() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for source in [NONZERO, INVERSE] {
        for change in ["proof", "store", "wd", "repeat", "order", "derivation"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            assert_eq!(call.dom_proofs.len(), if source == INVERSE { 9 } else { 8 });
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "wd" => call.conclusions_wd.clear(),
                "repeat" => {
                    call.dom_proofs.remove(1);
                }
                "order" => call.dom_proofs.swap(2, 5),
                _ => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
            }
            assert!(compiler.compile_run(&run, change).is_err(), "{change}");
        }
    }
}

#[test]
fn matrix_candidates_reject_changed_carriers_dimensions_subjects_and_natural_witnesses() {
    for source in [NONZERO, INVERSE] {
        for change in ["carrier", "rows", "cols", "subject", "natural", "identity"] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = if change == "natural" { 3 } else { 5 };
            let Fact::AtomicFact(AtomicFact::InFact(member)) = &mut b.requirements[index] else {
                panic!("original matrix context")
            };
            match change {
                "natural" => member.set = Obj::StandardSet(StandardSet::Z),
                "subject" => member.element = super::number_object("0"),
                "identity" => member.fact_id = FactId::new(u64::MAX),
                _ => {
                    let Obj::SetFormer(SetFormer::MatrixSet(m)) = &mut member.set else {
                        panic!("original complex square")
                    };
                    match change {
                        "carrier" => m.set = Box::new(Obj::StandardSet(StandardSet::R)),
                        "rows" => m.rows = Box::new(super::number_object("7")),
                        _ => m.cols = Box::new(super::number_object("7")),
                    }
                }
            }
            assert!(compiler.compile_run(&run, change).is_err(), "{change}");
        }
    }
}

#[test]
fn matrix_candidates_keep_both_ordered_products_and_all_three_multiply_dimensions() {
    for source in [NONZERO, INVERSE] {
        for change in ["swap", "left", "right", "inner", "identity", "orientation"] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            if change == "swap" {
                b.requirements.swap(6, 7);
            } else {
                let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut b.requirements[6] else {
                    panic!("original product")
                };
                if change == "orientation" {
                    std::mem::swap(&mut eq.left, &mut eq.right);
                } else if change == "identity" {
                    eq.right = super::number_object("1");
                } else {
                    let Obj::MatrixOperator(MatrixOperator::Multiply(m)) = &mut eq.left else {
                        panic!("matrix multiplication")
                    };
                    match change {
                        "left" => m.left = Box::new(super::number_object("0")),
                        "right" => m.right = Box::new(super::number_object("0")),
                        _ => m.inner = Box::new(super::number_object("7")),
                    }
                }
            }
            assert!(compiler.compile_run(&run, change).is_err(), "{change}");
        }
    }
}

#[test]
fn matrix_candidates_retain_original_determinant_guard_inverse_and_candidate() {
    for change in [
        "guard_matrix",
        "guard_zero",
        "inverse_matrix",
        "inverse_order",
        "candidate",
    ] {
        let (mut run, compiler) = super::execute(INVERSE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if change.starts_with("guard") {
            let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = &mut b.requirements[8] else {
                panic!("original determinant guard")
            };
            if change == "guard_zero" {
                f.right = super::number_object("1");
            } else {
                let Obj::MatrixOperator(MatrixOperator::Determinant(d)) = &mut f.left else {
                    panic!("determinant")
                };
                d.matrix = Box::new(b.arguments[1].clone());
            }
        } else {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.conclusions[0] else {
                panic!("selected inverse")
            };
            if change == "candidate" {
                f.right = b.arguments[0].clone();
            } else {
                let Obj::MatrixOperator(MatrixOperator::Inverse(m)) = &mut f.left else {
                    panic!("matrix inverse")
                };
                if change == "inverse_matrix" {
                    m.matrix = Box::new(b.arguments[1].clone());
                } else {
                    m.order = Box::new(super::number_object("7"));
                }
            }
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}

#[test]
fn matrix_candidate_nonzero_guard_requires_an_earlier_exact_citation() {
    for change in ["future", "equalities"] {
        let (mut run, compiler) = super::execute(INVERSE);
        let call = invocation(&mut run);
        let future = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let guard = super::atomic_proof_mut(&mut call.dom_proofs[8]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
            &mut guard.searched_proof
        else {
            panic!("original nonzero citation")
        };
        if change == "future" {
            cite.cite_fact_id = future;
        } else {
            cite.why_parameters_of_known_fact_are_equal_to_givens
                .clear();
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}
