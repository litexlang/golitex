use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCE: &str = r#"# Bound product rank by each original rectangular factor rank.
thm checked_matrix_rank_product_preparation:
    ? forall m, k, n N, A matrix(C,m,k), B matrix(C,k,n):
        matrix_rank(matrix_mul(A,B,m,k,n),m,n)<=matrix_rank(A,m,k)
        matrix_rank(matrix_mul(A,B,m,k,n),m,n)<=matrix_rank(B,k,n)
    release thm matrix_rank_product(A,B,m,k,n)
"#;

#[test]
fn rank_product_requires_all_six_stages_repeated_inner_dimension_and_both_output_wd() {
    for change in ["proof", "store", "repeat", "wd", "conclusion", "order"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        assert_eq!(call.dom_proofs.len(), 6);
        assert_eq!(call.conclusions_wd.len(), 2);
        match change {
            "proof" => {
                call.dom_proofs.pop();
            }
            "store" => {
                call.dom_stores.pop();
            }
            "repeat" => {
                call.dom_proofs.remove(3);
            }
            "wd" => {
                call.conclusions_wd.pop();
            }
            "conclusion" => {
                call.builtin.as_mut().unwrap().conclusions.pop();
            }
            _ => call.dom_proofs.swap(2, 5),
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}

#[test]
fn rank_product_keeps_exact_factor_carrier_shapes_subjects_and_context_fact_ids() {
    for change in [
        "carrier",
        "rows",
        "cols",
        "subject",
        "identity",
        "inner_witness",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let index = if change == "inner_witness" { 3 } else { 5 };
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &mut b.requirements[index] else {
            panic!("original rectangular context")
        };
        match change {
            "subject" => member.element = super::number_object("0"),
            "identity" => member.fact_id = FactId::new(u64::MAX),
            "inner_witness" => member.set = Obj::StandardSet(StandardSet::Z),
            _ => {
                let Obj::SetFormer(SetFormer::MatrixSet(m)) = &mut member.set else {
                    panic!("complex matrix")
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

#[test]
fn rank_product_retains_product_operands_inner_dimension_and_outer_rank_shape() {
    for change in [
        "left",
        "right",
        "inner",
        "product_rows",
        "rank_rows",
        "rank_cols",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut b.conclusions[0] else {
            panic!("product bound")
        };
        let Obj::MatrixOperator(MatrixOperator::Rank(r)) = &mut f.left else {
            panic!("product rank")
        };
        if change == "rank_rows" {
            r.rows = Box::new(super::number_object("7"));
        } else if change == "rank_cols" {
            r.cols = Box::new(super::number_object("7"));
        } else {
            let Obj::MatrixOperator(MatrixOperator::Multiply(m)) = r.matrix.as_mut() else {
                panic!("product")
            };
            match change {
                "left" => m.left = Box::new(b.arguments[1].clone()),
                "right" => m.right = Box::new(b.arguments[0].clone()),
                "inner" => m.inner = Box::new(super::number_object("7")),
                _ => m.rows = Box::new(super::number_object("7")),
            }
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}

#[test]
fn rank_product_preserves_both_ordered_factor_bounds_without_swapping_or_weakening() {
    for change in ["swap", "factor", "rows", "cols", "bound"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if change == "swap" {
            b.conclusions.swap(0, 1);
        } else {
            let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut b.conclusions[1] else {
                panic!("right factor bound")
            };
            if change == "bound" {
                f.right = super::number_object("100");
            } else {
                let Obj::MatrixOperator(MatrixOperator::Rank(r)) = &mut f.right else {
                    panic!("factor rank")
                };
                match change {
                    "factor" => r.matrix = Box::new(b.arguments[0].clone()),
                    "rows" => r.rows = Box::new(super::number_object("7")),
                    _ => r.cols = Box::new(super::number_object("7")),
                }
            }
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}

#[test]
fn rank_product_requires_original_native_derivation_and_call_identity() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for change in ["derivation", "arguments", "rule"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        match change {
            "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
            "arguments" => {
                call.builtin.as_mut().unwrap().arguments.pop();
            }
            _ => {
                call.builtin.as_mut().unwrap().theorem =
                    crate::builtin_theorem::BuiltinTheoremId::MatrixRankBounds
            }
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}
