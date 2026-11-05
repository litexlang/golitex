use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const SOURCE: &str = r#"# The rank equals the inner dimension of a supplied split matrix factorization.
thm checked_rank_split_factorization_preparation:
    ? forall m, k, n N, A matrix(C,m,n), U matrix(C,m,k), V matrix(C,k,n), L matrix(C,k,m), Rr matrix(C,n,k):
        k<=m
        k<=n
        A=matrix_mul(U,V,m,k,n)
        matrix_mul(L,U,k,m,k)=identity_matrix(k)
        matrix_mul(V,Rr,k,n,k)=identity_matrix(k)
        =>:
            matrix_rank(A,m,n)=k
    release thm matrix_rank_from_factorization(A,U,V,L,Rr,m,k,n)

"#;

#[test]
fn rank_factorization_retains_all_twenty_proofs_stores_and_original_order() {
    for change in ["proof", "store", "wd", "conclusion", "order"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        assert_eq!(call.dom_proofs.len(), 20);
        match change {
            "proof" => {
                call.dom_proofs.remove(9);
            }
            "store" => {
                call.dom_stores.remove(15);
            }
            "wd" => call.conclusions_wd.clear(),
            "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
            _ => call.dom_proofs.swap(18, 19),
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}

#[test]
fn rank_factorization_retains_each_matrix_context_natural_dimension_carrier_and_subject() {
    for matrix_index in 0..5 {
        for change in ["natural", "subject", "carrier", "rows", "cols", "fact_id"] {
            let (mut run, compiler) = super::execute(SOURCE);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = 3 * matrix_index + if change == "natural" { 0 } else { 2 };
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[index] else {
                panic!()
            };
            match change {
                "natural" => f.set = Obj::StandardSet(StandardSet::Z),
                "subject" => f.element = super::number_object("99"),
                "fact_id" => f.fact_id = FactId::new(u64::MAX),
                _ => {
                    let Obj::SetFormer(SetFormer::MatrixSet(s)) = &mut f.set else {
                        panic!()
                    };
                    match change {
                        "carrier" => s.set = Box::new(Obj::StandardSet(StandardSet::R)),
                        "rows" => s.rows = Box::new(super::number_object("99")),
                        _ => s.cols = Box::new(super::number_object("99")),
                    }
                }
            }
            assert!(
                compiler.compile_run(&run, change).is_err(),
                "{matrix_index}/{change}"
            );
        }
    }
}

#[test]
fn rank_factorization_requires_exact_inner_dimension_bounds_even_when_native_proof_is_stronger() {
    for index in [15, 16] {
        for reverse in [false, true] {
            let (mut run, compiler) = super::execute(SOURCE);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut b.requirements[index] else {
                panic!()
            };
            if reverse {
                std::mem::swap(&mut f.left, &mut f.right);
            } else {
                f.left = super::number_object("0");
            }
            let error = compiler.compile_run(&run, "bound").unwrap_err();
            assert_eq!(
                error.route,
                "RankFactorization/OriginalInnerDimensionBounds"
            );
        }
    }
}

#[test]
fn rank_factorization_preserves_each_product_operand_dimension_and_identity_orientation() {
    for index in [17, 18, 19] {
        for change in [
            "reverse", "left", "right", "rows", "inner", "cols", "target",
        ] {
            let (mut run, compiler) = super::execute(SOURCE);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.requirements[index] else {
                panic!()
            };
            if change == "reverse" {
                std::mem::swap(&mut f.left, &mut f.right);
            } else if change == "target" {
                if index == 17 {
                    f.left = super::number_object("0");
                } else {
                    f.right = super::number_object("1");
                }
            } else {
                let obj = if index == 17 {
                    &mut f.right
                } else {
                    &mut f.left
                };
                let Obj::MatrixOperator(MatrixOperator::Multiply(p)) = obj else {
                    panic!()
                };
                match change {
                    "left" => p.left = Box::new(super::number_object("0")),
                    "right" => p.right = Box::new(super::number_object("0")),
                    "rows" => p.rows = Box::new(super::number_object("99")),
                    "inner" => p.inner = Box::new(super::number_object("99")),
                    _ => p.cols = Box::new(super::number_object("99")),
                }
            }
            let error = compiler.compile_run(&run, change).unwrap_err();
            assert_eq!(
                error.route, "RankFactorization/OriginalFactorizationAndSplittings",
                "{index}/{change}"
            );
        }
    }
}

#[test]
fn rank_factorization_retains_exact_rank_subject_dimensions_and_output_value() {
    for change in ["subject", "rows", "cols", "value"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.conclusions[0] else {
            panic!()
        };
        if change == "value" {
            f.right = super::number_object("0");
        } else {
            let Obj::MatrixOperator(MatrixOperator::Rank(r)) = &mut f.left else {
                panic!()
            };
            match change {
                "subject" => r.matrix = Box::new(b.arguments[1].clone()),
                "rows" => r.rows = Box::new(super::number_object("99")),
                _ => r.cols = Box::new(super::number_object("99")),
            }
        }
        assert_eq!(
            compiler.compile_run(&run, change).unwrap_err().route,
            "RankFactorization/OriginalRankAndDimension"
        );
    }
}

#[test]
fn rank_factorization_retains_original_rule_arguments_and_selected_native_schema() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for change in ["rule", "args", "derivation"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        match change {
            "rule" => {
                call.builtin.as_mut().unwrap().theorem =
                    crate::builtin_theorem::BuiltinTheoremId::MatrixRankProduct
            }
            "args" => call.builtin.as_mut().unwrap().arguments.swap(1, 2),
            _ => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}
