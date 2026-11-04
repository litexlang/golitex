use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/matrix_inner_adjoint/statement.lit");

fn goal(b: &mut BuiltinThmApplication) -> &mut EqualFact {
    let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.conclusions[0] else {
        panic!()
    };
    f
}

#[test]
fn matrix_inner_adjoint_replays_complex_real_each_empty_axis_and_original_constructor_input() {
    for source in [
        SOURCE,
        include_str!("../../../lean/examples/matrix_inner_adjoint_real/statement.lit"),
        include_str!("../../../lean/examples/matrix_inner_adjoint_empty_rows/statement.lit"),
        include_str!("../../../lean/examples/matrix_inner_adjoint_empty_cols/statement.lit"),
        include_str!("../../../lean/examples/matrix_inner_adjoint_zero_matrix/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let out = compiler
            .compile_run(&run, "matrix_inner_adjoint")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(out.contains("Litex.matrixInnerProductAdjoint"));
        assert_eq!(
            out,
            compiler.compile_run(&run, "matrix_inner_adjoint").unwrap()
        );
    }
}

#[test]
fn matrix_inner_adjoint_keeps_all_seven_ordered_context_proofs_stores_and_conclusion_wd() {
    for change in [
        "proof",
        "store",
        "repeat_n",
        "repeat_m",
        "wd",
        "conclusion",
        "order",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        assert_eq!(call.dom_proofs.len(), 7);
        match change {
            "proof" => {
                call.dom_proofs.pop();
            }
            "store" => {
                call.dom_stores.pop();
            }
            "repeat_n" => {
                call.dom_proofs.remove(3);
            }
            "repeat_m" => {
                call.dom_proofs.remove(5);
            }
            "wd" => call.conclusions_wd.clear(),
            "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
            _ => call.dom_proofs.swap(4, 6),
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_inner_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn matrix_inner_adjoint_retains_each_original_complex_space_dimension_subject_and_fact_id() {
    for index in [0, 1, 2, 3, 4, 5, 6] {
        for change in ["carrier", "subject", "dimension", "fact_id"] {
            let (mut run, compiler) = super::execute(SOURCE);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[index] else {
                panic!()
            };
            match change {
                "subject" => f.element = super::number_object("99"),
                "fact_id" => f.fact_id = FactId::new(u64::MAX),
                _ => match &mut f.set {
                    Obj::StandardSet(_) => f.set = Obj::StandardSet(StandardSet::Z),
                    Obj::SetFormer(SetFormer::FiniteSeqSet(s)) => {
                        if change == "carrier" {
                            s.set = Box::new(Obj::StandardSet(StandardSet::R));
                        } else {
                            s.n = Box::new(super::number_object("99"));
                        }
                    }
                    Obj::SetFormer(SetFormer::MatrixSet(s)) => {
                        if change == "carrier" {
                            s.set = Box::new(Obj::StandardSet(StandardSet::R));
                        } else {
                            s.rows = Box::new(super::number_object("99"));
                        }
                    }
                    _ => panic!(),
                },
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_inner_{change}"))
                    .is_err(),
                "{index}/{change}"
            );
        }
    }
}

#[test]
fn matrix_inner_adjoint_retains_original_inner_product_sides_and_ordered_vector_arguments() {
    for change in [
        "orientation",
        "left_dimension",
        "right_dimension",
        "left_vector",
        "right_vector",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let u = b.arguments[1].clone();
        let v = b.arguments[2].clone();
        let f = goal(b);
        if change == "orientation" {
            std::mem::swap(&mut f.left, &mut f.right);
        } else if change.starts_with("left") {
            let Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) = &mut f.left else {
                panic!()
            };
            if change == "left_dimension" {
                p.dimension = Box::new(super::number_object("99"));
            } else {
                p.right = Box::new(u);
            }
        } else {
            let Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) = &mut f.right else {
                panic!()
            };
            if change == "right_dimension" {
                p.dimension = Box::new(super::number_object("99"));
            } else {
                p.left = Box::new(v);
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_inner_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn matrix_inner_adjoint_retains_original_left_application_matrix_vector_and_dimensions() {
    for change in ["matrix", "vector", "rows", "cols"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) = &mut goal(b).left else {
            panic!()
        };
        let Obj::MatrixOperator(MatrixOperator::Apply(action)) = p.left.as_mut() else {
            panic!()
        };
        match change {
            "matrix" => action.matrix = Box::new(super::number_object("0")),
            "vector" => action.vector = Box::new(super::number_object("0")),
            "rows" => action.rows = Box::new(super::number_object("99")),
            _ => action.cols = Box::new(super::number_object("99")),
        }
        assert_eq!(
            compiler
                .compile_run(&run, &format!("bad_inner_{change}"))
                .unwrap_err()
                .route,
            "MatrixInnerAdjoint/OriginalOrderedInnerProducts"
        );
    }
}

#[test]
fn matrix_inner_adjoint_requires_actual_conjugation_and_swapped_rectangular_application() {
    for change in [
        "transpose",
        "matrix",
        "source_rows",
        "source_cols",
        "rows",
        "cols",
        "vector",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) = &mut goal(b).right else {
            panic!()
        };
        let Obj::MatrixOperator(MatrixOperator::Apply(action)) = p.right.as_mut() else {
            panic!()
        };
        match change {
            "rows" => action.rows = Box::new(super::number_object("99")),
            "cols" => action.cols = Box::new(super::number_object("99")),
            "vector" => action.vector = Box::new(super::number_object("0")),
            _ => {
                let Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(t)) =
                    action.matrix.as_mut()
                else {
                    panic!()
                };
                match change {
                    "matrix" => t.matrix = Box::new(super::number_object("0")),
                    "source_rows" => t.rows = Box::new(super::number_object("99")),
                    "source_cols" => t.cols = Box::new(super::number_object("99")),
                    _ => {
                        let t = MatrixTranspose {
                            matrix: t.matrix.clone(),
                            rows: t.rows.clone(),
                            cols: t.cols.clone(),
                        };
                        action.matrix = Box::new(Obj::MatrixOperator(MatrixOperator::Transpose(t)));
                    }
                }
            }
        }
        assert_eq!(
            compiler
                .compile_run(&run, &format!("bad_inner_{change}"))
                .unwrap_err()
                .route,
            "MatrixInnerAdjoint/OriginalConjugateTransposeAndSwappedDimensions"
        );
    }
}

#[test]
fn matrix_inner_adjoint_rejects_reordered_or_changed_original_equality_constructor_wd() {
    for change in ["order", "left", "right"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        let FactWellDefinedProof::Equality(wd) = &mut call.conclusions_wd[0] else {
            panic!()
        };
        let wd = wd.as_detailed_mut().unwrap();
        if change == "order" {
            std::mem::swap(&mut wd.left, &mut wd.right);
        } else {
            let child = if change == "left" {
                &mut wd.left
            } else {
                &mut wd.right
            };
            let DetailedObjWellDefinedProof::ByDef { obj, .. } = child.as_detailed_mut().unwrap()
            else {
                panic!()
            };
            *obj = super::number_object("0");
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_inner_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn matrix_inner_adjoint_requires_original_native_schema_call_identity_and_argument_order() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for change in ["rule", "derivation", "args"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        match change {
            "rule" => {
                call.builtin.as_mut().unwrap().theorem =
                    crate::builtin_theorem::BuiltinTheoremId::InnerProductConjugateSymmetry
            }
            "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
            _ => call.builtin.as_mut().unwrap().arguments.swap(1, 2),
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_inner_{change}"))
                .is_err(),
            "{change}"
        );
    }
}
