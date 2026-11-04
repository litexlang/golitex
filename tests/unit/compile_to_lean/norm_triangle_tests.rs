use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

const VECTOR: &str = include_str!("../../../lean/examples/euclidean_norm_triangle/statement.lit");
const MATRIX: &str = include_str!("../../../lean/examples/frobenius_norm_triangle/statement.lit");

fn goal(b: &mut BuiltinThmApplication) -> &mut LessEqualFact {
    let Fact::AtomicFact(AtomicFact::LessEqualFact(goal)) = &mut b.conclusions[0] else {
        panic!()
    };
    goal
}
fn formula(b: &mut BuiltinThmApplication) -> &mut AnonymousFn {
    let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(norm)) = &mut goal(b).left else {
        panic!()
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = norm.vector.as_mut() else {
        panic!()
    };
    literal
}

#[test]
fn norm_triangles_replay_complex_real_empty_vector_and_each_empty_matrix_axis() {
    for (source, law) in [
        (VECTOR, "euclideanNormTriangleFormula"),
        (MATRIX, "frobeniusNormTriangleEntrywise"),
        (
            include_str!("../../../lean/examples/euclidean_norm_triangle_real/statement.lit"),
            "euclideanNormTriangleFormula",
        ),
        (
            include_str!("../../../lean/examples/euclidean_norm_triangle_empty/statement.lit"),
            "euclideanNormTriangleFormula",
        ),
        (
            include_str!("../../../lean/examples/frobenius_norm_triangle_real/statement.lit"),
            "frobeniusNormTriangleEntrywise",
        ),
        (
            include_str!("../../../lean/examples/frobenius_norm_triangle_empty_rows/statement.lit"),
            "frobeniusNormTriangleEntrywise",
        ),
        (
            include_str!("../../../lean/examples/frobenius_norm_triangle_empty_cols/statement.lit"),
            "frobeniusNormTriangleEntrywise",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let out = compiler
            .compile_run(&run, "norm_triangle")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(out.contains(&format!("Litex.{law}")));
        assert_eq!(out, compiler.compile_run(&run, "norm_triangle").unwrap());
    }
}

#[test]
fn norm_triangles_require_all_original_repeated_context_proofs_stores_and_conclusion_wd() {
    for source in [VECTOR, MATRIX] {
        for change in ["proof", "store", "repeat", "wd", "conclusion", "order"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "repeat" => {
                    call.dom_proofs.remove(if source == VECTOR { 2 } else { 3 });
                }
                "wd" => call.conclusions_wd.clear(),
                "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
                _ => call.dom_proofs.swap(0, 1),
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("mutated_triangle_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn norm_triangles_retain_original_complex_carriers_dimensions_subjects_and_fact_ids() {
    for source in [VECTOR, MATRIX] {
        for change in ["carrier", "dimension", "subject", "fact_id", "natural"] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = if change == "natural" {
                0
            } else if source == VECTOR {
                3
            } else {
                5
            };
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[index] else {
                panic!()
            };
            match change {
                "natural" => f.set = Obj::StandardSet(StandardSet::Z),
                "subject" => f.element = super::number_object("99"),
                "fact_id" => f.fact_id = FactId::new(u64::MAX),
                _ => match &mut f.set {
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
                            s.cols = Box::new(super::number_object("99"));
                        }
                    }
                    _ => panic!(),
                },
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("mutated_triangle_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn norm_triangle_vector_formula_retains_original_unit_coefficients_calls_and_binder_domain() {
    for change in [
        "coefficient",
        "call",
        "binder",
        "start",
        "end",
        "target",
        "guard",
    ] {
        let (mut run, compiler) = super::execute(VECTOR);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let guard = b.requirements[0].clone();
        let original = b.arguments[0].clone();
        let literal = formula(b);
        match change {
            "start" | "end" => {
                let Obj::SetFormer(SetFormer::ClosedRange(range)) =
                    literal.body.set_bound_parameters.groups[0]
                        .param_type
                        .as_mut()
                else {
                    panic!()
                };
                if change == "start" {
                    range.start = Box::new(super::number_object("0"));
                } else {
                    range.end = Box::new(super::number_object("99"));
                }
            }
            "target" => literal.body.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            "guard" => {
                let Fact::AtomicFact(guard) = guard else {
                    panic!()
                };
                literal
                    .body
                    .dom_facts
                    .push(QuantifierFreeFact::AtomicFact(guard));
            }
            _ => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) =
                    literal.equal_to.as_mut()
                else {
                    panic!()
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = sum.right.as_mut()
                else {
                    panic!()
                };
                if change == "coefficient" {
                    product.left = Box::new(super::number_object("2"));
                } else {
                    let Obj::FnObj(call) = product.right.as_mut() else {
                        panic!()
                    };
                    if change == "call" {
                        call.head = Box::new(FnObjHead::from_obj(original));
                    } else {
                        call.body[0][0] = Box::new(super::number_object("1"));
                    }
                }
            }
        }
        let error = compiler
            .compile_run(&run, &format!("mutated_triangle_{change}"))
            .unwrap_err();
        assert!(
            error.route == "NormTriangle/ExactUnitVectorSum"
                || error.route == "NormTriangle/ExactFormulaDomain",
            "{change}: {error}"
        );
    }
}

#[test]
fn norm_triangle_matrix_sum_retains_exact_operands_and_rectangular_dimensions() {
    for change in ["left", "right", "rows", "cols"] {
        let (mut run, compiler) = super::execute(MATRIX);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(norm)) = &mut goal(b).left else {
            panic!()
        };
        let Obj::MatrixOperator(MatrixOperator::Add(sum)) = norm.matrix.as_mut() else {
            panic!()
        };
        match change {
            "left" => sum.left = Box::new(super::number_object("0")),
            "right" => sum.right = Box::new(super::number_object("0")),
            "rows" => sum.rows = Box::new(super::number_object("99")),
            _ => sum.cols = Box::new(super::number_object("99")),
        }
        assert_eq!(
            compiler
                .compile_run(&run, &format!("mutated_triangle_{change}"))
                .unwrap_err()
                .route,
            "NormTriangle/OriginalMatrixSum"
        );
    }
}

#[test]
fn norm_triangles_retain_original_inequality_orientation_and_ordered_right_norms() {
    for source in [VECTOR, MATRIX] {
        for change in [
            "orientation",
            "order",
            "subject",
            "dimension",
            "left_dimension",
        ] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let original = b.arguments[1].clone();
            let f = goal(b);
            if change == "orientation" {
                std::mem::swap(&mut f.left, &mut f.right);
            } else if change == "left_dimension" {
                match &mut f.left {
                    Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p)) => {
                        p.dimension = Box::new(super::number_object("99"))
                    }
                    Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(p)) => {
                        p.rows = Box::new(super::number_object("99"))
                    }
                    _ => panic!(),
                }
            } else {
                let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &mut f.right else {
                    panic!()
                };
                if change == "order" {
                    std::mem::swap(&mut sum.left, &mut sum.right);
                } else {
                    match sum.left.as_mut() {
                        Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p)) => {
                            if change == "subject" {
                                p.vector = Box::new(original);
                            } else {
                                p.dimension = Box::new(super::number_object("99"));
                            }
                        }
                        Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(p)) => {
                            if change == "subject" {
                                p.matrix = Box::new(original);
                            } else {
                                p.cols = Box::new(super::number_object("99"));
                            }
                        }
                        _ => panic!(),
                    }
                }
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("mutated_triangle_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn norm_triangles_reject_missing_reordered_and_changed_original_constructor_wd() {
    for source in [VECTOR, MATRIX] {
        for change in ["missing", "order", "subject"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut call.conclusions_wd[0] else {
                panic!()
            };
            let detail = wd.as_detailed_mut().unwrap();
            match change {
                "missing" => {
                    detail.well_defined_of_each_parameter.pop();
                }
                "order" => detail.well_defined_of_each_parameter.swap(0, 1),
                _ => {
                    let DetailedObjWellDefinedProof::ByDef { obj, .. } = detail
                        .well_defined_of_each_parameter[0]
                        .as_detailed_mut()
                        .unwrap()
                    else {
                        panic!()
                    };
                    *obj = super::number_object("0");
                }
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("mutated_triangle_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn norm_triangles_require_original_native_rule_identity_and_argument_order() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for source in [VECTOR, MATRIX] {
        for change in ["rule", "derivation", "arguments"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "rule" => {
                    call.builtin.as_mut().unwrap().theorem =
                        crate::builtin_theorem::BuiltinTheoremId::EuclideanNormSquare
                }
                "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
                _ => call.builtin.as_mut().unwrap().arguments.swap(0, 1),
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("mutated_triangle_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}
