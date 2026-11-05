use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

const UPPER: &str = r#"# A triangular finite complex determinant is the product of its diagonal entries.
thm checked_det_upper_preparation:
    ? forall n N, A matrix(C,n,n):
        forall row, col closed_range(1,n):
            col<row
            =>:
                A(row,col)=0
        =>:
            det(A,n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C{A(k,k)})
    release thm matrix_det_upper_triangular(A,n)

"#;
const LOWER: &str = r#"# A triangular finite complex determinant is the product of its diagonal entries.
thm checked_det_lower_preparation:
    ? forall n N, A matrix(C,n,n):
        forall row, col closed_range(1,n):
            row<col
            =>:
                A(row,col)=0
        =>:
            det(A,n)=finite_set_product(closed_range(1,n),fn(k closed_range(1,n)) C{A(k,k)})
    release thm matrix_det_lower_triangular(A,n)

"#;
fn condition(b: &mut BuiltinThmApplication) -> &mut ForallFact {
    let Fact::ForallFact(f) = &mut b.requirements[3] else {
        panic!()
    };
    f
}
fn goal(b: &mut BuiltinThmApplication) -> &mut EqualFact {
    let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.conclusions[0] else {
        panic!()
    };
    f
}
fn callback(b: &mut BuiltinThmApplication) -> &mut AnonymousFn {
    let Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(p)) = &mut goal(b).right else {
        panic!()
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = p.func.as_mut() else {
        panic!()
    };
    f
}

#[test]
fn triangular_determinants_retain_four_ordered_requirements_stores_and_output_wd() {
    for source in [UPPER, LOWER] {
        for change in [
            "proof",
            "store",
            "repeat",
            "forall",
            "wd",
            "conclusion",
            "order",
        ] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            assert_eq!(call.dom_proofs.len(), 4);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "repeat" => {
                    call.dom_proofs.remove(1);
                }
                "forall" => {
                    call.builtin.as_mut().unwrap().requirements.pop();
                }
                "wd" => call.conclusions_wd.clear(),
                "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
                _ => call.dom_proofs.swap(2, 3),
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_tri_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn triangular_determinants_retain_complex_square_carriers_both_naturals_and_exact_ids() {
    for source in [UPPER, LOWER] {
        for change in [
            "natural0", "natural1", "carrier", "rows", "cols", "subject", "fact_id",
        ] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = if change == "natural0" {
                0
            } else if change == "natural1" {
                1
            } else {
                2
            };
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[index] else {
                panic!()
            };
            match change {
                "natural0" | "natural1" => f.set = Obj::StandardSet(StandardSet::Z),
                "subject" => f.element = super::number_object("0"),
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
                compiler
                    .compile_run(&run, &format!("bad_tri_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn triangular_determinants_retain_original_forall_binders_distinct_ids_and_index_ranges() {
    for source in [UPPER, LOWER] {
        for change in ["groups", "binder", "identity", "start", "end"] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let f = condition(b);
            match change {
                "groups" => {
                    f.typed_parameters.groups.pop();
                }
                "binder" => f.typed_parameters.groups[0].params.clear(),
                "identity" => {
                    f.typed_parameters.groups[1].params[0].id =
                        f.typed_parameters.groups[0].params[0].id
                }
                _ => {
                    let ParamType::Obj(domain) = &mut f.typed_parameters.groups[1].param_type
                    else {
                        panic!()
                    };
                    let Obj::SetFormer(SetFormer::ClosedRange(range)) = domain else {
                        panic!()
                    };
                    if change == "start" {
                        range.start = Box::new(super::number_object("0"));
                    } else {
                        range.end = Box::new(super::number_object("99"));
                    }
                }
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_tri_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn triangular_determinants_preserve_the_original_strict_upper_or_lower_guard() {
    for source in [UPPER, LOWER] {
        for change in ["reverse", "missing", "extra", "kind"] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let f = condition(b);
            match change {
                "missing" => f.dom_facts.clear(),
                "extra" => f.dom_facts.push(f.dom_facts[0].clone()),
                _ => {
                    let Fact::AtomicFact(AtomicFact::LessFact(g)) = &mut f.dom_facts[0] else {
                        panic!()
                    };
                    if change == "reverse" {
                        std::mem::swap(&mut g.left, &mut g.right);
                    } else {
                        f.dom_facts[0] = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                            fact_id: g.fact_id,
                            left: g.left.clone(),
                            right: g.right.clone(),
                            line_file: g.line_file.clone(),
                        }));
                    }
                }
            }
            let error = compiler
                .compile_run(&run, &format!("bad_tri_{change}"))
                .unwrap_err();
            assert!(
                error.route == "TriangularDeterminant/OriginalStrictGuard"
                    || error.route == "TriangularDeterminant/OriginalGuardOrientation",
                "{change}: {error}"
            );
        }
    }
}

#[test]
fn triangular_determinants_preserve_zero_entry_value_matrix_and_ordered_coordinates() {
    for source in [UPPER, LOWER] {
        for change in ["value", "matrix", "coordinates", "missing"] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let f = condition(b);
            if change == "missing" {
                f.then_facts.clear();
            } else {
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) =
                    &mut f.then_facts[0]
                else {
                    panic!()
                };
                if change == "value" {
                    e.right = super::number_object("1");
                } else {
                    let Obj::FnObj(call) = &mut e.left else {
                        panic!()
                    };
                    if change == "matrix" {
                        call.head = Box::new(FnObjHead::from_obj(super::number_object("0")));
                    } else {
                        call.body[0].swap(0, 1);
                    }
                }
            }
            assert_eq!(
                compiler
                    .compile_run(&run, &format!("bad_tri_{change}"))
                    .unwrap_err()
                    .route,
                "TriangularDeterminant/OriginalZeroEntry"
            );
        }
    }
}

#[test]
fn triangular_determinants_preserve_diagonal_product_range_callback_domain_and_body() {
    for source in [UPPER, LOWER] {
        for change in [
            "product", "range", "start", "end", "target", "guard", "matrix", "diagonal",
        ] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let guard = b.requirements[0].clone();
            if change == "product" {
                goal(b).right = super::number_object("0");
            } else if change == "range" {
                let Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(p)) =
                    &mut goal(b).right
                else {
                    panic!()
                };
                let Obj::SetFormer(SetFormer::ClosedRange(range)) = p.set.as_mut() else {
                    panic!()
                };
                range.start = Box::new(super::number_object("0"));
            } else {
                let g = callback(b);
                match change {
                    "start" | "end" => {
                        let Obj::SetFormer(SetFormer::ClosedRange(range)) =
                            g.body.set_bound_parameters.groups[0].param_type.as_mut()
                        else {
                            panic!()
                        };
                        if change == "start" {
                            range.start = Box::new(super::number_object("0"));
                        } else {
                            range.end = Box::new(super::number_object("99"));
                        }
                    }
                    "target" => g.body.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
                    "guard" => {
                        let Fact::AtomicFact(guard) = guard else {
                            panic!()
                        };
                        g.body.dom_facts.push(QuantifierFreeFact::AtomicFact(guard));
                    }
                    _ => {
                        let Obj::FnObj(call) = g.equal_to.as_mut() else {
                            panic!()
                        };
                        if change == "matrix" {
                            call.head = Box::new(FnObjHead::from_obj(super::number_object("0")));
                        } else {
                            call.body[0][1] = Box::new(super::number_object("1"));
                        }
                    }
                }
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_tri_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn triangular_determinants_retain_original_determinant_and_each_equality_wd_subject() {
    for source in [UPPER, LOWER] {
        for change in ["matrix", "order", "wd_left", "wd_right", "wd_order"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            if change.starts_with("wd") {
                let FactWellDefinedProof::Equality(wd) = &mut call.conclusions_wd[0] else {
                    panic!()
                };
                let wd = wd.as_detailed_mut().unwrap();
                if change == "wd_order" {
                    std::mem::swap(&mut wd.left, &mut wd.right);
                } else {
                    let child = if change == "wd_left" {
                        &mut wd.left
                    } else {
                        &mut wd.right
                    };
                    let DetailedObjWellDefinedProof::ByDef { obj, .. } =
                        child.as_detailed_mut().unwrap()
                    else {
                        panic!()
                    };
                    *obj = super::number_object("0");
                }
            } else {
                let b = call.builtin.as_mut().unwrap();
                let Obj::MatrixOperator(MatrixOperator::Determinant(d)) = &mut goal(b).left else {
                    panic!()
                };
                if change == "matrix" {
                    d.matrix = Box::new(super::number_object("0"));
                } else {
                    d.order = Box::new(super::number_object("99"));
                }
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_tri_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn triangular_determinants_require_original_native_schema_rule_and_call_arguments() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for source in [UPPER, LOWER] {
        for change in ["rule", "derivation", "args"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "rule" => {
                    call.builtin.as_mut().unwrap().theorem =
                        crate::builtin_theorem::BuiltinTheoremId::MatrixDetMul
                }
                "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
                _ => call.builtin.as_mut().unwrap().arguments.swap(0, 1),
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_tri_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}
