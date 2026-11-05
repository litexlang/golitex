use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

const ROW: &str = r#"# Expand a finite complex determinant along a chosen row.
thm checked_laplace_row_preparation:
    ? forall n N+, A matrix(C,n,n), row closed_range(1,n):
        det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C{A(row,k)*matrix_cofactor(A,n,row,k)})
    release thm matrix_det_laplace_row(A,n,row)
"#;
const COLUMN: &str = r#"# Expand a finite complex determinant along a chosen column.
thm checked_laplace_column_preparation:
    ? forall n N+, A matrix(C,n,n), col closed_range(1,n):
        det(A,n)=finite_set_sum(closed_range(1,n),fn(k closed_range(1,n)) C{A(k,col)*matrix_cofactor(A,n,k,col)})
    release thm matrix_det_laplace_column(A,n,col)
"#;
fn goal(b: &mut BuiltinThmApplication) -> &mut EqualFact {
    let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.conclusions[0] else {
        panic!()
    };
    f
}
fn callback(b: &mut BuiltinThmApplication) -> &mut AnonymousFn {
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(p)) = &mut goal(b).right else {
        panic!()
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(g)) = p.func.as_mut() else {
        panic!()
    };
    g
}
fn product(b: &mut BuiltinThmApplication) -> &mut Mul {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = callback(b).equal_to.as_mut() else {
        panic!()
    };
    p
}

#[test]
fn laplace_determinants_require_five_ordered_proofs_stores_and_output_wd() {
    for source in [ROW, COLUMN] {
        for change in [
            "proof",
            "store",
            "repeat",
            "positive",
            "wd",
            "conclusion",
            "order",
        ] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            assert_eq!(call.dom_proofs.len(), 5);
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
                "positive" => {
                    call.builtin.as_mut().unwrap().requirements.remove(3);
                }
                "wd" => call.conclusions_wd.clear(),
                "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
                _ => call.dom_proofs.swap(3, 4),
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_laplace_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn laplace_determinants_retain_square_complex_carrier_and_exact_positive_index() {
    for source in [ROW, COLUMN] {
        for change in [
            "natural0",
            "natural1",
            "carrier",
            "rows",
            "cols",
            "positive",
            "index",
            "index_start",
            "index_end",
            "fact_id",
        ] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = match change {
                "natural0" => 0,
                "natural1" => 1,
                "positive" => 3,
                "index" | "index_start" | "index_end" => 4,
                _ => 2,
            };
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[index] else {
                panic!()
            };
            match change {
                "natural0" | "natural1" | "positive" => f.set = Obj::StandardSet(StandardSet::Z),
                "index" => f.element = super::number_object("0"),
                "fact_id" => f.fact_id = FactId::new(u64::MAX),
                "index_start" | "index_end" => {
                    let Obj::SetFormer(SetFormer::ClosedRange(r)) = &mut f.set else {
                        panic!()
                    };
                    if change == "index_start" {
                        r.start = Box::new(super::number_object("0"));
                    } else {
                        r.end = Box::new(super::number_object("99"));
                    }
                }
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
                    .compile_run(&run, &format!("bad_laplace_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn laplace_determinants_retain_original_sum_and_callback_domain() {
    for source in [ROW, COLUMN] {
        for change in [
            "sum", "range", "binder", "start", "end", "target", "guard", "body",
        ] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let guard = b.requirements[0].clone();
            if change == "sum" {
                goal(b).right = super::number_object("0");
            } else if change == "range" {
                let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) = &mut goal(b).right
                else {
                    panic!()
                };
                let Obj::SetFormer(SetFormer::ClosedRange(r)) = s.set.as_mut() else {
                    panic!()
                };
                r.start = Box::new(super::number_object("0"));
            } else {
                let g = callback(b);
                match change {
                    "binder" => g.body.set_bound_parameters.groups[0].params.clear(),
                    "start" | "end" => {
                        let Obj::SetFormer(SetFormer::ClosedRange(r)) =
                            g.body.set_bound_parameters.groups[0].param_type.as_mut()
                        else {
                            panic!()
                        };
                        if change == "start" {
                            r.start = Box::new(super::number_object("0"));
                        } else {
                            r.end = Box::new(super::number_object("99"));
                        }
                    }
                    "target" => g.body.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
                    "guard" => {
                        let Fact::AtomicFact(f) = guard else { panic!() };
                        g.body.dom_facts.push(QuantifierFreeFact::AtomicFact(f));
                    }
                    _ => g.equal_to = Box::new(super::number_object("0")),
                }
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_laplace_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn laplace_determinants_reject_transposed_or_changed_matrix_entries_and_cofactors() {
    for source in [ROW, COLUMN] {
        for change in [
            "entry_source",
            "entry_order",
            "entry_index",
            "cofactor_source",
            "cofactor_size",
            "cofactor_order",
            "cofactor_index",
            "product_order",
        ] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let p = product(b);
            if change == "product_order" {
                std::mem::swap(&mut p.left, &mut p.right);
            } else if change.starts_with("entry") {
                let Obj::FnObj(f) = p.left.as_mut() else {
                    panic!()
                };
                match change {
                    "entry_source" => {
                        f.head = Box::new(FnObjHead::from_obj(super::number_object("0")))
                    }
                    "entry_order" => f.body[0].swap(0, 1),
                    _ => f.body[0][0] = Box::new(super::number_object("0")),
                }
            } else {
                let Obj::MatrixOperator(MatrixOperator::Cofactor(c)) = p.right.as_mut() else {
                    panic!()
                };
                match change {
                    "cofactor_source" => c.matrix = Box::new(super::number_object("0")),
                    "cofactor_size" => c.order = Box::new(super::number_object("99")),
                    "cofactor_order" => std::mem::swap(&mut c.row, &mut c.col),
                    _ => c.row = Box::new(super::number_object("0")),
                }
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_laplace_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn laplace_determinants_retain_original_determinant_and_both_wd_subjects() {
    for source in [ROW, COLUMN] {
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
                let Obj::MatrixOperator(MatrixOperator::Determinant(d)) =
                    &mut goal(call.builtin.as_mut().unwrap()).left
                else {
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
                    .compile_run(&run, &format!("bad_laplace_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn laplace_determinants_reject_future_citations_and_reordered_stores() {
    for source in [ROW, COLUMN] {
        for change in ["future", "stores"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            if change == "stores" {
                call.dom_stores.swap(0, 1);
            } else {
                let id = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
                let child = super::atomic_proof_mut(&mut call.dom_proofs[2]);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut child.searched_proof
                else {
                    panic!("original matrix assumption")
                };
                cite.cite_fact_id = id;
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_laplace_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn laplace_determinants_require_native_derivation_and_exact_original_arguments() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for source in [ROW, COLUMN] {
        for change in ["rule", "derivation", "args", "index"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "rule" => {
                    call.builtin.as_mut().unwrap().theorem =
                        crate::builtin_theorem::BuiltinTheoremId::MatrixDetMul
                }
                "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
                "args" => call.builtin.as_mut().unwrap().arguments.swap(0, 1),
                _ => call.builtin.as_mut().unwrap().arguments[2] = super::number_object("0"),
            }
            assert!(
                compiler
                    .compile_run(&run, &format!("bad_laplace_{change}"))
                    .is_err(),
                "{change}"
            );
        }
    }
}
