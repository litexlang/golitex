use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;

const GENERIC: &str = r#"# The complex inner product is linear in its second vector.
thm checked_inner_product_linear_right:
    ? forall n N, u, v, w cart_n(C, n), a, b C:
        inner_product(u, fn(k closed_range(1, n)) C{a * v(k) + b * w(k)}, n) = a * inner_product(u, v, n) + b * inner_product(u, w, n)
    release thm inner_product_linear_right(u, v, w, a, b, n)
"#;
const SELECTED: &str = r#"# Select the original builtin equality for linearity in the second vector.
thm checked_inner_product_linear_right_selected:
    ? forall n N, u, v, w cart_n(C, n), a, b C:
        inner_product(u, fn(k closed_range(1, n)) C{a * v(k) + b * w(k)}, n) = a * inner_product(u, v, n) + b * inner_product(u, w, n)
    by thm inner_product_linear_right(u, v, w, a, b, n) => inner_product(u, fn(k closed_range(1, n)) C{a * v(k) + b * w(k)}, n) = a * inner_product(u, v, n) + b * inner_product(u, w, n)
"#;
const EMPTY: &str = r#"# Linearity also holds for vectors with an empty coordinate domain.
thm checked_inner_product_linear_right_empty:
    ? forall u, v, w cart_n(C, 0), a, b C:
        inner_product(u, fn(k closed_range(1, 0)) C{a * v(k) + b * w(k)}, 0) = a * inner_product(u, v, 0) + b * inner_product(u, w, 0)
    release thm inner_product_linear_right(u, v, w, a, b, 0)
"#;

#[test]
fn inner_linear_replays_release_selected_and_empty_dimension() {
    for source in [GENERIC, SELECTED, EMPTY] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "linear").unwrap();
        assert!(output.contains("Litex.finiteInnerProductLinearRight"));
        assert_eq!(output, compiler.compile_run(&run, "linear").unwrap());
    }
    let (mut run, _) = super::execute(GENERIC);
    assert_eq!(
        invocation(&mut run).builtin.as_ref().unwrap().theorem,
        BuiltinTheoremId::InnerProductLinearRight
    );
}

#[test]
fn inner_linear_preserves_eight_original_prerequisites_and_formation() {
    for change in [
        "args",
        "proof",
        "proof_order",
        "store",
        "store_order",
        "wd",
        "conclusion",
        "types",
    ] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run);
        match change {
            "args" => p.builtin.as_mut().unwrap().arguments.swap(1, 2),
            "proof" => p.dom_proofs.clear(),
            "proof_order" => p.dom_proofs.swap(1, 3),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(1, 3),
            "wd" => p.conclusions_wd.clear(),
            "conclusion" => p.builtin.as_mut().unwrap().conclusions.clear(),
            _ => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("original stages and IDs must match");
    }
}

#[test]
fn inner_linear_rejects_changed_vector_scalar_and_dimension_requirements() {
    for index in 0..8 {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[index] else {
            panic!()
        };
        f.set = Obj::StandardSet(StandardSet::R);
        compiler
            .compile_run(&run, "requirement")
            .expect_err("all eight original domains are required");
    }
}

#[test]
fn inner_linear_retains_exact_binder_domain_body_and_rhs() {
    for change in [
        "left",
        "dimension",
        "right",
        "start",
        "end",
        "carrier",
        "guards",
        "binder",
        "body",
        "call",
        "scalar",
    ] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let guard = p.requirements[0].clone();
        let Fact::AtomicFact(AtomicFact::EqualFact(goal)) = &mut p.conclusions[0] else {
            panic!()
        };
        if change == "right" {
            goal.right = Obj::StandardSet(StandardSet::R);
        } else {
            let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = &mut goal.left else {
                panic!()
            };
            if change == "left" {
                inner.left = Box::new(Obj::StandardSet(StandardSet::R));
            } else if change == "dimension" {
                inner.dimension = Box::new(super::number_object("1"));
            } else {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = inner.right.as_mut() else {
                    panic!()
                };
                match change {
                    "start" | "end" => {
                        let Obj::SetFormer(SetFormer::ClosedRange(r)) =
                            f.body.set_bound_parameters.groups[0].param_type.as_mut()
                        else {
                            panic!()
                        };
                        if change == "start" {
                            r.start = Box::new(super::number_object("0"));
                        } else {
                            r.end = Box::new(super::number_object("2"));
                        }
                    }
                    "carrier" => f.body.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
                    "guards" => {
                        let Fact::AtomicFact(guard) = guard else {
                            panic!()
                        };
                        f.body.dom_facts.push(QuantifierFreeFact::AtomicFact(guard));
                    }
                    "binder" => f.body.set_bound_parameters.groups[0].params.clear(),
                    "body" => f.equal_to = Box::new(super::number_object("0")),
                    "call" | "scalar" => {
                        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) =
                            f.equal_to.as_mut()
                        else {
                            panic!()
                        };
                        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) =
                            sum.left.as_mut()
                        else {
                            panic!()
                        };
                        if change == "scalar" {
                            mul.left = Box::new(super::number_object("2"));
                        } else {
                            mul.right = Box::new(super::number_object("2"));
                        }
                    }
                    _ => panic!(),
                }
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("linearity cannot certify another expression or captured binder");
    }
}

#[test]
fn inner_linear_rejects_future_conclusion_citation() {
    let (mut run, compiler) = super::execute(GENERIC);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler
        .compile_run(&run, "future")
        .expect_err("conclusions are invisible in prerequisite scope");
}

#[test]
fn inner_alpha_requires_exact_free_vectors_dimension_domain_and_coordinate_body() {
    use super::super::source_position::{SourceOwner, SourcePosition};
    let source = r#"# Renaming a coordinate binder preserves a finite inner product.
thm checked_vector_bound_names:
    ? forall n N, u, v cart_n(C, n), a C:
        inner_product(u, fn(k closed_range(1, n)) C{a * v(k)}, n) = inner_product(u, fn(j closed_range(1, n)) C{a * v(j)}, n)
    inner_product(u, fn(k closed_range(1, n)) C{a * v(k)}, n) = inner_product(u, fn(j closed_range(1, n)) C{a * v(j)}, n)
"#;
    let (run, compiler) = super::execute(source);
    compiler.compile_run(&run, "vector_alpha").unwrap();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(body) = &named.body else {
        panic!()
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &body.proof_steps[0] else {
        panic!()
    };
    let equality = super::equality_proof(&step.verify_result);
    let EqualFactSearchedProof::ByTheyAreTheSame(identity) = &equality.searched_proof else {
        panic!("original alpha identity")
    };
    let position = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    for change in ["body", "domain", "dimension", "vector"] {
        let mut right = equality.fact.right.clone();
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = &mut right else {
            panic!()
        };
        if change == "dimension" {
            inner.dimension = Box::new(super::number_object("0"));
        } else if change == "vector" {
            inner.left = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = inner.right.as_mut()
            else {
                panic!()
            };
            if change == "body" {
                function.equal_to = Box::new(super::number_object("99"));
            } else {
                function.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N));
            }
        }
        let error = compiler
            .compile_identity(&equality.fact.left, &right, identity, &position)
            .expect_err("alpha evidence permits only bound-name renaming");
        assert_eq!(error.route, "Equality/FiniteAggregateAlphaSubject");
    }
}
