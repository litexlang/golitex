use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;
const GENERIC: &str = r#"# Scaling a finite complex vector scales its Euclidean norm by the scalar modulus.
thm checked_euclidean_norm_scale:
    ? forall n N, v cart_n(C, n), a C:
        euclidean_norm(fn(k closed_range(1, n)) C{a * v(k)}, n) = C_abs(a) * euclidean_norm(v, n)
    release thm euclidean_norm_scale(a, v, n)
"#;
const SELECTED: &str = r#"# Select norm scaling by the zero scalar in every finite dimension.
thm checked_euclidean_norm_scale_zero_selected:
    ? forall n N, v cart_n(C, n):
        euclidean_norm(fn(k closed_range(1, n)) C{0 * v(k)}, n) = C_abs(0) * euclidean_norm(v, n)
    by thm euclidean_norm_scale(0, v, n) => euclidean_norm(fn(k closed_range(1, n)) C{0 * v(k)}, n) = C_abs(0) * euclidean_norm(v, n)
"#;
const EMPTY: &str = r#"# Scaling an empty complex vector also admits a non-real scalar.
thm checked_euclidean_norm_scale_empty:
    ? forall v cart_n(C, 0):
        euclidean_norm(fn(k closed_range(1, 0)) C{i * v(k)}, 0) = C_abs(i) * euclidean_norm(v, 0)
    release thm euclidean_norm_scale(i, v, 0)
"#;

#[test]
fn norm_scale_replays_complex_scalars_selected_zero_and_empty_dimensions() {
    for source in [GENERIC, SELECTED, EMPTY] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "norm_scale").unwrap();
        assert!(output.contains("Litex.euclideanNormScale"));
        assert_eq!(output, compiler.compile_run(&run, "norm_scale").unwrap());
    }
    let (mut run, _) = super::execute(GENERIC);
    assert_eq!(
        invocation(&mut run).builtin.as_ref().unwrap().theorem,
        BuiltinTheoremId::EuclideanNormScale
    );
}
#[test]
fn norm_scale_requires_original_scalar_dimension_vector_proofs_stores_and_wd() {
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
            "args" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
            "proof" => p.dom_proofs.clear(),
            "proof_order" => p.dom_proofs.swap(0, 1),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(0, 1),
            "wd" => p.conclusions_wd.clear(),
            "conclusion" => p.builtin.as_mut().unwrap().conclusions.clear(),
            _ => std::mem::swap(&mut p.type_proofs, &mut p.dom_proofs),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("preserve the original three-stage builtin pipeline");
    }
    for index in 0..3 {
        let (mut run, compiler) = super::execute(GENERIC);
        let Fact::AtomicFact(AtomicFact::InFact(f)) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[index]
        else {
            panic!()
        };
        f.set = Obj::StandardSet(StandardSet::R);
        compiler
            .compile_run(&run, "requirement")
            .expect_err("original domains are mandatory");
    }
}
#[test]
fn norm_scale_preserves_exact_coordinate_function_and_modulus_norm_arguments() {
    for change in [
        "dimension",
        "rhs",
        "modulus",
        "original_vector",
        "body",
        "start",
        "end",
        "carrier",
        "guards",
        "binder",
        "call",
        "scalar",
    ] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let guard = p.requirements[0].clone();
        let Fact::AtomicFact(AtomicFact::EqualFact(goal)) = &mut p.conclusions[0] else {
            panic!()
        };
        if change == "rhs" {
            goal.right = super::number_object("0");
        } else if change == "modulus" || change == "original_vector" {
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = &mut goal.right else {
                panic!()
            };
            if change == "modulus" {
                product.left = Box::new(super::number_object("1"));
            } else {
                let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(norm)) =
                    product.right.as_mut()
                else {
                    panic!()
                };
                norm.vector = Box::new(super::number_object("0"));
            }
        } else {
            let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(norm)) = &mut goal.left else {
                panic!()
            };
            if change == "dimension" {
                norm.dimension = Box::new(super::number_object("0"));
            } else {
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = norm.vector.as_mut() else {
                    panic!()
                };
                match change {
                    "body" => f.equal_to = Box::new(super::number_object("0")),
                    "start" | "end" => {
                        let Obj::SetFormer(SetFormer::ClosedRange(range)) =
                            f.body.set_bound_parameters.groups[0].param_type.as_mut()
                        else {
                            panic!()
                        };
                        if change == "start" {
                            range.start = Box::new(super::number_object("0"));
                        } else {
                            range.end = Box::new(super::number_object("1"));
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
                    "call" | "scalar" => {
                        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) =
                            f.equal_to.as_mut()
                        else {
                            panic!()
                        };
                        if change == "call" {
                            product.right = Box::new(super::number_object("0"));
                        } else {
                            product.left = Box::new(super::number_object("1"));
                        }
                    }
                    _ => panic!(),
                }
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("retain original function/scalar/norm subjects");
    }
}
#[test]
fn norm_scale_cannot_use_its_future_norm_equation_for_the_scalar_membership() {
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
        .expect_err("no future conclusion may enter the prerequisite scope");
}
