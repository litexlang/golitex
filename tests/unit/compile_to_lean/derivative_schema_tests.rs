use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

const UNIQUE: &str = r#"# A coordinate partial derivative has a unique real value.
thm checked_partial_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), L, K R:
        $has_partial_derivative_at(f, p, 2, 1, L)
        $has_partial_derivative_at(f, p, 2, 1, K)
        =>:
            L = K
    release thm partial_at_unique(f, p, 2, 1, L, K)
"#;
const EXISTS: &str = r#"# A known coordinate partial derivative supplies an existential real witness.
thm checked_partial_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), L R:
        $has_partial_derivative_at(f, p, 2, 1, L)
        =>:
            exist value R st {$has_partial_derivative_at(f, p, 2, 1, value)}
    release thm partial_at_exists(f, p, 2, 1, L)
"#;
const SELECTED: &str = r#"# A partial-derivative selector consumes an original real derivative witness.
thm checked_partial_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):
        exist value R st {$has_partial_derivative_at(f, p, 2, 1, value)}
        =>:
            $has_partial_derivative_at(f, p, 2, 1, partial_derivative(f, p, 2, 1))
    release thm partial_at_selected(f, p, 2, 1)
"#;
const GUARDED: &str = r#"# Partial-derivative uniqueness retains membership in the actual guarded function domain.
thm checked_partial_builtin_guarded_unique:
    ? forall f fn(x cart_n(R, 2): x(1) > 0) R, p cart_n(R, 2), L, K R:
        p(1) > 0
        $has_partial_derivative_at(f, p, 2, 1, L)
        $has_partial_derivative_at(f, p, 2, 1, K)
        =>:
            L = K
    release thm partial_at_unique(f, p, 2, 1, L, K)
"#;
const SECOND_UNIQUE: &str = r#"# Second partial values are unique for the same ordered pair of coordinate directions.
thm checked_second_partial_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), L, K R:
        $has_second_partial_derivative_at(f, p, 2, 1, 2, L)
        $has_second_partial_derivative_at(f, p, 2, 1, 2, K)
        =>:
            L = K
    release thm second_partial_at_unique(f, p, 2, 1, 2, L, K)
"#;
const SECOND_EXISTS: &str = r#"# A second partial supplies a real witness without interchanging the coordinate directions.
thm checked_second_partial_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), L R:
        $has_second_partial_derivative_at(f, p, 2, 1, 2, L)
        =>:
            exist value R st {$has_second_partial_derivative_at(f, p, 2, 1, 2, value)}
    release thm second_partial_at_exists(f, p, 2, 1, 2, L)
"#;
const GRADIENT_UNIQUE: &str = r#"# A real scalar field has a unique gradient vector in the declared input dimension.
thm checked_gradient_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), g, h cart_n(R, 2):
        $has_gradient_at(f, p, 2, g)
        $has_gradient_at(f, p, 2, h)
        =>:
            g = h
    release thm gradient_at_unique(f, p, 2, g, h)
"#;
const GRADIENT_EXISTS: &str = r#"# A gradient candidate supplies a vector witness in the original input dimension.
thm checked_gradient_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), g cart_n(R, 2):
        $has_gradient_at(f, p, 2, g)
        =>:
            exist value cart_n(R, 2) st {$has_gradient_at(f, p, 2, value)}
    release thm gradient_at_exists(f, p, 2, g)
"#;
const GRADIENT_SELECTED: &str = r#"# The gradient selector consumes an original vector witness for the same scalar field and point.
thm checked_gradient_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):
        exist value cart_n(R, 2) st {$has_gradient_at(f, p, 2, value)}
        =>:
            $has_gradient_at(f, p, 2, gradient_at(f, p, 2))
    release thm gradient_at_selected(f, p, 2)
"#;
const JACOBIAN_UNIQUE: &str = r#"# A Jacobian retains three output rows and two input-coordinate columns.
thm checked_jacobian_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), A, B matrix(R, 3, 2):
        $has_jacobian_at(f, p, 2, 3, A)
        $has_jacobian_at(f, p, 2, 3, B)
        =>:
            A = B
    release thm jacobian_at_unique(f, p, 2, 3, A, B)
"#;
const JACOBIAN_EXISTS: &str = r#"# The Jacobian witness has output rows and input columns in their original order.
thm checked_jacobian_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), A matrix(R, 3, 2):
        $has_jacobian_at(f, p, 2, 3, A)
        =>:
            exist value matrix(R, 3, 2) st {$has_jacobian_at(f, p, 2, 3, value)}
    release thm jacobian_at_exists(f, p, 2, 3, A)
"#;
const JACOBIAN_SELECTED: &str = r#"# The Jacobian selector preserves the output-row/input-column matrix shape.
thm checked_jacobian_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2):
        exist value matrix(R, 3, 2) st {$has_jacobian_at(f, p, 2, 3, value)}
        =>:
            $has_jacobian_at(f, p, 2, 3, jacobian(f, p, 2, 3))
    release thm jacobian_at_selected(f, p, 2, 3)
"#;

#[test]
fn unary_derivative_elementary_builtins_reject_erased_positivity_and_wrong_factor() {
    for change in ["positive", "factor", "body", "future"] {
        let (mut run, compiler) = super::execute(
            r#"# An elementary formula is differentiated only on its original real domain.
thm checked_unary_derivative_builtin_sqrt:
    ? forall f fn(x R+) R, p R+:
        exist radius R+ st {{x R: abs(x-p)<radius} $subset R+}
        forall x R+:
            f(x)=sqrt(x)
        =>:
            $has_derivative_at(f,p,1/2/sqrt(p))
    release thm fn_derivative_at_sqrt(f,p)
"#,
        );
        let p = invocation(&mut run);
        match change {
            "positive" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[5]
                else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            "factor" => {
                let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!()
                };
                f.value = super::number_object("0");
            }
            "body" => {
                let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[6] else {
                    panic!()
                };
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut f.then_facts[0]
                else {
                    panic!()
                };
                eq.right = super::number_object("0");
            }
            _ => {
                let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
                super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
                    AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                        AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                            cite_fact_id: future,
                            why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
                        },
                    );
            }
        }
        compiler.compile_run(&run,change).expect_err("the original positive point, exact elementary body/factor and citation scope are retained");
    }
}

#[test]
fn unary_derivative_formulas_reject_wrong_body_interior_and_coefficient() {
    for change in ["formula", "interior", "coefficient", "formation"] {
        let (mut run, compiler) = super::execute(
            r#"# A constant formula on the original domain has zero derivative at an interior point.
thm checked_unary_derivative_builtin_constant:
    ? forall f fn(x R) R, p R, c R:
        exist radius R+ st {{x R: abs(x-p)<radius} $subset R}
        forall x R:
            f(x)=c
        =>:
            $has_derivative_at(f,p,0)
    release thm fn_derivative_at_constant(f,p,c)
"#,
        );
        let p = invocation(&mut run);
        match change {
            "formula" => {
                let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[6] else {
                    panic!()
                };
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut f.then_facts[0]
                else {
                    panic!()
                };
                eq.right = super::number_object("0");
            }
            "interior" => {
                let Fact::ExistFact(f) = &mut p.builtin.as_mut().unwrap().requirements[4] else {
                    panic!()
                };
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            }
            "coefficient" => {
                let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!()
                };
                f.value = super::number_object("1");
            }
            _ => p.conclusions_wd.clear(),
        }
        compiler.compile_run(&run,change).expect_err("the original formula, positive interior radius, coefficient and output WD are mandatory");
    }
}

#[test]
fn unary_derivative_continuity_rejects_changed_side_point_and_source_context() {
    for change in ["side", "point", "context"] {
        let (mut run, compiler) = super::execute(
            r#"# Differentiability and continuity retain the actual function and point domain.
thm checked_unary_derivative_builtin_continuous:
    ? forall f fn(x R) R, p R, a R:
        $has_derivative_at(f,p,a)
        =>:
            $is_continuous_at(f,p)
    release thm fn_derivative_at_continuous(f,p,a)
"#,
        );
        let p = invocation(&mut run);
        if change == "context" {
            p.dom_stores.swap(0, 3);
        } else {
            let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) =
                &mut p.builtin.as_mut().unwrap().conclusions[0]
            else {
                panic!()
            };
            if change == "side" {
                f.side = RealApproachSide::Left;
            } else {
                f.point = super::number_object("0");
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("continuity keeps its original side, point and ordered prerequisites");
    }
    let (mut run, compiler) = super::execute(
        r#"# Differentiability and continuity retain the actual function and point domain.
thm checked_unary_differentiable_builtin_continuous:
    ? forall f fn(x R) R, p R:
        $is_differentiable_at(f,p)
        =>:
            $is_continuous_at(f,p)
    release thm fn_differentiable_at_continuous(f,p)
"#,
    );
    let Fact::AtomicFact(AtomicFact::FunctionDifferentiableAtFact(f)) =
        &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[4]
    else {
        panic!()
    };
    f.point = super::number_object("0");
    compiler
        .compile_run(&run, "different_differentiability_point")
        .expect_err("differentiability must concern the original point");
}

#[test]
fn unary_derivative_standard_interiors_reject_changed_carrier_ball_and_output_wd() {
    let source = r#"# An open standard real domain contains a ball around each of its points.
thm checked_unary_derivative_positive_interior:
    ? forall p R+:
        exist radius R+ st {{x R: abs(x-p)<radius} $subset R+}
    release thm fn_derivative_at_positive_interior(p)
"#;
    for change in ["carrier", "ball", "output_wd", "future"] {
        let (mut run, compiler) = super::execute(source);
        let p = invocation(&mut run);
        match change {
            "carrier" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[0]
                else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            "ball" => {
                let Fact::ExistFact(f) = &mut p.builtin.as_mut().unwrap().conclusions[0] else {
                    panic!()
                };
                let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(s)) = &mut f.facts[0]
                else {
                    panic!()
                };
                s.right = Obj::StandardSet(StandardSet::R);
            }
            "output_wd" => p.conclusions_wd.clear(),
            _ => {
                let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
                super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
                    AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
                        AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                            cite_fact_id: future,
                            why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
                        },
                    );
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "open-carrier membership, exact ball, output WD and source order are mandatory",
        );
    }
}
#[test]
fn unary_derivative_builtins_reject_reordered_context_and_value_candidates() {
    for change in ["context", "candidate", "output_wd"] {
        let (mut run, compiler) = super::execute(
            r#"# A unary real derivative preserves the original candidate, point and function domain.
thm checked_unary_derivative_builtin_unique:
    ? forall f fn(x R) R, p R, a, b R:
        $has_derivative_at(f,p,a)
        $has_derivative_at(f,p,b)
        =>:
            a = b
    release thm fn_derivative_at_unique(f,p,a,b)
"#,
        );
        let p = invocation(&mut run);
        if change == "context" {
            p.dom_proofs.swap(0, 3);
        } else if change == "output_wd" {
            p.conclusions_wd.clear();
        } else {
            let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[5]
            else {
                panic!()
            };
            f.value = super::number_object("0");
        }
        compiler.compile_run(&run, change).expect_err(
            "original domain order, independent candidates and output formation remain mandatory",
        );
    }
}
#[test]
fn unary_derivative_builtins_reject_changed_witness_carrier_and_selector_point() {
    let (mut run, compiler) = super::execute(
        r#"# A unary real derivative preserves the original candidate, point and function domain.
thm checked_unary_derivative_builtin_exists:
    ? forall f fn(x R) R, p R, a R:
        $has_derivative_at(f,p,a)
        =>:
            exist value R st {$has_derivative_at(f,p,value)}
    release thm fn_derivative_at_exists(f,p,a)
"#,
    );
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::C));
    compiler
        .compile_run(&run, "complex_witness")
        .expect_err("derivative existence retains its original real witness carrier");
    let (mut run, compiler) = super::execute(
        r#"# A unary real derivative preserves the original candidate, point and function domain.
thm checked_unary_derivative_builtin_selected:
    ? forall f fn(x R) R, p R:
        exist value R st {$has_derivative_at(f,p,value)}
        =>:
            $has_derivative_at(f,p,derivative(f,p))
    release thm fn_derivative_at_selected(f,p)
"#,
    );
    let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) =
        &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    let Obj::DerivativeOperator(DerivativeOperator::AtPoint(p)) = &mut f.value else {
        panic!()
    };
    p.point = Box::new(super::number_object("0"));
    compiler
        .compile_run(&run, "changed_selector_point")
        .expect_err("selection consumes the original derivative constructor and point");
}
#[test]
fn unary_derivative_context_cannot_cite_its_future_equality() {
    let (mut run, compiler) = super::execute(
        r#"# A unary real derivative preserves the original candidate, point and function domain.
thm checked_unary_derivative_builtin_unique:
    ? forall f fn(x R) R, p R, a, b R:
        $has_derivative_at(f,p,a)
        $has_derivative_at(f,p,b)
        =>:
            a = b
    release thm fn_derivative_at_unique(f,p,a,b)
"#,
    );
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
        .compile_run(&run, "future_citation")
        .expect_err("all original function/point prerequisites precede the output");
}

#[test]
fn remainder_definition_partial_retains_both_ordered_clauses_and_wd() {
    for (source, law) in [
        (
            r#"# A coordinate derivative follows from the original local section and punctured quotient limit.
thm checked_partial_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
        exist radius R+ st {{t R: abs(t)<radius} $subset {h R: fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)}}
        $has_limit_at(fn(h R: h!=0, fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)) R {(f(fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)})-f(p))/h},0,L)
        =>:
            $has_partial_derivative_at(f,p,2,1,L)
    release thm partial_at_from_definition(f,p,2,1,L)
"#,
            "partialDerivativeOfClauses",
        ),
        (
            r#"# Expanding a coordinate derivative preserves both its local-section and quotient-limit clauses.
thm checked_partial_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
        $has_partial_derivative_at(f,p,2,1,L)
        =>:
            exist radius R+ st {{t R: abs(t)<radius} $subset {h R: fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)}}
            $has_limit_at(fn(h R: h!=0, fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)) R {(f(fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)})-f(p))/h},0,L)
    release thm partial_at_to_definition(f,p,2,1,L)
"#,
            "partialDerivativeClauses",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "partial_remainder")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# A coordinate derivative follows from the original local section and punctured quotient limit.
thm checked_partial_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
        exist radius R+ st {{t R: abs(t)<radius} $subset {h R: fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)}}
        $has_limit_at(fn(h R: h!=0, fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)) R {(f(fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)})-f(p))/h},0,L)
        =>:
            $has_partial_derivative_at(f,p,2,1,L)
    release thm partial_at_from_definition(f,p,2,1,L)
"#,
    );
    invocation(&mut run).dom_proofs.swap(6, 7);
    compiler
        .compile_run(&run, "partial_reordered_clauses")
        .expect_err(
            "the original interior and limit/remainder proofs keep their exact subjects and order",
        );
    let (mut run, compiler) = super::execute(
        r#"# Expanding a coordinate derivative preserves both its local-section and quotient-limit clauses.
thm checked_partial_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
        $has_partial_derivative_at(f,p,2,1,L)
        =>:
            exist radius R+ st {{t R: abs(t)<radius} $subset {h R: fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)}}
            $has_limit_at(fn(h R: h!=0, fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)) R {(f(fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)})-f(p))/h},0,L)
    release thm partial_at_to_definition(f,p,2,1,L)
"#,
    );
    invocation(&mut run)
        .builtin
        .as_mut()
        .unwrap()
        .conclusions
        .swap(0, 1);
    compiler
        .compile_run(&run, "partial_reordered_outputs")
        .expect_err("both defining outputs retain their original ordered formation");
    let (mut run, compiler) = super::execute(
        r#"# Expanding a coordinate derivative preserves both its local-section and quotient-limit clauses.
thm checked_partial_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
        $has_partial_derivative_at(f,p,2,1,L)
        =>:
            exist radius R+ st {{t R: abs(t)<radius} $subset {h R: fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)}}
            $has_limit_at(fn(h R: h!=0, fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)} $in cart_n(R,2)) R {(f(fn(k closed_range(1,2)) R {p(k)+h*identity_matrix(2)(k,1)})-f(p))/h},0,L)
    release thm partial_at_to_definition(f,p,2,1,L)
"#,
    );
    invocation(&mut run).conclusions_wd.pop();
    compiler
        .compile_run(&run, "partial_missing_output_wd")
        .expect_err("neither defining output can lose its original WD");
}

#[test]
fn remainder_definition_scalar_differential_retains_both_ordered_clauses_and_wd() {
    for (source, law) in [
        (
            r#"# The differential follows from the original interior ball and punctured remainder bound.
thm checked_scalar_differential_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), A matrix(R,1,2):
        exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
        forall epsilon R+:
            exist delta R+ st {{x cart_n(R,2): 0<euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2), euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<delta} $subset {y cart_n(R,2): abs(f(y)-f(p)-matrix_apply(A,fn(k closed_range(1,2)) R {y(k)-p(k)},1,2)(1))<epsilon*euclidean_norm(fn(k closed_range(1,2)) R {y(k)-p(k)},2)}}
        =>:
            $has_scalar_differential_at(f,p,2,A)
    release thm scalar_differential_at_from_definition(f,p,2,A)
"#,
            "scalarDifferentialOfClauses",
        ),
        (
            r#"# A differential preserves the original interior neighborhood as part of its full defining clauses.
thm checked_scalar_differential_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), A matrix(R,1,2):
        $has_scalar_differential_at(f,p,2,A)
        =>:
            exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
    release thm scalar_differential_at_to_definition(f,p,2,A)
"#,
            "scalarDifferentialClauses",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "scalar_differential_remainder")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# The differential follows from the original interior ball and punctured remainder bound.
thm checked_scalar_differential_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), A matrix(R,1,2):
        exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
        forall epsilon R+:
            exist delta R+ st {{x cart_n(R,2): 0<euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2), euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<delta} $subset {y cart_n(R,2): abs(f(y)-f(p)-matrix_apply(A,fn(k closed_range(1,2)) R {y(k)-p(k)},1,2)(1))<epsilon*euclidean_norm(fn(k closed_range(1,2)) R {y(k)-p(k)},2)}}
        =>:
            $has_scalar_differential_at(f,p,2,A)
    release thm scalar_differential_at_from_definition(f,p,2,A)
"#,
    );
    invocation(&mut run).dom_proofs.swap(5, 6);
    compiler
        .compile_run(&run, "scalar_differential_reordered_clauses")
        .expect_err(
            "the original interior and limit/remainder proofs keep their exact subjects and order",
        );
    let (mut run, compiler) = super::execute(
        r#"# A differential preserves the original interior neighborhood as part of its full defining clauses.
thm checked_scalar_differential_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), A matrix(R,1,2):
        $has_scalar_differential_at(f,p,2,A)
        =>:
            exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
    release thm scalar_differential_at_to_definition(f,p,2,A)
"#,
    );
    invocation(&mut run)
        .builtin
        .as_mut()
        .unwrap()
        .conclusions
        .swap(0, 1);
    compiler
        .compile_run(&run, "scalar_differential_reordered_outputs")
        .expect_err("both defining outputs retain their original ordered formation");
    let (mut run, compiler) = super::execute(
        r#"# A differential preserves the original interior neighborhood as part of its full defining clauses.
thm checked_scalar_differential_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), A matrix(R,1,2):
        $has_scalar_differential_at(f,p,2,A)
        =>:
            exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
    release thm scalar_differential_at_to_definition(f,p,2,A)
"#,
    );
    invocation(&mut run).conclusions_wd.pop();
    compiler
        .compile_run(&run, "scalar_differential_missing_output_wd")
        .expect_err("neither defining output can lose its original WD");
}

#[test]
fn remainder_definition_total_derivative_retains_both_ordered_clauses_and_wd() {
    for (source, law) in [
        (
            r#"# The differential follows from the original interior ball and punctured remainder bound.
thm checked_total_derivative_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), A matrix(R,3,2):
        exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
        forall epsilon R+:
            exist delta R+ st {{x cart_n(R,2): 0<euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2), euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<delta} $subset {y cart_n(R,2): euclidean_norm(fn(row closed_range(1,3)) R {f(y)(row)-f(p)(row)-matrix_apply(A,fn(k closed_range(1,2)) R {y(k)-p(k)},3,2)(row)},3)<epsilon*euclidean_norm(fn(k closed_range(1,2)) R {y(k)-p(k)},2)}}
        =>:
            $has_total_derivative_at(f,p,2,3,A)
    release thm total_derivative_at_from_definition(f,p,2,3,A)
"#,
            "totalDifferentialOfClauses",
        ),
        (
            r#"# A differential preserves the original interior neighborhood as part of its full defining clauses.
thm checked_total_derivative_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), A matrix(R,3,2):
        $has_total_derivative_at(f,p,2,3,A)
        =>:
            exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
    release thm total_derivative_at_to_definition(f,p,2,3,A)
"#,
            "totalDifferentialClauses",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "total_derivative_remainder")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# The differential follows from the original interior ball and punctured remainder bound.
thm checked_total_derivative_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), A matrix(R,3,2):
        exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
        forall epsilon R+:
            exist delta R+ st {{x cart_n(R,2): 0<euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2), euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<delta} $subset {y cart_n(R,2): euclidean_norm(fn(row closed_range(1,3)) R {f(y)(row)-f(p)(row)-matrix_apply(A,fn(k closed_range(1,2)) R {y(k)-p(k)},3,2)(row)},3)<epsilon*euclidean_norm(fn(k closed_range(1,2)) R {y(k)-p(k)},2)}}
        =>:
            $has_total_derivative_at(f,p,2,3,A)
    release thm total_derivative_at_from_definition(f,p,2,3,A)
"#,
    );
    invocation(&mut run).dom_proofs.swap(6, 7);
    compiler
        .compile_run(&run, "total_derivative_reordered_clauses")
        .expect_err(
            "the original interior and limit/remainder proofs keep their exact subjects and order",
        );
    let (mut run, compiler) = super::execute(
        r#"# A differential preserves the original interior neighborhood as part of its full defining clauses.
thm checked_total_derivative_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), A matrix(R,3,2):
        $has_total_derivative_at(f,p,2,3,A)
        =>:
            exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
    release thm total_derivative_at_to_definition(f,p,2,3,A)
"#,
    );
    invocation(&mut run)
        .builtin
        .as_mut()
        .unwrap()
        .conclusions
        .swap(0, 1);
    compiler
        .compile_run(&run, "total_derivative_reordered_outputs")
        .expect_err("both defining outputs retain their original ordered formation");
    let (mut run, compiler) = super::execute(
        r#"# A differential preserves the original interior neighborhood as part of its full defining clauses.
thm checked_total_derivative_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), A matrix(R,3,2):
        $has_total_derivative_at(f,p,2,3,A)
        =>:
            exist radius R+ st {{x cart_n(R,2): euclidean_norm(fn(k closed_range(1,2)) R {x(k)-p(k)},2)<radius} $subset cart_n(R,2)}
    release thm total_derivative_at_to_definition(f,p,2,3,A)
"#,
    );
    invocation(&mut run).conclusions_wd.pop();
    compiler
        .compile_run(&run, "total_derivative_missing_output_wd")
        .expect_err("neither defining output can lose its original WD");
}

#[test]
fn coordinate_definition_divergence_retains_defining_witness_and_inference() {
    for (source, law) in [
        (
            r#"# The divergence definition consumes the original diagonal derivative witness and finite sum.
thm checked_divergence_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,2), p cart_n(R,2), d R:
        exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_partial_derivative_at(fn(x cart_n(R,2)) R {f(x)(k)},p,2,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
        =>:
            $has_divergence_at(f,p,2,d)
    release thm divergence_at_from_definition(f, p, 2, d)
"#,
            "divergenceOfDiagonalPartials",
        ),
        (
            r#"# Expanding divergence recovers the original diagonal derivative witness and finite sum.
thm checked_divergence_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,2), p cart_n(R,2), d R:
        $has_divergence_at(f,p,2,d)
        =>:
            exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_partial_derivative_at(fn(x cart_n(R,2)) R {f(x)(k)},p,2,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
    release thm divergence_at_to_definition(f,p,2,d)
"#,
            "divergenceDiagonalPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "divergence_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# The divergence definition consumes the original diagonal derivative witness and finite sum.
thm checked_divergence_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,2), p cart_n(R,2), d R:
        exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_partial_derivative_at(fn(x cart_n(R,2)) R {f(x)(k)},p,2,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
        =>:
            $has_divergence_at(f,p,2,d)
    release thm divergence_at_from_definition(f, p, 2, d)
"#,
    );
    invocation(&mut run).dom_proofs.swap(0, 6);
    compiler
        .compile_run(&run, "divergence_reordered_witness")
        .expect_err("the defining witness remains after the original context proofs");
    let (mut run, compiler) = super::execute(
        r#"# Expanding divergence recovers the original diagonal derivative witness and finite sum.
thm checked_divergence_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) cart_n(R,2), p cart_n(R,2), d R:
        $has_divergence_at(f,p,2,d)
        =>:
            exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_partial_derivative_at(fn(x cart_n(R,2)) R {f(x)(k)},p,2,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
    release thm divergence_at_to_definition(f,p,2,d)
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[6].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.function_domain = None;
    compiler
        .compile_run(&run, "divergence_missing_definition_domain")
        .expect_err("unfolding consumes its original complete-domain capture");
}

#[test]
fn coordinate_definition_laplacian_retains_defining_witness_and_inference() {
    for (source, law) in [
        (
            r#"# The laplacian definition consumes the original diagonal derivative witness and finite sum.
thm checked_laplacian_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d R:
        exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_second_partial_derivative_at(f,p,2,k,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
        =>:
            $has_laplacian_at(f,p,2,d)
    release thm laplacian_at_from_definition(f, p, 2, d)
"#,
            "laplacianOfDiagonalPartials",
        ),
        (
            r#"# Expanding laplacian recovers the original diagonal derivative witness and finite sum.
thm checked_laplacian_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d R:
        $has_laplacian_at(f,p,2,d)
        =>:
            exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_second_partial_derivative_at(f,p,2,k,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
    release thm laplacian_at_to_definition(f,p,2,d)
"#,
            "laplacianDiagonalPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "laplacian_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# The laplacian definition consumes the original diagonal derivative witness and finite sum.
thm checked_laplacian_builtin_from_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d R:
        exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_second_partial_derivative_at(f,p,2,k,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
        =>:
            $has_laplacian_at(f,p,2,d)
    release thm laplacian_at_from_definition(f, p, 2, d)
"#,
    );
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "laplacian_reordered_witness")
        .expect_err("the defining witness remains after the original context proofs");
    let (mut run, compiler) = super::execute(
        r#"# Expanding laplacian recovers the original diagonal derivative witness and finite sum.
thm checked_laplacian_builtin_to_definition:
    ? forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d R:
        $has_laplacian_at(f,p,2,d)
        =>:
            exist v cart_n(R,2) st {closed_range(1,2) $subset {k closed_range(1,2): $has_second_partial_derivative_at(f,p,2,k,k,v(k))}, finite_set_sum(closed_range(1,2),v)=d}
    release thm laplacian_at_to_definition(f,p,2,d)
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[5].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.function_domain = None;
    compiler
        .compile_run(&run, "laplacian_missing_definition_domain")
        .expect_err("unfolding consumes its original complete-domain capture");
}

#[test]
fn coordinate_definition_curl_retains_defining_witness_and_inference() {
    for (source, law) in [
        (
            r#"# Curl's defining witness keeps all six partial derivatives and their orientation.
thm checked_curl_builtin_from_definition:
    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):
        exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}
        =>:
            $has_curl_at(f,p,c)
    release thm curl_at_from_definition(f,p,c)
"#,
            "curlOfCoordinatePartials",
        ),
        (
            r#"# Expanding curl recovers the same ordered six partials and three signed coordinate differences.
thm checked_curl_builtin_to_definition:
    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):
        $has_curl_at(f,p,c)
        =>:
            exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}
    release thm curl_at_to_definition(f,p,c)
"#,
            "curlCoordinatePartials",
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        let original = invocation(&mut run);
        let expected = if law == "curlOfCoordinatePartials" {
            crate::builtin_theorem::BuiltinTheoremId::CurlAtFromDefinition
        } else {
            crate::builtin_theorem::BuiltinTheoremId::CurlAtToDefinition
        };
        assert_eq!(original.builtin.as_ref().unwrap().theorem, expected);
        assert!(matches!(
            original.theorem_derivation,
            crate::execute::execute_by_stmt::TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(original.dom_proofs.len(), 7);
        assert_eq!(original.dom_stores.len(), 7);
        assert!(compiler
            .compile_run(&run, "curl_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# Curl's defining witness keeps all six partial derivatives and their orientation.
thm checked_curl_builtin_from_definition:
    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):
        exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}
        =>:
            $has_curl_at(f,p,c)
    release thm curl_at_from_definition(f,p,c)
"#,
    );
    invocation(&mut run).dom_proofs.swap(0, 6);
    compiler
        .compile_run(&run, "curl_reordered_witness")
        .expect_err("the defining witness remains after the original context proofs");
    let (mut run, compiler) = super::execute(
        r#"# Expanding curl recovers the same ordered six partials and three signed coordinate differences.
thm checked_curl_builtin_to_definition:
    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):
        $has_curl_at(f,p,c)
        =>:
            exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}
    release thm curl_at_to_definition(f,p,c)
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[6].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.function_domain = None;
    compiler
        .compile_run(&run, "curl_missing_definition_domain")
        .expect_err("unfolding consumes its original complete-domain capture");
}

#[test]
fn coordinate_definition_jacobian_keeps_component_domain_and_matrix_orientation() {
    for (source, law) in [
        (
            r#"# A rectangular Jacobian records the component partials with output rows and input columns.
thm checked_jacobian_builtin_from_definition:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), J matrix(R, 3, 2):
        forall row closed_range(1, 3), col closed_range(1, 2):
            $has_partial_derivative_at(fn(x cart_n(R, 2)) R {f(x)(row)}, p, 2, col, J(row, col))
        =>:
            $has_jacobian_at(f, p, 2, 3, J)
    release thm jacobian_at_from_definition(f, p, 2, 3, J)
"#,
            "jacobianOfComponentPartials",
        ),
        (
            r#"# Each Jacobian entry retains its component function and ordered matrix coordinates.
thm checked_jacobian_builtin_to_definition:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), J matrix(R, 3, 2), row closed_range(1, 3), col closed_range(1, 2):
        $has_jacobian_at(f, p, 2, 3, J)
        =>:
            $has_partial_derivative_at(fn(x cart_n(R, 2)) R {f(x)(row)}, p, 2, col, J(row, col))
    release thm jacobian_at_to_definition(f, p, 2, 3, J)
    $has_partial_derivative_at(fn(x cart_n(R, 2)) R {f(x)(row)}, p, 2, col, J(row, col))
"#,
            "jacobianComponentPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "jacobian_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# Each Jacobian entry retains its component function and ordered matrix coordinates.
thm checked_jacobian_builtin_to_definition:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), J matrix(R, 3, 2), row closed_range(1, 3), col closed_range(1, 2):
        $has_jacobian_at(f, p, 2, 3, J)
        =>:
            $has_partial_derivative_at(fn(x cart_n(R, 2)) R {f(x)(row)}, p, 2, col, J(row, col))
    release thm jacobian_at_to_definition(f, p, 2, 3, J)
    $has_partial_derivative_at(fn(x cart_n(R, 2)) R {f(x)(row)}, p, 2, col, J(row, col))
"#,
    );
    let Fact::ForallFact(f) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    f.typed_parameters.groups.swap(0, 1);
    compiler
        .compile_run(&run, "jacobian_reversed_coordinates")
        .expect_err(
            "the output-row and input-column binders keep their original carriers and order",
        );
}

#[test]
fn coordinate_component_binding_requires_original_substitution_and_strict_equality() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
    for change in ["substitution", "capture", "equality"] {
        let (mut run, compiler) = super::execute(
            r#"# Each Jacobian entry retains its component function and ordered matrix coordinates.
thm checked_jacobian_builtin_to_definition:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), J matrix(R, 3, 2), row closed_range(1, 3), col closed_range(1, 2):
        $has_jacobian_at(f, p, 2, 3, J)
        =>:
            $has_partial_derivative_at(fn(x cart_n(R, 2)) R {f(x)(row)}, p, 2, col, J(row, col))
    release thm jacobian_at_to_definition(f, p, 2, 3, J)
    $has_partial_derivative_at(fn(x cart_n(R, 2)) R {f(x)(row)}, p, 2, col, J(row, col))
"#,
        );
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
            panic!()
        };
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &mut body.proof_steps[1]
        else {
            panic!()
        };
        let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(call) =
            &mut super::atomic_proof_mut(&mut statement.verify_result).searched_proof
        else {
            panic!("original component forall application")
        };
        let detail = call.as_detailed_mut().unwrap();
        if change == "substitution" {
            detail.forall_parameters_match_what_args[0] = super::number_object("1");
        } else {
            let DetailedForallConclusionArgMatchProof::NonParamEqual {
                pattern_after_subst,
                equal,
                ..
            } = detail.arg_match_proofs[0].as_detailed_mut().unwrap()
            else {
                panic!("whole component function binding certificate")
            };
            if change == "capture" {
                *pattern_after_subst = Obj::StandardSet(StandardSet::R);
            } else {
                equal.equal_fact.left = Obj::StandardSet(StandardSet::R);
            }
        }
        compiler.compile_run(&run,change).expect_err("component parameter bindings are owned by the exact captured instantiation and original strict equality");
    }
}

#[test]
fn coordinate_definition_gradient_retains_original_clauses_and_inference_identity() {
    for (source, law) in [
        (
            r#"# A gradient is specified by the original ordered coordinate partial derivatives.
thm checked_gradient_builtin_from_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), g cart_n(R, 2):
        forall k closed_range(1, 2):
            $has_partial_derivative_at(f, p, 2, k, g(k))
        =>:
            $has_gradient_at(f, p, 2, g)
    release thm gradient_at_from_definition(f, p, 2, g)
"#,
            "gradientOfCoordinatePartials",
        ),
        (
            r#"# Each gradient coordinate equals the original partial derivative in that direction.
thm checked_gradient_builtin_to_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), g cart_n(R, 2), k closed_range(1, 2):
        $has_gradient_at(f, p, 2, g)
        =>:
            $has_partial_derivative_at(f, p, 2, k, g(k))
    release thm gradient_at_to_definition(f, p, 2, g)
    $has_partial_derivative_at(f, p, 2, k, g(k))
"#,
            "gradientCoordinatePartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "gradient_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# A gradient is specified by the original ordered coordinate partial derivatives.
thm checked_gradient_builtin_from_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), g cart_n(R, 2):
        forall k closed_range(1, 2):
            $has_partial_derivative_at(f, p, 2, k, g(k))
        =>:
            $has_gradient_at(f, p, 2, g)
    release thm gradient_at_from_definition(f, p, 2, g)
"#,
    );
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "gradient_reordered_definition")
        .expect_err("original coordinate clauses cannot replace an earlier dimension proof");
    let (mut run, compiler) = super::execute(
        r#"# Each gradient coordinate equals the original partial derivative in that direction.
thm checked_gradient_builtin_to_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), g cart_n(R, 2), k closed_range(1, 2):
        $has_gradient_at(f, p, 2, g)
        =>:
            $has_partial_derivative_at(f, p, 2, k, g(k))
    release thm gradient_at_to_definition(f, p, 2, g)
    $has_partial_derivative_at(f, p, 2, k, g(k))
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[5].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.derived.pop();
    compiler
        .compile_run(&run, "gradient_missing_definition_inference")
        .expect_err("unfolding retains the original complete definition inference capture");
}

#[test]
fn coordinate_definition_hessian_retains_original_clauses_and_inference_identity() {
    for (source, law) in [
        (
            r#"# Hessian entries retain the ordered pair of coordinate directions.
thm checked_hessian_builtin_from_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 2, 2):
        forall row, col closed_range(1, 2):
            $has_second_partial_derivative_at(f, p, 2, row, col, A(row, col))
        =>:
            $has_hessian_at(f, p, 2, A)
    release thm hessian_at_from_definition(f, p, 2, A)
"#,
            "hessianOfOrderedPartials",
        ),
        (
            r#"# A Hessian entry is the second partial in its original row-column order.
thm checked_hessian_builtin_to_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 2, 2), row, col closed_range(1, 2):
        $has_hessian_at(f, p, 2, A)
        =>:
            $has_second_partial_derivative_at(f, p, 2, row, col, A(row, col))
    release thm hessian_at_to_definition(f, p, 2, A)
    $has_second_partial_derivative_at(f, p, 2, row, col, A(row, col))
"#,
            "hessianOrderedPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "hessian_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# Hessian entries retain the ordered pair of coordinate directions.
thm checked_hessian_builtin_from_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 2, 2):
        forall row, col closed_range(1, 2):
            $has_second_partial_derivative_at(f, p, 2, row, col, A(row, col))
        =>:
            $has_hessian_at(f, p, 2, A)
    release thm hessian_at_from_definition(f, p, 2, A)
"#,
    );
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "hessian_reordered_definition")
        .expect_err("original coordinate clauses cannot replace an earlier dimension proof");
    let (mut run, compiler) = super::execute(
        r#"# A Hessian entry is the second partial in its original row-column order.
thm checked_hessian_builtin_to_definition:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 2, 2), row, col closed_range(1, 2):
        $has_hessian_at(f, p, 2, A)
        =>:
            $has_second_partial_derivative_at(f, p, 2, row, col, A(row, col))
    release thm hessian_at_to_definition(f, p, 2, A)
    $has_second_partial_derivative_at(f, p, 2, row, col, A(row, col))
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[5].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.derived.pop();
    compiler
        .compile_run(&run, "hessian_missing_definition_inference")
        .expect_err("unfolding retains the original complete definition inference capture");
}

#[test]
fn derivative_schemas_scalar_differential_replays_uniqueness_context_and_matrix_carrier() {
    for (source, law) in [
        (
            r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_scalar_differential_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A, B matrix(R, 1, 2):
        $has_scalar_differential_at(f, p, 2, A)
        $has_scalar_differential_at(f, p, 2, B)
        =>:
            A = B
    release thm scalar_differential_at_unique(f, p, 2, A, B)
"#,
            "scalarDifferentialCandidatesEqual",
        ),
        (
            r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_scalar_differential_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 1, 2):
        $has_scalar_differential_at(f, p, 2, A)
        =>:
            exist value matrix(R, 1, 2) st {$has_scalar_differential_at(f, p, 2, value)}
    release thm scalar_differential_at_exists(f, p, 2, A)
"#,
            "scalarDifferentialExistsOfCandidate",
        ),
        (
            r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_scalar_differential_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):
        exist value matrix(R, 1, 2) st {$has_scalar_differential_at(f, p, 2, value)}
        =>:
            $has_scalar_differential_at(f, p, 2, scalar_differential(f, p, 2))
    release thm scalar_differential_at_selected(f, p, 2)
"#,
            "scalarDifferentialValueSelected",
        ),
        (
            r#"# Scalar differential uniqueness keeps the authored guard and point-in-domain proof.
thm checked_scalar_differential_builtin_guarded_unique:
    ? forall f fn(x cart_n(R, 2): x(1) > 0) R, p cart_n(R, 2), A, B matrix(R, 1, 2):
        p(1) > 0
        $has_scalar_differential_at(f, p, 2, A)
        $has_scalar_differential_at(f, p, 2, B)
        =>:
            A = B
    release thm scalar_differential_at_unique(f, p, 2, A, B)
"#,
            "scalarDifferentialCandidatesEqual",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "scalar_differential_schema")
            .unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_scalar_differential_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A, B matrix(R, 1, 2):
        $has_scalar_differential_at(f, p, 2, A)
        $has_scalar_differential_at(f, p, 2, B)
        =>:
            A = B
    release thm scalar_differential_at_unique(f, p, 2, A, B)
"#,
    );
    invocation(&mut run).dom_proofs.swap(0, 4);
    compiler
        .compile_run(&run, "scalar_differential_swapped_context")
        .expect_err("dimensional and point-in-domain source proofs retain their ordered subjects");
    let (mut run, compiler) = super::execute(
        r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_scalar_differential_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 1, 2):
        $has_scalar_differential_at(f, p, 2, A)
        =>:
            exist value matrix(R, 1, 2) st {$has_scalar_differential_at(f, p, 2, value)}
    release thm scalar_differential_at_exists(f, p, 2, A)
"#,
    );
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "scalar_differential_scalar_witness")
        .expect_err("the original differential witness is a matrix");
}

#[test]
fn derivative_schemas_total_derivative_replays_uniqueness_context_and_matrix_carrier() {
    for (source, law) in [
        (
            r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_total_derivative_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), A, B matrix(R, 3, 2):
        $has_total_derivative_at(f, p, 2, 3, A)
        $has_total_derivative_at(f, p, 2, 3, B)
        =>:
            A = B
    release thm total_derivative_at_unique(f, p, 2, 3, A, B)
"#,
            "totalDifferentialCandidatesEqual",
        ),
        (
            r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_total_derivative_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), A matrix(R, 3, 2):
        $has_total_derivative_at(f, p, 2, 3, A)
        =>:
            exist value matrix(R, 3, 2) st {$has_total_derivative_at(f, p, 2, 3, value)}
    release thm total_derivative_at_exists(f, p, 2, 3, A)
"#,
            "totalDifferentialExistsOfCandidate",
        ),
        (
            r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_total_derivative_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2):
        exist value matrix(R, 3, 2) st {$has_total_derivative_at(f, p, 2, 3, value)}
        =>:
            $has_total_derivative_at(f, p, 2, 3, differential(f, p, 2, 3))
    release thm total_derivative_at_selected(f, p, 2, 3)
"#,
            "totalDifferentialValueSelected",
        ),
        (
            r#"# Total differential uniqueness preserves independent symbolic input and output dimensions.
thm checked_total_derivative_builtin_generic_unique:
    ? forall n, m N+, f fn(x cart_n(R, n)) cart_n(R, m), p cart_n(R, n), A, B matrix(R, m, n):
        $has_total_derivative_at(f, p, n, m, A)
        $has_total_derivative_at(f, p, n, m, B)
        =>:
            A = B
    release thm total_derivative_at_unique(f, p, n, m, A, B)
"#,
            "totalDifferentialCandidatesEqual",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "total_derivative_schema")
            .unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_total_derivative_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), A, B matrix(R, 3, 2):
        $has_total_derivative_at(f, p, 2, 3, A)
        $has_total_derivative_at(f, p, 2, 3, B)
        =>:
            A = B
    release thm total_derivative_at_unique(f, p, 2, 3, A, B)
"#,
    );
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "total_derivative_swapped_context")
        .expect_err("dimensional and point-in-domain source proofs retain their ordered subjects");
    let (mut run, compiler) = super::execute(
        r#"# The differential preserves the original function signature and matrix dimensions.
thm checked_total_derivative_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 3), p cart_n(R, 2), A matrix(R, 3, 2):
        $has_total_derivative_at(f, p, 2, 3, A)
        =>:
            exist value matrix(R, 3, 2) st {$has_total_derivative_at(f, p, 2, 3, value)}
    release thm total_derivative_at_exists(f, p, 2, 3, A)
"#,
    );
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "total_derivative_scalar_witness")
        .expect_err("the original differential witness is a matrix");
}

#[test]
fn derivative_schemas_divergence_preserves_value_carrier_and_original_domain_capture() {
    for (source, law) in [
        (
            r#"# Divergence retains the original square vector field and scalar value contract.
thm checked_divergence_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 2), p cart_n(R, 2), a, b R:
        $has_divergence_at(f, p, 2, a)
        $has_divergence_at(f, p, 2, b)
        =>:
            a = b
    release thm divergence_at_unique(f, p, 2, a, b)
"#,
            "divergenceCandidatesEqual",
        ),
        (
            r#"# Divergence retains the original square vector field and scalar value contract.
thm checked_divergence_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 2), p cart_n(R, 2), a R:
        $has_divergence_at(f, p, 2, a)
        =>:
            exist value R st {$has_divergence_at(f, p, 2, value)}
    release thm divergence_at_exists(f, p, 2, a)
"#,
            "divergenceExistsOfCandidate",
        ),
        (
            r#"# Divergence retains the original square vector field and scalar value contract.
thm checked_divergence_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 2), p cart_n(R, 2):
        exist value R st {$has_divergence_at(f, p, 2, value)}
        =>:
            $has_divergence_at(f, p, 2, divergence(f, p, 2))
    release thm divergence_at_selected(f, p, 2)
"#,
            "divergenceValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "divergence_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# Divergence retains the original square vector field and scalar value contract.
thm checked_divergence_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) cart_n(R, 2), p cart_n(R, 2), a, b R:
        $has_divergence_at(f, p, 2, a)
        $has_divergence_at(f, p, 2, b)
        =>:
            a = b
    release thm divergence_at_unique(f, p, 2, a, b)
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[6].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.function_domain = None;
    compiler
        .compile_run(&run, "divergence_missing_domain")
        .expect_err("the original complete function-domain evidence is required");
}

#[test]
fn derivative_schemas_curl_preserves_value_carrier_and_original_domain_capture() {
    for (source, law) in [
        (
            r#"# Curl retains its fixed three-dimensional vector field and orientation.
thm checked_curl_builtin_unique:
    ? forall f fn(x cart_n(R, 3)) cart_n(R, 3), p cart_n(R, 3), a, b cart_n(R, 3):
        $has_curl_at(f, p, a)
        $has_curl_at(f, p, b)
        =>:
            a = b
    release thm curl_at_unique(f, p, a, b)
"#,
            "curlCandidatesEqual",
        ),
        (
            r#"# Curl retains its fixed three-dimensional vector field and orientation.
thm checked_curl_builtin_exists:
    ? forall f fn(x cart_n(R, 3)) cart_n(R, 3), p cart_n(R, 3), a cart_n(R, 3):
        $has_curl_at(f, p, a)
        =>:
            exist value cart_n(R, 3) st {$has_curl_at(f, p, value)}
    release thm curl_at_exists(f, p, a)
"#,
            "curlExistsOfCandidate",
        ),
        (
            r#"# Curl retains its fixed three-dimensional vector field and orientation.
thm checked_curl_builtin_selected:
    ? forall f fn(x cart_n(R, 3)) cart_n(R, 3), p cart_n(R, 3):
        exist value cart_n(R, 3) st {$has_curl_at(f, p, value)}
        =>:
            $has_curl_at(f, p, curl(f, p))
    release thm curl_at_selected(f, p)
"#,
            "curlValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "curl_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# Curl retains its fixed three-dimensional vector field and orientation.
thm checked_curl_builtin_unique:
    ? forall f fn(x cart_n(R, 3)) cart_n(R, 3), p cart_n(R, 3), a, b cart_n(R, 3):
        $has_curl_at(f, p, a)
        $has_curl_at(f, p, b)
        =>:
            a = b
    release thm curl_at_unique(f, p, a, b)
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[6].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.function_domain = None;
    compiler
        .compile_run(&run, "curl_missing_domain")
        .expect_err("the original complete function-domain evidence is required");
}

#[test]
fn derivative_schemas_laplacian_preserves_value_carrier_and_original_domain_capture() {
    for (source, law) in [
        (
            r#"# The Laplacian retains the scalar field and the sum of its pure second partials.
thm checked_laplacian_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), a, b R:
        $has_laplacian_at(f, p, 2, a)
        $has_laplacian_at(f, p, 2, b)
        =>:
            a = b
    release thm laplacian_at_unique(f, p, 2, a, b)
"#,
            "laplacianCandidatesEqual",
        ),
        (
            r#"# The Laplacian retains the scalar field and the sum of its pure second partials.
thm checked_laplacian_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), a R:
        $has_laplacian_at(f, p, 2, a)
        =>:
            exist value R st {$has_laplacian_at(f, p, 2, value)}
    release thm laplacian_at_exists(f, p, 2, a)
"#,
            "laplacianExistsOfCandidate",
        ),
        (
            r#"# The Laplacian retains the scalar field and the sum of its pure second partials.
thm checked_laplacian_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):
        exist value R st {$has_laplacian_at(f, p, 2, value)}
        =>:
            $has_laplacian_at(f, p, 2, laplacian(f, p, 2))
    release thm laplacian_at_selected(f, p, 2)
"#,
            "laplacianValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "laplacian_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# The Laplacian retains the scalar field and the sum of its pure second partials.
thm checked_laplacian_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), a, b R:
        $has_laplacian_at(f, p, 2, a)
        $has_laplacian_at(f, p, 2, b)
        =>:
            a = b
    release thm laplacian_at_unique(f, p, 2, a, b)
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[5].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.function_domain = None;
    compiler
        .compile_run(&run, "laplacian_missing_domain")
        .expect_err("the original complete function-domain evidence is required");
}

#[test]
fn derivative_schemas_hessian_actions_preserve_square_matrix_and_definition_capture() {
    for (source, law) in [
        (
            r#"# A Hessian is unique componentwise in its fixed square matrix carrier.
thm checked_hessian_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A, B matrix(R, 2, 2):
        $has_hessian_at(f, p, 2, A)
        $has_hessian_at(f, p, 2, B)
        =>:
            A = B
    release thm hessian_at_unique(f, p, 2, A, B)
"#,
            "hessianCandidatesEqual",
        ),
        (
            r#"# A Hessian candidate provides a square-matrix witness for the same scalar field.
thm checked_hessian_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 2, 2):
        $has_hessian_at(f, p, 2, A)
        =>:
            exist value matrix(R, 2, 2) st {$has_hessian_at(f, p, 2, value)}
    release thm hessian_at_exists(f, p, 2, A)
"#,
            "hessianExistsOfCandidate",
        ),
        (
            r#"# The Hessian selector preserves the scalar field, point and square matrix dimension.
thm checked_hessian_builtin_selected:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):
        exist value matrix(R, 2, 2) st {$has_hessian_at(f, p, 2, value)}
        =>:
            $has_hessian_at(f, p, 2, hessian(f, p, 2))
    release thm hessian_at_selected(f, p, 2)
"#,
            "hessianValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "hessian_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(
        r#"# A Hessian candidate provides a square-matrix witness for the same scalar field.
thm checked_hessian_builtin_exists:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A matrix(R, 2, 2):
        $has_hessian_at(f, p, 2, A)
        =>:
            exist value matrix(R, 2, 2) st {$has_hessian_at(f, p, 2, value)}
    release thm hessian_at_exists(f, p, 2, A)
"#,
    );
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "hessian_scalar_witness")
        .expect_err("Hessian witnesses retain the original square matrix carrier");
    let (mut run, compiler) = super::execute(
        r#"# A Hessian is unique componentwise in its fixed square matrix carrier.
thm checked_hessian_builtin_unique:
    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2), A, B matrix(R, 2, 2):
        $has_hessian_at(f, p, 2, A)
        $has_hessian_at(f, p, 2, B)
        =>:
            A = B
    release thm hessian_at_unique(f, p, 2, A, B)
"#,
    );
    let p = invocation(&mut run);
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[5].infer
    else {
        panic!()
    };
    let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0] else {
        panic!()
    };
    capture.derived.pop();
    compiler
        .compile_run(&run, "hessian_missing_entries")
        .expect_err("the original ordered-entry definition inference remains required");
}

#[test]
fn derivative_schemas_jacobian_actions_retain_distinct_matrix_rows_and_columns() {
    for (source, law) in [
        (JACOBIAN_UNIQUE, "jacobianCandidatesEqual"),
        (JACOBIAN_EXISTS, "jacobianExistsOfCandidate"),
        (JACOBIAN_SELECTED, "jacobianValueSelected"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "jacobian_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(JACOBIAN_UNIQUE);
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
        &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[7]
    else {
        panic!()
    };
    let MultivariableAnalysisRelation::JacobianAt(r) = &mut f.relation else {
        panic!()
    };
    std::mem::swap(&mut r.input_dimension, &mut r.output_dimension);
    compiler
        .compile_run(&run, "jacobian_swapped_dimensions")
        .expect_err("Jacobian input columns and output rows cannot be interchanged");
    let (mut run, compiler) = super::execute(JACOBIAN_EXISTS);
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "jacobian_scalar_witness")
        .expect_err("a Jacobian witness has its original matrix carrier");
}

#[test]
fn derivative_schemas_gradient_actions_preserve_vector_carriers_and_selected_dimension() {
    for (source, law) in [
        (GRADIENT_UNIQUE, "gradientCandidatesEqual"),
        (GRADIENT_EXISTS, "gradientExistsOfCandidate"),
        (GRADIENT_SELECTED, "gradientValueSelected"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "gradient_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(GRADIENT_EXISTS);
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "gradient_scalar_witness")
        .expect_err("a gradient is a vector in the input dimension");
    let (mut run, compiler) = super::execute(GRADIENT_SELECTED);
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
        &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    let MultivariableAnalysisRelation::GradientAt(r) = &mut f.relation else {
        panic!()
    };
    r.dimension = super::number_object("3");
    compiler
        .compile_run(&run, "gradient_changed_dimension")
        .expect_err("the selected gradient retains the original input dimension");
}

#[test]
fn derivative_schemas_second_partials_preserve_ordered_axes_and_original_definition_capture() {
    for (source, law) in [
        (SECOND_UNIQUE, "secondPartialCandidatesEqual"),
        (SECOND_EXISTS, "secondPartialExistsOfCandidate"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "second_partial")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    for change in ["axes", "coordinate_proofs", "capture", "identity"] {
        let (mut run, compiler) = super::execute(SECOND_UNIQUE);
        let p = invocation(&mut run);
        if change == "axes" {
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[8]
            else {
                panic!()
            };
            let MultivariableAnalysisRelation::SecondPartialDerivativeAt(r) = &mut f.relation
            else {
                panic!()
            };
            std::mem::swap(&mut r.first_coordinate, &mut r.second_coordinate);
        } else if change == "coordinate_proofs" {
            p.dom_proofs.swap(5, 6);
        } else {
            let other = p.builtin.as_ref().unwrap().requirements[8].fact_id();
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &mut p.dom_stores[7].infer
            else {
                panic!()
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_mut_slice()
            else {
                panic!()
            };
            if change == "identity" {
                capture.source_fact_id = other;
            } else {
                capture.derived.pop();
            }
        }
        compiler.compile_run(&run,change).expect_err("second partials retain ordered axes, both original coordinate proofs and the exact two-fact inference capture");
    }
}
#[test]
fn derivative_schema_preserves_all_original_prerequisite_store_and_wd_stages() {
    for change in [
        "proof",
        "proof_order",
        "store",
        "store_order",
        "wd",
        "types",
    ] {
        let (mut run, compiler) = super::execute(UNIQUE);
        let p = invocation(&mut run);
        match change {
            "proof" => p.dom_proofs.clear(),
            "proof_order" => p.dom_proofs.swap(0, 6),
            "store" => p.dom_stores.clear(),
            "store_order" => p.dom_stores.swap(0, 6),
            "wd" => p.conclusions_wd.clear(),
            _ => std::mem::swap(&mut p.dom_proofs, &mut p.type_proofs),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("derivative actions retain every original stage and prefix");
    }
}
#[test]
fn derivative_schema_requires_original_inference_identity_and_complete_domain() {
    for change in ["missing", "identity", "derived", "domain", "return"] {
        let (mut run, compiler) = super::execute(UNIQUE);
        let p = invocation(&mut run);
        if change == "missing" {
            p.dom_stores[6].infer = None;
        } else {
            let other = p.builtin.as_ref().unwrap().requirements[7].fact_id();
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &mut p.dom_stores[6].infer
            else {
                panic!()
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_mut_slice()
            else {
                panic!()
            };
            match change {
                "identity" => capture.source_fact_id = other,
                "derived" => capture.derived.clear(),
                "domain" => capture.function_domain = None,
                _ => {
                    capture.function_domain.as_mut().unwrap().signature.ret_set =
                        Box::new(Obj::StandardSet(StandardSet::C))
                }
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "only the original candidate's exact complete-domain inference is authoritative",
        );
    }
}
#[test]
fn derivative_schema_retains_actual_guarded_point_domain_and_coordinate() {
    for change in ["domain", "axis", "point"] {
        let (mut run, compiler) = super::execute(GUARDED);
        let p = invocation(&mut run);
        if change == "domain" {
            let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(
                rules,
            ))) = &mut p.dom_stores[6].infer
            else {
                panic!()
            };
            let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_mut_slice()
            else {
                panic!()
            };
            capture
                .function_domain
                .as_mut()
                .unwrap()
                .signature
                .dom_facts
                .clear();
        } else {
            let index = if change == "axis" { 5 } else { 4 };
            let Fact::AtomicFact(AtomicFact::InFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[index]
            else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::R);
        }
        compiler.compile_run(&run,change).expect_err("point membership in actual D and the original coordinate interval are independent prerequisites");
    }
}
#[test]
fn derivative_schema_retains_real_witness_and_exact_selected_coordinate_formation() {
    let (mut run, compiler) = super::execute(EXISTS);
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::C));
    compiler
        .compile_run(&run, "complex_witness")
        .expect_err("the original real witness carrier is fixed");
    for change in ["selector", "capture"] {
        let (mut run, compiler) = super::execute(SELECTED);
        let p = invocation(&mut run);
        if change == "selector" {
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                &mut p.builtin.as_mut().unwrap().conclusions[0]
            else {
                panic!()
            };
            let MultivariableAnalysisRelation::PartialDerivativeAt(r) = &mut f.relation else {
                panic!()
            };
            r.coordinate = super::number_object("2");
        } else {
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
                panic!()
            };
            let PredicateDomainProof::MultivariableAnalysis(capture) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!()
            };
            capture.requirements.pop();
        }
        compiler.compile_run(&run, change).expect_err(
            "selection keeps the original coordinate, domain and value formation capture",
        );
    }
}
#[test]
fn derivative_schema_rejects_future_conclusion_as_an_original_dimension_premise() {
    let (mut run, compiler) = super::execute(UNIQUE);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[0]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler.compile_run(&run, "future").expect_err(
        "the output equality is invisible at each earlier derivative prerequisite stage",
    );
}
