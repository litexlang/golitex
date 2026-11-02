use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

const UNIQUE: &str = include_str!("../../../lean/examples/partial_builtin_unique/statement.lit");
const EXISTS: &str = include_str!("../../../lean/examples/partial_builtin_exists/statement.lit");
const SELECTED: &str =
    include_str!("../../../lean/examples/partial_builtin_selected/statement.lit");
const GUARDED: &str =
    include_str!("../../../lean/examples/partial_builtin_guarded_unique/statement.lit");
const GENERIC: &str =
    include_str!("../../../lean/examples/partial_builtin_generic_unique/statement.lit");
const SECOND_UNIQUE: &str =
    include_str!("../../../lean/examples/second_partial_builtin_unique/statement.lit");
const SECOND_EXISTS: &str =
    include_str!("../../../lean/examples/second_partial_builtin_exists/statement.lit");
const GRADIENT_UNIQUE: &str =
    include_str!("../../../lean/examples/gradient_builtin_unique/statement.lit");
const GRADIENT_EXISTS: &str =
    include_str!("../../../lean/examples/gradient_builtin_exists/statement.lit");
const GRADIENT_SELECTED: &str =
    include_str!("../../../lean/examples/gradient_builtin_selected/statement.lit");
const JACOBIAN_UNIQUE: &str =
    include_str!("../../../lean/examples/jacobian_builtin_unique/statement.lit");
const JACOBIAN_EXISTS: &str =
    include_str!("../../../lean/examples/jacobian_builtin_exists/statement.lit");
const JACOBIAN_SELECTED: &str =
    include_str!("../../../lean/examples/jacobian_builtin_selected/statement.lit");

#[test]
fn derivative_schemas_replay_original_partial_actions_guarded_domain_and_generic_axis() {
    for (source, law) in [
        (UNIQUE, "partialDerivativeCandidatesEqual"),
        (EXISTS, "partialDerivativeExistsOfCandidate"),
        (SELECTED, "partialDerivativeValueSelected"),
        (GUARDED, "partialDerivativeCandidatesEqual"),
        (GENERIC, "partialDerivativeCandidatesEqual"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "partial_schema").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(
            output,
            compiler.compile_run(&run, "partial_schema").unwrap()
        );
    }
}

#[test]
fn unary_derivative_elementary_builtins_replay_original_formula_and_positive_point() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_exp/statement.lit"),
            "semanticDerivativeExp",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_sin/statement.lit"),
            "semanticDerivativeSin",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_cos/statement.lit"),
            "semanticDerivativeCos",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_ln/statement.lit"),
            "semanticDerivativeLn",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_sqrt/statement.lit"),
            "semanticDerivativeSqrt",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let out = compiler.compile_run(&run, "elementary_derivative").unwrap();
        assert!(out.contains(law));
        assert_eq!(
            out,
            compiler.compile_run(&run, "elementary_derivative").unwrap()
        );
    }
}

#[test]
fn unary_derivative_elementary_builtins_reject_erased_positivity_and_wrong_factor() {
    for change in ["positive", "factor", "body", "future"] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/unary_derivative_builtin_sqrt/statement.lit"
        ));
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
fn unary_derivative_constant_and_identity_replay_interior_and_formula() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_constant/statement.lit"),
            "semanticDerivativeConstant",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_identity/statement.lit"),
            "semanticDerivativeVariable",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let out = compiler.compile_run(&run, "derivative_formula").unwrap();
        assert!(out.contains(law));
        assert!(out.contains("Litex.derivativeOfSemanticFormula"));
        assert_eq!(
            out,
            compiler.compile_run(&run, "derivative_formula").unwrap()
        );
    }
}

#[test]
fn unary_derivative_formulas_reject_wrong_body_interior_and_coefficient() {
    for change in ["formula", "interior", "coefficient", "formation"] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/unary_derivative_builtin_constant/statement.lit"
        ));
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
fn unary_derivative_differentiability_and_continuity_replay_original_candidates() {
    for (source, law) in [
        (
            include_str!(
                "../../../lean/examples/unary_derivative_builtin_differentiable/statement.lit"
            ),
            "derivativeExistsValueOfCandidate",
        ),
        (
            include_str!(
                "../../../lean/examples/unary_derivative_builtin_continuous/statement.lit"
            ),
            "functionContinuousAtOfDerivative",
        ),
        (
            include_str!(
                "../../../lean/examples/unary_differentiable_builtin_continuous/statement.lit"
            ),
            "functionContinuousAtOfDifferentiable",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "continuity_from_derivative")
            .unwrap();
        assert!(output.contains(law));
        assert_eq!(
            output,
            compiler
                .compile_run(&run, "continuity_from_derivative")
                .unwrap()
        );
    }
}

#[test]
fn unary_derivative_continuity_rejects_changed_side_point_and_source_context() {
    for change in ["side", "point", "context"] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/unary_derivative_builtin_continuous/statement.lit"
        ));
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
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/unary_differentiable_builtin_continuous/statement.lit"
    ));
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
fn unary_derivative_standard_interiors_replay_the_original_open_carrier() {
    for source in [
        include_str!("../../../lean/examples/unary_derivative_real_interior/statement.lit"),
        include_str!("../../../lean/examples/unary_derivative_nonzero_interior/statement.lit"),
        include_str!("../../../lean/examples/unary_derivative_positive_interior/statement.lit"),
        include_str!("../../../lean/examples/unary_derivative_negative_interior/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "standard_interior").unwrap();
        assert!(output.contains("Litex.realInteriorOfOpenDomain"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "standard_interior").unwrap()
        );
    }
}

#[test]
fn unary_derivative_standard_interiors_reject_changed_carrier_ball_and_output_wd() {
    let source =
        include_str!("../../../lean/examples/unary_derivative_positive_interior/statement.lit");
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
fn unary_derivative_builtins_replay_real_observations_and_original_selector_wd() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_unique/statement.lit"),
            "derivativeCandidatesUnique",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_exists/statement.lit"),
            "derivativeExistsValueOfCandidate",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_builtin_selected/statement.lit"),
            "derivativeSelectedCandidate",
        ),
        (
            include_str!(
                "../../../lean/examples/unary_derivative_builtin_guarded_unique/statement.lit"
            ),
            "derivativeCandidatesUnique",
        ),
        (
            include_str!(
                "../../../lean/examples/unary_derivative_builtin_literal_selected/statement.lit"
            ),
            "derivativeSelectedCandidate",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let out = compiler.compile_run(&run, "unary_derivative").unwrap();
        assert!(out.contains(&format!("Litex.{law}")));
        assert_eq!(out, compiler.compile_run(&run, "unary_derivative").unwrap());
    }
}
#[test]
fn unary_derivative_builtins_reject_reordered_context_and_value_candidates() {
    for change in ["context", "candidate", "output_wd"] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/unary_derivative_builtin_unique/statement.lit"
        ));
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
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/unary_derivative_builtin_exists/statement.lit"
    ));
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::C));
    compiler
        .compile_run(&run, "complex_witness")
        .expect_err("derivative existence retains its original real witness carrier");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/unary_derivative_builtin_selected/statement.lit"
    ));
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
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/unary_derivative_builtin_unique/statement.lit"
    ));
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
            include_str!("../../../lean/examples/partial_builtin_from_definition/statement.lit"),
            "partialDerivativeOfClauses",
        ),
        (
            include_str!("../../../lean/examples/partial_builtin_to_definition/statement.lit"),
            "partialDerivativeClauses",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "partial_remainder")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/partial_builtin_from_definition/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(6, 7);
    compiler
        .compile_run(&run, "partial_reordered_clauses")
        .expect_err(
            "the original interior and limit/remainder proofs keep their exact subjects and order",
        );
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/partial_builtin_to_definition/statement.lit"
    ));
    invocation(&mut run)
        .builtin
        .as_mut()
        .unwrap()
        .conclusions
        .swap(0, 1);
    compiler
        .compile_run(&run, "partial_reordered_outputs")
        .expect_err("both defining outputs retain their original ordered formation");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/partial_builtin_to_definition/statement.lit"
    ));
    invocation(&mut run).conclusions_wd.pop();
    compiler
        .compile_run(&run, "partial_missing_output_wd")
        .expect_err("neither defining output can lose its original WD");
}

#[test]
fn remainder_definition_scalar_differential_retains_both_ordered_clauses_and_wd() {
    for (source, law) in [
        (
            include_str!(
                "../../../lean/examples/scalar_differential_builtin_from_definition/statement.lit"
            ),
            "scalarDifferentialOfClauses",
        ),
        (
            include_str!(
                "../../../lean/examples/scalar_differential_builtin_to_definition/statement.lit"
            ),
            "scalarDifferentialClauses",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "scalar_differential_remainder")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/scalar_differential_builtin_from_definition/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(5, 6);
    compiler
        .compile_run(&run, "scalar_differential_reordered_clauses")
        .expect_err(
            "the original interior and limit/remainder proofs keep their exact subjects and order",
        );
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/scalar_differential_builtin_to_definition/statement.lit"
    ));
    invocation(&mut run)
        .builtin
        .as_mut()
        .unwrap()
        .conclusions
        .swap(0, 1);
    compiler
        .compile_run(&run, "scalar_differential_reordered_outputs")
        .expect_err("both defining outputs retain their original ordered formation");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/scalar_differential_builtin_to_definition/statement.lit"
    ));
    invocation(&mut run).conclusions_wd.pop();
    compiler
        .compile_run(&run, "scalar_differential_missing_output_wd")
        .expect_err("neither defining output can lose its original WD");
}

#[test]
fn remainder_definition_total_derivative_retains_both_ordered_clauses_and_wd() {
    for (source, law) in [
        (
            include_str!(
                "../../../lean/examples/total_derivative_builtin_from_definition/statement.lit"
            ),
            "totalDifferentialOfClauses",
        ),
        (
            include_str!(
                "../../../lean/examples/total_derivative_builtin_to_definition/statement.lit"
            ),
            "totalDifferentialClauses",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "total_derivative_remainder")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/total_derivative_builtin_from_definition/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(6, 7);
    compiler
        .compile_run(&run, "total_derivative_reordered_clauses")
        .expect_err(
            "the original interior and limit/remainder proofs keep their exact subjects and order",
        );
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/total_derivative_builtin_to_definition/statement.lit"
    ));
    invocation(&mut run)
        .builtin
        .as_mut()
        .unwrap()
        .conclusions
        .swap(0, 1);
    compiler
        .compile_run(&run, "total_derivative_reordered_outputs")
        .expect_err("both defining outputs retain their original ordered formation");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/total_derivative_builtin_to_definition/statement.lit"
    ));
    invocation(&mut run).conclusions_wd.pop();
    compiler
        .compile_run(&run, "total_derivative_missing_output_wd")
        .expect_err("neither defining output can lose its original WD");
}

#[test]
fn coordinate_definition_divergence_retains_defining_witness_and_inference() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/divergence_builtin_from_definition/statement.lit"),
            "divergenceOfDiagonalPartials",
        ),
        (
            include_str!("../../../lean/examples/divergence_builtin_to_definition/statement.lit"),
            "divergenceDiagonalPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "divergence_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/divergence_builtin_from_definition/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(0, 6);
    compiler
        .compile_run(&run, "divergence_reordered_witness")
        .expect_err("the defining witness remains after the original context proofs");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/divergence_builtin_to_definition/statement.lit"
    ));
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
            include_str!("../../../lean/examples/laplacian_builtin_from_definition/statement.lit"),
            "laplacianOfDiagonalPartials",
        ),
        (
            include_str!("../../../lean/examples/laplacian_builtin_to_definition/statement.lit"),
            "laplacianDiagonalPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "laplacian_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/laplacian_builtin_from_definition/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "laplacian_reordered_witness")
        .expect_err("the defining witness remains after the original context proofs");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/laplacian_builtin_to_definition/statement.lit"
    ));
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
    for (source,law) in [
        ("# Curl's defining witness keeps all six partial derivatives and their orientation.\nthm checked_curl_builtin_from_definition:\n    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):\n        exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}\n        =>:\n            $has_curl_at(f,p,c)\n    release thm curl_at_from_definition(f,p,c)\n","curlOfCoordinatePartials"),
        ("# Expanding curl recovers the same ordered six partials and three signed coordinate differences.\nthm checked_curl_builtin_to_definition:\n    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):\n        $has_curl_at(f,p,c)\n        =>:\n            exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}\n    release thm curl_at_to_definition(f,p,c)\n","curlCoordinatePartials"),
    ] {
        let (run,compiler) = super::execute(source);
        assert!(compiler.compile_run(&run,"curl_definition").unwrap().contains(&format!("Litex.{law}")));
    }
    let (mut run,compiler) = super::execute("# Curl's defining witness keeps all six partial derivatives and their orientation.\nthm checked_curl_builtin_from_definition:\n    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):\n        exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}\n        =>:\n            $has_curl_at(f,p,c)\n    release thm curl_at_from_definition(f,p,c)\n");
    invocation(&mut run).dom_proofs.swap(0, 6);
    compiler
        .compile_run(&run, "curl_reordered_witness")
        .expect_err("the defining witness remains after the original context proofs");
    let (mut run,compiler) = super::execute("# Expanding curl recovers the same ordered six partials and three signed coordinate differences.\nthm checked_curl_builtin_to_definition:\n    ? forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):\n        $has_curl_at(f,p,c)\n        =>:\n            exist v cart_n(R,6) st {$has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,2,v(1)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,3,v(2)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,3,v(3)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(3)},p,3,1,v(4)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(2)},p,3,1,v(5)), $has_partial_derivative_at(fn(x cart_n(R,3)) R {f(x)(1)},p,3,2,v(6)), c(1)=v(1)-v(2), c(2)=v(3)-v(4), c(3)=v(5)-v(6)}\n    release thm curl_at_to_definition(f,p,c)\n");
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
            include_str!("../../../lean/examples/jacobian_builtin_from_definition/statement.lit"),
            "jacobianOfComponentPartials",
        ),
        (
            include_str!("../../../lean/examples/jacobian_builtin_to_definition/statement.lit"),
            "jacobianComponentPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "jacobian_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/jacobian_builtin_to_definition/statement.lit"
    ));
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
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/jacobian_builtin_to_definition/statement.lit"
        ));
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
fn multivariable_negative_coordinate_forall_replays_original_typed_instantiation() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/multivariable_negative_forall_instantiation/statement.lit"
    ));
    compiler.compile_run(&run, "negative_coordinate").unwrap();
}

#[test]
fn coordinate_definition_gradient_retains_original_clauses_and_inference_identity() {
    for (source, law) in [
        (
            include_str!("../../../lean/examples/gradient_builtin_from_definition/statement.lit"),
            "gradientOfCoordinatePartials",
        ),
        (
            include_str!("../../../lean/examples/gradient_builtin_to_definition/statement.lit"),
            "gradientCoordinatePartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "gradient_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/gradient_builtin_from_definition/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "gradient_reordered_definition")
        .expect_err("original coordinate clauses cannot replace an earlier dimension proof");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/gradient_builtin_to_definition/statement.lit"
    ));
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
            include_str!("../../../lean/examples/hessian_builtin_from_definition/statement.lit"),
            "hessianOfOrderedPartials",
        ),
        (
            include_str!("../../../lean/examples/hessian_builtin_to_definition/statement.lit"),
            "hessianOrderedPartials",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "hessian_definition")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/hessian_builtin_from_definition/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "hessian_reordered_definition")
        .expect_err("original coordinate clauses cannot replace an earlier dimension proof");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/hessian_builtin_to_definition/statement.lit"
    ));
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
            include_str!("../../../lean/examples/scalar_differential_builtin_unique/statement.lit"),
            "scalarDifferentialCandidatesEqual",
        ),
        (
            include_str!("../../../lean/examples/scalar_differential_builtin_exists/statement.lit"),
            "scalarDifferentialExistsOfCandidate",
        ),
        (
            include_str!(
                "../../../lean/examples/scalar_differential_builtin_selected/statement.lit"
            ),
            "scalarDifferentialValueSelected",
        ),
        (
            include_str!(
                "../../../lean/examples/scalar_differential_builtin_guarded_unique/statement.lit"
            ),
            "scalarDifferentialCandidatesEqual",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "scalar_differential_schema")
            .unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/scalar_differential_builtin_unique/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(0, 4);
    compiler
        .compile_run(&run, "scalar_differential_swapped_context")
        .expect_err("dimensional and point-in-domain source proofs retain their ordered subjects");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/scalar_differential_builtin_exists/statement.lit"
    ));
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
            include_str!("../../../lean/examples/total_derivative_builtin_unique/statement.lit"),
            "totalDifferentialCandidatesEqual",
        ),
        (
            include_str!("../../../lean/examples/total_derivative_builtin_exists/statement.lit"),
            "totalDifferentialExistsOfCandidate",
        ),
        (
            include_str!("../../../lean/examples/total_derivative_builtin_selected/statement.lit"),
            "totalDifferentialValueSelected",
        ),
        (
            include_str!(
                "../../../lean/examples/total_derivative_builtin_generic_unique/statement.lit"
            ),
            "totalDifferentialCandidatesEqual",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "total_derivative_schema")
            .unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/total_derivative_builtin_unique/statement.lit"
    ));
    invocation(&mut run).dom_proofs.swap(0, 5);
    compiler
        .compile_run(&run, "total_derivative_swapped_context")
        .expect_err("dimensional and point-in-domain source proofs retain their ordered subjects");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/total_derivative_builtin_exists/statement.lit"
    ));
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
            include_str!("../../../lean/examples/divergence_builtin_unique/statement.lit"),
            "divergenceCandidatesEqual",
        ),
        (
            include_str!("../../../lean/examples/divergence_builtin_exists/statement.lit"),
            "divergenceExistsOfCandidate",
        ),
        (
            include_str!("../../../lean/examples/divergence_builtin_selected/statement.lit"),
            "divergenceValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "divergence_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/divergence_builtin_unique/statement.lit"
    ));
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
            include_str!("../../../lean/examples/curl_builtin_unique/statement.lit"),
            "curlCandidatesEqual",
        ),
        (
            include_str!("../../../lean/examples/curl_builtin_exists/statement.lit"),
            "curlExistsOfCandidate",
        ),
        (
            include_str!("../../../lean/examples/curl_builtin_selected/statement.lit"),
            "curlValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "curl_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/curl_builtin_unique/statement.lit"
    ));
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
            include_str!("../../../lean/examples/laplacian_builtin_unique/statement.lit"),
            "laplacianCandidatesEqual",
        ),
        (
            include_str!("../../../lean/examples/laplacian_builtin_exists/statement.lit"),
            "laplacianExistsOfCandidate",
        ),
        (
            include_str!("../../../lean/examples/laplacian_builtin_selected/statement.lit"),
            "laplacianValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "laplacian_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/laplacian_builtin_unique/statement.lit"
    ));
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
            include_str!("../../../lean/examples/hessian_builtin_unique/statement.lit"),
            "hessianCandidatesEqual",
        ),
        (
            include_str!("../../../lean/examples/hessian_builtin_exists/statement.lit"),
            "hessianExistsOfCandidate",
        ),
        (
            include_str!("../../../lean/examples/hessian_builtin_selected/statement.lit"),
            "hessianValueSelected",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&run, "hessian_schema")
            .unwrap()
            .contains(&format!("Litex.{law}")));
    }
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/hessian_builtin_exists/statement.lit"
    ));
    let Fact::ExistFact(e) = &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
    else {
        panic!()
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::R));
    compiler
        .compile_run(&run, "hessian_scalar_witness")
        .expect_err("Hessian witnesses retain the original square matrix carrier");
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/hessian_builtin_unique/statement.lit"
    ));
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
