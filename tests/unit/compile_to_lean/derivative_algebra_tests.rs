use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const NEG: &str = include_str!("../../../lean/examples/unary_derivative_algebra_neg/statement.lit");
const SCALE: &str =
    include_str!("../../../lean/examples/unary_derivative_algebra_scale/statement.lit");
const POWER: &str =
    include_str!("../../../lean/examples/unary_derivative_algebra_power/statement.lit");
const DIVIDE: &str =
    include_str!("../../../lean/examples/unary_derivative_algebra_divide/statement.lit");
const COMPOSE: &str =
    include_str!("../../../lean/examples/unary_derivative_algebra_compose/statement.lit");

#[test]
fn derivative_algebra_replays_all_original_unary_and_binary_schemas() {
    for (source, law) in [
        (NEG, "semanticDerivativeNeg"),
        (SCALE, "semanticDerivativeScale"),
        (POWER, "semanticDerivativePower"),
        (
            include_str!("../../../lean/examples/unary_derivative_algebra_add/statement.lit"),
            "semanticDerivativeAdd",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_algebra_subtract/statement.lit"),
            "semanticDerivativeSub",
        ),
        (
            include_str!("../../../lean/examples/unary_derivative_algebra_multiply/statement.lit"),
            "semanticDerivativeMul",
        ),
        (DIVIDE, "semanticDerivativeDiv"),
        (COMPOSE, "semanticDerivativeComposeCandidates"),
    ] {
        let (run, compiler) = super::execute(source);
        let out = compiler.compile_run(&run, "derivative_algebra").unwrap();
        assert!(out.contains(&format!("Litex.{law}")));
        assert_eq!(
            out,
            compiler.compile_run(&run, "derivative_algebra").unwrap()
        );
    }
}

#[test]
fn derivative_algebra_rejects_changed_stages_actual_domains_and_output_formation() {
    for change in [
        "proof_order",
        "store_order",
        "point_domain",
        "output_wd",
        "candidate",
        "formula",
        "conclusion",
    ] {
        let (mut run, compiler) = super::execute(NEG);
        let p = invocation(&mut run);
        match change {
            "proof_order" => p.dom_proofs.swap(0, 4),
            "store_order" => p.dom_stores.swap(0, 4),
            "point_domain" => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[7]
                else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::RPos);
            }
            "output_wd" => p.conclusions_wd.clear(),
            "candidate" => {
                let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[10]
                else {
                    panic!()
                };
                f.value = super::number_object("0");
            }
            "formula" => {
                let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[11] else {
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
                let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!()
                };
                f.value = super::number_object("0");
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "original stages, domains, formula, candidate and conclusion WD are required",
        );
    }
}

#[test]
fn derivative_algebra_scalar_and_power_retain_the_original_carriers() {
    for source in [SCALE, POWER] {
        let (mut run, compiler) = super::execute(source);
        let Fact::AtomicFact(AtomicFact::InFact(f)) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[11]
        else {
            panic!()
        };
        f.set = Obj::StandardSet(StandardSet::C);
        compiler
            .compile_run(&run, "wrong_coefficient_carrier")
            .expect_err("real scalar and natural exponent remain distinct original requirements");
    }
}

#[test]
fn derivative_algebra_quotient_requires_its_original_nonzero_value() {
    let (mut run, compiler) = super::execute(DIVIDE);
    let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) =
        &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[16]
    else {
        panic!()
    };
    f.right = super::number_object("1");
    compiler
        .compile_run(&run, "nonzero_other_value")
        .expect_err("the original denominator at the original point must be nonzero");
}

#[test]
fn derivative_algebra_chain_rule_requires_the_original_outer_point_and_image() {
    for change in ["outer_point", "image_domain"] {
        let (mut run, compiler) = super::execute(COMPOSE);
        let p = invocation(&mut run);
        if change == "outer_point" {
            let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[14]
            else {
                panic!()
            };
            f.point = super::number_object("0");
        } else {
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[15] else {
                panic!()
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(m)) = &mut f.then_facts[0]
            else {
                panic!()
            };
            m.set = Obj::StandardSet(StandardSet::RPos);
        }
        compiler
            .compile_run(&run, change)
            .expect_err("chain rule replays the actual outer evaluation point and image domain");
    }
}

#[test]
fn derivative_algebra_candidate_cannot_cite_its_future_output() {
    let (mut run, compiler) = super::execute(NEG);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    super::atomic_proof_mut(&mut p.dom_proofs[10]).searched_proof =
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(
            AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
                cite_fact_id: future,
                why_parameters_of_known_fact_are_equal_to_givens: Vec::new(),
            },
        );
    compiler
        .compile_run(&run, "future_candidate")
        .expect_err("input derivative precedes the output theorem");
}
