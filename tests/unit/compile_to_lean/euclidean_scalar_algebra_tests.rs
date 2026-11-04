use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCES: [&str; 8] = [
    include_str!("../../../lean/examples/multivariable_limit_add/statement.lit"),
    include_str!("../../../lean/examples/multivariable_limit_subtract/statement.lit"),
    include_str!("../../../lean/examples/multivariable_limit_multiply/statement.lit"),
    include_str!("../../../lean/examples/multivariable_limit_divide/statement.lit"),
    include_str!("../../../lean/examples/multivariable_continuous_add/statement.lit"),
    include_str!("../../../lean/examples/multivariable_continuous_subtract/statement.lit"),
    include_str!("../../../lean/examples/multivariable_continuous_multiply/statement.lit"),
    include_str!("../../../lean/examples/multivariable_continuous_divide/statement.lit"),
];
fn binary_right(o: &mut Obj) -> &mut Box<Obj> {
    match o {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => &mut x.right,
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => &mut x.right,
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => &mut x.right,
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => &mut x.right,
        _ => panic!(),
    }
}
#[test]
fn euclidean_scalar_algebra_replays_all_eight_rules_deterministically() {
    for (i, source) in SOURCES.iter().enumerate() {
        let (run, c) = super::execute(source);
        let out = c
            .compile_run(&run, "scalar_algebra")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        let family = if i < 4 { "Limit" } else { "Continuous" };
        let op = ["Add", "Subtract", "Multiply", "Divide"][i % 4];
        assert!(out.contains(&format!("Litex.scalarMultivariable{family}{op}")));
        assert_eq!(out, c.compile_run(&run, "scalar_algebra").unwrap());
    }
}
#[test]
fn euclidean_scalar_algebra_retains_original_ordered_stages() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "args",
            "result",
            "route",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                "proof_order" => p.dom_proofs.swap(0, 1),
                "store_order" => p.dom_stores.swap(0, 1),
                "args" => {
                    p.builtin.as_mut().unwrap().arguments.pop();
                }
                "result" => p.builtin.as_mut().unwrap().conclusions.clear(),
                _ => {
                    p.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            assert!(c.compile_run(&run, "bad_stages").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_scalar_algebra_requires_exact_pointwise_formula_and_binders() {
    for (i, source) in SOURCES.iter().enumerate() {
        for change in [
            "domain",
            "capture",
            "premise",
            "left",
            "right",
            "orientation",
            "operation",
        ] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let context = if i < 4 { 4 } else { 5 };
            let Fact::ForallFact(all) = &mut b.requirements[3 * context + 2] else {
                panic!()
            };
            match change {
                "domain" => {
                    all.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                "capture" => {
                    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &b.arguments[3] else {
                        panic!()
                    };
                    all.typed_parameters.groups[0].params[0].id = *id;
                }
                "premise" => all.dom_facts.push(Fact::ForallFact(all.clone())),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut all.then_facts[0]
                    else {
                        panic!()
                    };
                    if change == "left" {
                        eq.left = super::number_object("0");
                    } else if change == "right" {
                        *binary_right(&mut eq.right) = Box::new(super::number_object("0"));
                    } else if change == "operation" {
                        use crate::rational_expression::helper::{add_objs, sub_objs};
                        eq.right = match &eq.right {
                            Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
                                sub_objs((*x.left).clone(), (*x.right).clone())
                            }
                            Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
                                add_objs((*x.left).clone(), (*x.right).clone())
                            }
                            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
                                add_objs((*x.left).clone(), (*x.right).clone())
                            }
                            Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
                                add_objs((*x.left).clone(), (*x.right).clone())
                            }
                            _ => panic!(),
                        };
                    } else {
                        std::mem::swap(&mut eq.left, &mut eq.right);
                    }
                }
            }
            assert!(c.compile_run(&run, "bad_formula").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_scalar_algebra_division_requires_original_nonzero_subject_and_orientation() {
    for source in [SOURCES[3], SOURCES[7]] {
        for change in ["denominator", "zero", "orientation"] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) = b.requirements.last_mut().unwrap()
            else {
                panic!()
            };
            match change {
                "denominator" => f.left = super::number_object("0"),
                "zero" => f.right = super::number_object("1"),
                _ => std::mem::swap(&mut f.left, &mut f.right),
            }
            assert!(c.compile_run(&run, "bad_nonzero").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_scalar_algebra_requires_both_original_candidate_inferences() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for (i, source) in SOURCES.iter().enumerate() {
        for which in [0, 1] {
            for change in ["missing", "source", "derived", "domain"] {
                let (mut run, c) = super::execute(source);
                let p = invocation(&mut run);
                let index = 3 * if i < 4 { 4 } else { 5 } + which;
                let infer = &mut p.dom_stores[index].infer;
                if change == "missing" {
                    *infer = None;
                } else {
                    let Some(InferResult::AtomicFact(
                        InferAtomicFactResult::MultivariableAnalysisFact(rules),
                    )) = infer
                    else {
                        panic!()
                    };
                    let [InferMultivariableAnalysisFactResult::Definition(p)] =
                        rules.as_mut_slice()
                    else {
                        panic!()
                    };
                    match change {
                        "source" => p.source_fact_id = FactId::new(u64::MAX),
                        "derived" => p.derived.clear(),
                        _ => p.function_domain = None,
                    }
                }
                assert!(
                    c.compile_run(&run, "bad_candidate").is_err(),
                    "{change} /{which}"
                );
            }
        }
    }
}
#[test]
fn euclidean_scalar_algebra_rejects_future_formula_citation() {
    for (i, source) in SOURCES.iter().enumerate() {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let index = 3 * if i < 4 { 4 } else { 5 } + 2;
        let VerifyFactResult::ForallFact(f) = &mut p.dom_proofs[index] else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(f)) =
            f.as_mut()
        else {
            panic!("known formula")
        };
        f.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_formula").is_err());
    }
}
#[test]
fn euclidean_scalar_algebra_retains_formation_context_dimensions_and_limit_operation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for (i, source) in SOURCES.iter().enumerate() {
        for change in ["count", "context", "point", "dimension", "value"] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            if change == "count" || change == "context" {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                else {
                    panic!()
                };
                let PredicateDomainProof::MultivariableAnalysis(f) =
                    &mut wd.as_detailed_mut().unwrap().predicate_domain
                else {
                    panic!()
                };
                if change == "count" {
                    f.requirements.pop();
                } else {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut f.requirements[0].requirement
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::R);
                }
            } else {
                let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!()
                };
                match &mut f.relation {
                    MultivariableAnalysisRelation::ScalarContinuousAt(r) => {
                        if change == "point" {
                            r.point = super::number_object("99");
                        } else {
                            r.dimension = super::number_object("99");
                        }
                    }
                    MultivariableAnalysisRelation::ScalarLimit(r) => {
                        if change == "value" {
                            *binary_right(&mut r.value) = Box::new(super::number_object("99"));
                        } else if change == "point" {
                            r.point = super::number_object("99");
                        } else {
                            r.dimension = super::number_object("99");
                        }
                    }
                    _ => panic!("{i}"),
                }
            }
            assert!(c.compile_run(&run, "bad_formation").is_err(), "{change}");
        }
    }
}

#[test]
fn euclidean_scalar_algebra_preserves_generic_and_guarded_domains() {
    for source in [
        include_str!("../../../lean/examples/multivariable_limit_add_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_subtract_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_multiply_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_divide_generic/statement.lit"),
        include_str!("../../../lean/examples/multivariable_continuous_add_generic/statement.lit"),
        include_str!(
            "../../../lean/examples/multivariable_continuous_subtract_generic/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_continuous_multiply_generic/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_continuous_divide_generic/statement.lit"
        ),
        include_str!("../../../lean/examples/multivariable_limit_add_guarded/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_subtract_guarded/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_multiply_guarded/statement.lit"),
        include_str!("../../../lean/examples/multivariable_limit_divide_guarded/statement.lit"),
        include_str!("../../../lean/examples/multivariable_continuous_add_guarded/statement.lit"),
        include_str!(
            "../../../lean/examples/multivariable_continuous_subtract_guarded/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_continuous_multiply_guarded/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_continuous_divide_guarded/statement.lit"
        ),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "actual_domains")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}

#[test]
fn euclidean_scalar_algebra_division_accepts_general_nonzero_real_denominators() {
    for source in [
        include_str!(
            "../../../lean/examples/multivariable_limit_divide_general_nonzero/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/multivariable_continuous_divide_general_nonzero/statement.lit"
        ),
    ] {
        let (run, c) = super::execute(source);
        let out = c
            .compile_run(&run, "nonzero_real")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(out.contains("Divide"));
    }
}
