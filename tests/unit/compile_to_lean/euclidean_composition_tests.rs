use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCES: [&str; 4] = [
    r#"# Compose a Euclidean real function with a continuous unary real function.
thm checked_multivariable_continuous_compose:
    ? forall f,h fn(x cart_n(R,2)) R,g fn(t R) R,p cart_n(R,2):
        $is_multi_continuous_at(f,p,2)
        $is_continuous_at(g,f(p))
        forall x cart_n(R,2):
            h(x)=g(f(x))
        =>:
            $is_multi_continuous_at(h,p,2)
    release thm multi_continuous_at_compose(f,g,h,p,2)
"#,
    r#"# Continuity of the outer real function transports an independently checked Euclidean limit.
thm checked_multivariable_limit_compose:
    ? forall f,h fn(x cart_n(R,2)) R,g fn(t R) R,p cart_n(R,2),L R:
        $has_multi_limit_at(f,p,2,L)
        $is_continuous_at(g,L)
        forall x cart_n(R,2):
            h(x)=g(f(x))
        =>:
            $has_multi_limit_at(h,p,2,g(L))
    release thm multi_limit_at_compose(f,g,h,p,2,L)
"#,
    r#"# Compose continuous Euclidean vector functions while retaining all three dimensions.
thm checked_vector_continuous_compose:
    ? forall f fn(x cart_n(R,2)) cart_n(R,3),g fn(y cart_n(R,3)) cart_n(R,4),h fn(z cart_n(R,2)) cart_n(R,4),p cart_n(R,2):
        $is_vector_continuous_at(f,p,2,3)
        $is_vector_continuous_at(g,f(p),3,4)
        forall x cart_n(R,2):
            h(x)=g(f(x))
        =>:
            $is_vector_continuous_at(h,p,2,4)
    release thm vector_continuous_at_compose(f,g,h,p,2,3,4)
"#,
    r#"# A continuous outer vector function transports a Euclidean vector limit on the same domain.
thm checked_vector_limit_compose:
    ? forall f fn(x cart_n(R,2)) cart_n(R,3),g fn(y cart_n(R,3)) cart_n(R,4),h fn(z cart_n(R,2)) cart_n(R,4),p cart_n(R,2),L cart_n(R,3):
        $has_vector_limit_at(f,p,2,3,L)
        $is_vector_continuous_at(g,L,3,4)
        forall x cart_n(R,2):
            h(x)=g(f(x))
        =>:
            $has_vector_limit_at(h,p,2,4,g(L))
    release thm vector_limit_at_compose(f,g,h,p,2,3,4,L)
"#,
];
#[test]
fn euclidean_composition_requires_all_original_ordered_stages() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "arguments",
            "conclusion",
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
                "arguments" => {
                    p.builtin.as_mut().unwrap().arguments.pop();
                }
                "conclusion" => p.builtin.as_mut().unwrap().conclusions.clear(),
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
fn euclidean_composition_requires_exact_global_mapping_and_formula() {
    for source in SOURCES {
        for change in [
            "domain",
            "capture",
            "premise",
            "mapping_function",
            "mapping_target",
            "formula_orientation",
            "formula_inner",
            "formula_outer",
        ] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let len = b.requirements.len();
            let q = if change.starts_with("formula_") {
                len - 1
            } else {
                len - 2
            };
            let Fact::ForallFact(all) = &mut b.requirements[q] else {
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
                "mapping_function" | "mapping_target" => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut all.then_facts[0]
                    else {
                        panic!()
                    };
                    if change == "mapping_function" {
                        f.element = super::number_object("0");
                    } else {
                        f.set = Obj::StandardSet(StandardSet::C);
                    }
                }
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f)) =
                        &mut all.then_facts[0]
                    else {
                        panic!()
                    };
                    if change == "formula_orientation" {
                        std::mem::swap(&mut f.left, &mut f.right);
                    } else if change == "formula_inner" {
                        f.right = super::number_object("0");
                    } else {
                        f.left = super::number_object("0");
                    }
                }
            }
            assert!(c.compile_run(&run, "bad_clauses").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_composition_requires_original_inner_inference_and_domain() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for (i, source) in SOURCES.iter().enumerate() {
        for change in ["missing", "source", "derived", "domain"] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let index = if i < 2 {
                if i == 0 {
                    5
                } else {
                    4
                }
            } else if i == 2 {
                6
            } else {
                5
            };
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
                let [InferMultivariableAnalysisFactResult::Definition(r)] = rules.as_mut_slice()
                else {
                    panic!()
                };
                match change {
                    "source" => r.source_fact_id = FactId::new(u64::MAX),
                    "derived" => r.derived.clear(),
                    _ => r.function_domain = None,
                }
            }
            assert!(c.compile_run(&run, "bad_inference").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_composition_keeps_outer_two_sided_continuity_and_domain() {
    for (i, source) in SOURCES.iter().take(2).enumerate() {
        for change in ["side", "point", "function", "member"] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = if i == 0 { 7 } else { 6 };
            if change == "member" {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[index - 1] else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::C);
            } else {
                let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) =
                    &mut b.requirements[index]
                else {
                    panic!()
                };
                match change {
                    "side" => f.side = RealApproachSide::Right,
                    "point" => f.point = super::number_object("0"),
                    _ => f.function = super::number_object("0"),
                }
            }
            assert!(c.compile_run(&run, "bad_outer").is_err(), "{change}");
        }
    }
}
#[test]
fn euclidean_composition_rejects_future_formula_citations() {
    for source in SOURCES {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let VerifyFactResult::ForallFact(f) = p.dom_proofs.last_mut().unwrap() else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(f)) =
            f.as_mut()
        else {
            panic!("forall citation")
        };
        f.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_formula").is_err());
    }
}

#[test]
fn euclidean_composition_retains_output_formation_and_three_distinct_dimensions() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for source in SOURCES {
        for change in ["context", "count", "dimension", "point", "value"] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            if change == "context" || change == "count" {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                else {
                    panic!()
                };
                let PredicateDomainProof::MultivariableAnalysis(r) =
                    &mut wd.as_detailed_mut().unwrap().predicate_domain
                else {
                    panic!()
                };
                if change == "count" {
                    r.requirements.pop();
                } else {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut r.requirements[0].requirement
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
                    MultivariableAnalysisRelation::VectorContinuousAt(r) => {
                        if change == "point" {
                            r.point = super::number_object("99");
                        } else {
                            r.output_dimension = super::number_object("99");
                        }
                    }
                    MultivariableAnalysisRelation::ScalarLimit(r) => {
                        if change == "value" {
                            r.value = super::number_object("99");
                        } else {
                            r.point = super::number_object("99");
                        }
                    }
                    MultivariableAnalysisRelation::VectorLimit(r) => {
                        if change == "value" {
                            r.value = super::number_object("99");
                        } else {
                            r.output_dimension = super::number_object("99");
                        }
                    }
                    _ => panic!(),
                }
            }
            assert!(c.compile_run(&run, "bad_output").is_err(), "{change}");
        }
    }
}

#[test]
fn euclidean_composition_preserves_guarded_common_domain_and_rejects_its_erasure() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for source in [
        r#"# Compose a Euclidean real function with a continuous unary real function.
thm guarded_multivariable_continuous_compose:
    ? forall f,h fn(x cart_n(R,2): x(1)>0) R,g fn(t R) R,p cart_n(R,2):
        p(1)>0
        $is_multi_continuous_at(f,p,2)
        $is_continuous_at(g,f(p))
        forall x {z cart_n(R,2): z(1)>0}:
            h(x)=g(f(x))
        =>:
            $is_multi_continuous_at(h,p,2)
    release thm multi_continuous_at_compose(f,g,h,p,2)
"#,
        r#"# Continuity of the outer real function transports an independently checked Euclidean limit.
thm guarded_multivariable_limit_compose:
    ? forall f,h fn(x cart_n(R,2): x(1)>0) R,g fn(t R) R,p cart_n(R,2),L R:
        $has_multi_limit_at(f,p,2,L)
        $is_continuous_at(g,L)
        forall x {z cart_n(R,2): z(1)>0}:
            h(x)=g(f(x))
        =>:
            $has_multi_limit_at(h,p,2,g(L))
    release thm multi_limit_at_compose(f,g,h,p,2,L)
"#,
        r#"# Compose continuous Euclidean vector functions while retaining all three dimensions.
thm guarded_vector_continuous_compose:
    ? forall f fn(x cart_n(R,2): x(1)>0) cart_n(R,3),g fn(y cart_n(R,3)) cart_n(R,4),h fn(z cart_n(R,2): z(1)>0) cart_n(R,4),p cart_n(R,2):
        p(1)>0
        $is_vector_continuous_at(f,p,2,3)
        $is_vector_continuous_at(g,f(p),3,4)
        forall x {z cart_n(R,2): z(1)>0}:
            h(x)=g(f(x))
        =>:
            $is_vector_continuous_at(h,p,2,4)
    release thm vector_continuous_at_compose(f,g,h,p,2,3,4)
"#,
        r#"# A continuous outer vector function transports a Euclidean vector limit on the same domain.
thm guarded_vector_limit_compose:
    ? forall f fn(x cart_n(R,2): x(1)>0) cart_n(R,3),g fn(y cart_n(R,3)) cart_n(R,4),h fn(z cart_n(R,2): z(1)>0) cart_n(R,4),p cart_n(R,2),L cart_n(R,3):
        $has_vector_limit_at(f,p,2,3,L)
        $is_vector_continuous_at(g,L,3,4)
        forall x {z cart_n(R,2): z(1)>0}:
            h(x)=g(f(x))
        =>:
            $has_vector_limit_at(h,p,2,4,g(L))
    release thm vector_limit_at_compose(f,g,h,p,2,3,4,L)
"#,
    ] {
        let (mut run, c) = super::execute(source);
        c.compile_run(&run, "guarded_composition")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        let p = invocation(&mut run);
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
            panic!()
        };
        let PredicateDomainProof::MultivariableAnalysis(formation) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!()
        };
        assert!(!formation.function_domain.signature.dom_facts.is_empty());
        formation.function_domain.signature.dom_facts.clear();
        assert!(c.compile_run(&run, "erased_actual_domain").is_err());
    }
}
