use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
use crate::prelude::*;
const SOURCES: [&str; 4] = [
    r#"# A real Riemann integral candidate supplies an integral value.
thm checked_riemann_certificate_exists:
    ? forall f fn(x R) R,a,b,I R:
        $has_riemann_integral(f,a,b,I)
        =>:
            exist J R st {$has_riemann_integral(f,a,b,J)}
    release thm riemann_integral_exists(f,a,b,I)
"#,
    r#"# A real integral candidate establishes Riemann integrability.
thm checked_riemann_certificate_integrable_from_candidate:
    ? forall f fn(x R) R,a,b,I R:
        $has_riemann_integral(f,a,b,I)
        =>:
            $is_riemann_integrable(f,a,b)
    release thm riemann_integrable_from_candidate(f,a,b,I)
"#,
    r#"# The selected Riemann integral satisfies its defining candidate predicate.
thm checked_riemann_certificate_selected:
    ? forall f fn(x R) R,a,b R:
        exist I R st {$has_riemann_integral(f,a,b,I)}
        =>:
            $has_riemann_integral(f,a,b,integral(f,a,b))
    release thm riemann_integral_selected(f,a,b)
"#,
    r#"# Two integral candidates on the same oriented interval have equal values.
thm checked_riemann_certificate_unique:
    ? forall f fn(x R) R,a,b,I,J R:
        $has_riemann_integral(f,a,b,I)
        $has_riemann_integral(f,a,b,J)
        =>:
            I=J
    release thm riemann_integral_unique(f,a,b,I,J)
"#,
];
fn original_wd(run: &mut RunLitexCodeResult, selected: bool) -> &mut AtomicFactWellDefinedProof {
    if selected {
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut invocation(run).conclusions_wd[0]
        else {
            panic!()
        };
        return wd;
    }
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!()
    };
    let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.assumed_dom_facts[0].well_defined
    else {
        panic!()
    };
    wd
}
#[test]
fn riemann_certificates_replay_four_actual_native_schemas_deterministically() {
    for ((source, id), law) in SOURCES
        .into_iter()
        .zip([
            BuiltinTheoremId::RiemannIntegralExists,
            BuiltinTheoremId::RiemannIntegrableFromCandidate,
            BuiltinTheoremId::RiemannIntegralSelected,
            BuiltinTheoremId::RiemannIntegralUnique,
        ])
        .zip([
            "riemannIntegralExistsOfCandidate",
            "riemannIntegralExistsOfCandidate",
            "riemannIntegralValueSelected",
            "riemannIntegralCandidatesEqual",
        ])
    {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(p.builtin.as_ref().unwrap().theorem, id);
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(
            p.dom_proofs.len(),
            if id == BuiltinTheoremId::RiemannIntegralUnique {
                5
            } else {
                4
            }
        );
        let out = c.compile_run(&run, "integral_certificate").unwrap();
        assert!(out.contains(&format!("Litex.{law}")));
        assert!(out.contains("_riemann_original_real"));
        assert_eq!(out, c.compile_run(&run, "integral_certificate").unwrap());
    }
}
#[test]
fn riemann_certificates_require_all_original_ordered_pipeline_stages() {
    for source in SOURCES {
        for change in 0..8 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => {
                    p.dom_stores.pop();
                }
                2 => p.dom_proofs.swap(0, 1),
                3 => p.dom_stores.swap(0, 1),
                4 => p.conclusions_wd.clear(),
                5 => p.theorem_derivation = TheoremDerivationProof::UserTheorem,
                6 => p.builtin.as_mut().unwrap().arguments.clear(),
                _ => p.builtin.as_mut().unwrap().requirements.swap(0, 1),
            }
            assert!(
                c.compile_run(&run, "damaged_integral_stages").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn riemann_certificates_preserve_real_endpoints_and_complete_interval_coverage() {
    for source in SOURCES {
        for change in 0..5 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            if change < 2 {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[change] else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::C);
            } else {
                let Fact::AtomicFact(AtomicFact::SubsetFact(f)) = &mut b.requirements[2] else {
                    panic!()
                };
                match change {
                    2 => f.right = Obj::StandardSet(StandardSet::Q),
                    3 => f.left = Obj::StandardSet(StandardSet::R),
                    _ => std::mem::swap(&mut f.left, &mut f.right),
                }
            }
            assert!(
                c.compile_run(&run, "bad_integral_context").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn riemann_certificates_reject_changed_candidate_function_endpoints_and_value() {
    for source in [SOURCES[0], SOURCES[1], SOURCES[3]] {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(f)) =
                &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[3]
            else {
                panic!()
            };
            match change {
                0 => f.function = super::number_object("9"),
                1 => f.lower = super::number_object("9"),
                2 => f.upper = super::number_object("9"),
                _ => f.value = super::number_object("9"),
            }
            assert!(
                c.compile_run(&run, "bad_integral_candidate").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn riemann_certificates_retain_original_candidate_function_domain_and_value_formation() {
    for (index, source) in SOURCES.into_iter().enumerate() {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let wd = original_wd(&mut run, index == 2);
            let PredicateDomainProof::FunctionAnalysis(p) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("actual original integral formation")
            };
            match change {
                0 => p.requirements.clear(),
                1 => p.function_domain.domain = Obj::StandardSet(StandardSet::Q),
                2 => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut p.requirements[3].requirement
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::Q);
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(f)) =
                        &mut p.requirements[2].requirement
                    else {
                        panic!()
                    };
                    f.right = Obj::StandardSet(StandardSet::Q);
                }
            }
            assert!(
                c.compile_run(&run, "bad_original_integral_formation")
                    .is_err(),
                "{index}/{change}"
            );
        }
    }
}
#[test]
fn riemann_certificates_cannot_cite_their_future_conclusion_as_a_premise() {
    for (index, source) in SOURCES.into_iter().enumerate() {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        if index == 2 {
            let VerifyFactResult::ExistShapedFact(r) = &mut p.dom_proofs[3] else {
                panic!()
            };
            let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(r)) =
                r.as_mut()
            else {
                panic!()
            };
            let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) = &mut r.searched_proof
            else {
                panic!("original existence citation")
            };
            cite.cite_fact_id = future;
        } else {
            let child = super::atomic_proof_mut(&mut p.dom_proofs[3]);
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut child.searched_proof
            else {
                panic!()
            };
            cite.cite_fact_id = future;
        }
        assert!(c.compile_run(&run, "future_integral_premise").is_err());
    }
}
#[test]
fn integral_existence_retains_real_witness_and_fresh_binder_identity() {
    for change in 0..3 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &b.arguments[0] else {
            panic!()
        };
        let id = *id;
        let Fact::ExistFact(f) = &mut b.conclusions[0] else {
            panic!()
        };
        match change {
            0 => {
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::Q))
            }
            1 => f.typed_parameters.groups[0].params[0].id = id,
            _ => f.facts.push(f.facts[0].clone()),
        }
        assert!(
            c.compile_run(&run, "bad_integral_existence").is_err(),
            "{change}"
        );
    }
}
#[test]
fn integral_selection_retains_existing_selector_and_exact_three_arguments() {
    for change in 0..4 {
        let (mut run, c) = super::execute(SOURCES[2]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(f)) = &mut b.conclusions[0] else {
            panic!()
        };
        let Obj::IntegralOperator(IntegralOperator::Riemann(integral)) = &mut f.value else {
            panic!()
        };
        match change {
            0 => integral.function = super::number_object("9").into(),
            1 => integral.lower = super::number_object("9").into(),
            2 => integral.upper = super::number_object("9").into(),
            _ => f.function = super::number_object("9"),
        }
        assert!(
            c.compile_run(&run, "bad_integral_selection").is_err(),
            "{change}"
        );
    }
}
#[test]
fn integral_uniqueness_retains_second_candidate_and_oriented_equal_conclusion() {
    for change in 0..3 {
        let (mut run, c) = super::execute(SOURCES[3]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if change < 2 {
            let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(f)) = &mut b.requirements[4]
            else {
                panic!()
            };
            if change == 0 {
                f.value = b.arguments[3].clone();
            } else {
                std::mem::swap(&mut f.lower, &mut f.upper);
            }
        } else {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut b.conclusions[0] else {
                panic!()
            };
            std::mem::swap(&mut f.left, &mut f.right);
        }
        assert!(
            c.compile_run(&run, "bad_integral_uniqueness").is_err(),
            "{change}"
        );
    }
}
#[test]
fn integral_certificates_preserve_original_integrability_subject() {
    for change in 0..3 {
        let (mut run, c) = super::execute(SOURCES[1]);
        let Fact::AtomicFact(AtomicFact::FunctionRiemannIntegrableFact(f)) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().conclusions[0]
        else {
            panic!()
        };
        match change {
            0 => f.function = super::number_object("9"),
            1 => f.lower = super::number_object("9"),
            _ => f.upper = super::number_object("9"),
        }
        assert!(
            c.compile_run(&run, "bad_integrability_subject").is_err(),
            "{change}"
        );
    }
}

const TRANSPORTS: [&str; 6] = [
    r#"# Transport the original integral predicate along the recorded value equality.
thm checked_riemann_candidate_transport:
    ? forall f fn(x R) R,a,b,I,J R:
        $has_riemann_integral(f,a,b,I)
        I=J
        =>:
            $has_riemann_integral(f,a,b,J)
    $has_riemann_integral(f,a,b,J)
"#,
    r#"# Transport the original integral predicate along the recorded value equality.
thm checked_riemann_negative_candidate_transport:
    ? forall f fn(x R) R,a,b,I,J R:
        not $has_riemann_integral(f,a,b,I)
        I=J
        =>:
            not $has_riemann_integral(f,a,b,J)
    not $has_riemann_integral(f,a,b,J)
"#,
    r#"# Transport the original integrability predicate along a function equality.
thm checked_riemann_integrability_transport:
    ? forall f,g fn(x R) R,a,b R:
        $is_riemann_integrable(f,a,b)
        f=g
        =>:
            $is_riemann_integrable(g,a,b)
    $is_riemann_integrable(g,a,b)
"#,
    r#"# Transport the original integrability predicate along a function equality.
thm checked_riemann_negative_integrability_transport:
    ? forall f,g fn(x R) R,a,b R:
        not $is_riemann_integrable(f,a,b)
        f=g
        =>:
            not $is_riemann_integrable(g,a,b)
    not $is_riemann_integrable(g,a,b)
"#,
    r#"# An existing integral candidate equals the selected integral and certifies it.
thm checked_riemann_selector_existing_inference_closed:
    ? forall f fn(x '[0,1]) R,I R:
        $has_riemann_integral(f,0,1,I)
        =>:
            $has_riemann_integral(f,0,1,integral(f,0,1))
    integral(f,0,1)=I
    $has_riemann_integral(f,0,1,integral(f,0,1))
"#,
    r#"# An existing integral candidate equals the selected integral and certifies it.
thm checked_riemann_selector_existing_inference_named:
    ? forall D set,f fn(x D) R,a,b,I R:
        D $subset R
        '[min(a,b),max(a,b)] $subset D
        $has_riemann_integral(f,a,b,I)
        =>:
            $has_riemann_integral(f,a,b,integral(f,a,b))
    integral(f,a,b)=I
    $has_riemann_integral(f,a,b,integral(f,a,b))
"#,
];
fn transported(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!()
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = body.proof_steps.last_mut().unwrap()
    else {
        panic!("actual ordinary assertion")
    };
    super::atomic_proof_mut(&mut p.verify_result)
}
#[test]
fn riemann_predicate_transport_keeps_original_citation_and_ordered_equality_winners() {
    for source in TRANSPORTS {
        for change in 0..3 {
            let (mut run, c) = super::execute(source);
            let p = transported(&mut run);
            let future = p.fact.fact_id();
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut p.searched_proof
            else {
                panic!("actual source argument transport")
            };
            match change {
                0 => {
                    cite.why_parameters_of_known_fact_are_equal_to_givens.pop();
                }
                1 => {
                    let last = cite.why_parameters_of_known_fact_are_equal_to_givens.len() - 1;
                    cite.why_parameters_of_known_fact_are_equal_to_givens
                        .swap(0, last);
                }
                _ => cite.cite_fact_id = future,
            }
            assert!(
                c.compile_run(&run, "damaged_riemann_argument_transport")
                    .is_err(),
                "{change}"
            );
        }
    }
}
