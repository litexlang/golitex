use super::antiderivative_tests::body;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SOURCES: [&str; 2] = [
    r#"# Reverse integration endpoints and negate the original candidate value.
thm riemann_builtin_reverse:
    ? forall f fn(x R) R,a,b,v R:
        $has_riemann_integral(f,a,b,v)
        =>:
            $has_riemann_integral(f,b,a,(-1)*v)
    release thm riemann_integral_reverse(f,a,b,v)
"#,
    r#"# Transfer an integral using equality only on the sorted closed integration interval.
thm riemann_builtin_extensional:
    ? forall f,g fn(x R) R,a,b,v R:
        $has_riemann_integral(f,a,b,v)
        forall x '[min(a,b),max(a,b)]:
            f(x)=g(x)
        =>:
            $has_riemann_integral(g,a,b,v)
    release thm riemann_integral_extensional(f,g,a,b,v)
"#,
];
const VARIANTS: [(&str, bool); 3] = [
    (
        r#"# Reverse a zero-width integral while retaining the original guarded function domain.
thm riemann_builtin_reverse_guarded_zero:
    ? forall f fn(x R:x>0) R,a,v R:
        '[min(a,a),max(a,a)] $subset {t R:t>0}
        $has_riemann_integral(f,a,a,v)
        =>:
            $has_riemann_integral(f,a,a,(-1)*v)
    release thm riemann_integral_reverse(f,a,a,v)
"#,
        true,
    ),
    (
        r#"# Transfer an integral between a full-real-domain function and a positive-domain function.
thm riemann_builtin_extensional_independent_domains:
    ? forall f fn(x R) R,g fn(x R+) R,a,b,v R:
        '[min(a,b),max(a,b)] $subset R+
        $has_riemann_integral(f,a,b,v)
        forall x '[min(a,b),max(a,b)]:
            f(x)=g(x)
        =>:
            $has_riemann_integral(g,a,b,v)
    release thm riemann_integral_extensional(f,g,a,b,v)
"#,
        false,
    ),
    (
        r#"# Establish each original point's function-domain guard before replaying interval equality.
thm riemann_builtin_extensional_guarded:
    ? forall f fn(x R) R,g fn(x R:x>0) R,a,b,v R:
        '[min(a,b),max(a,b)] $subset {t R:t>0}
        $has_riemann_integral(f,a,b,v)
        forall x '[min(a,b),max(a,b)]:
            x>0
            =>:
                f(x)=g(x)
        =>:
            $has_riemann_integral(g,a,b,v)
    claim:
        ? forall x '[min(a,b),max(a,b)]:
            x>0
        x $in {t R:t>0}
        x>0
    claim:
        ? forall x '[min(a,b),max(a,b)]:
            f(x)=g(x)
        x>0
        f(x)=g(x)
    release thm riemann_integral_extensional(f,g,a,b,v)
"#,
        false,
    ),
];
fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    for step in body(run).proof_steps.iter_mut().rev() {
        if let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(p),
        )) = step
        {
            return p;
        }
    }
    panic!("original Riemann invocation")
}

#[test]
fn riemann_transport_replays_original_oriented_and_interval_equality_schemas() {
    for (source, reverse) in [(SOURCES[0], true), (SOURCES[1], false)]
        .into_iter()
        .chain(VARIANTS)
    {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(
            p.builtin.as_ref().unwrap().theorem,
            if reverse {
                BuiltinTheoremId::RiemannIntegralReverse
            } else {
                BuiltinTheoremId::RiemannIntegralExtensional
            }
        );
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), if reverse { 4 } else { 8 });
        assert_eq!(p.dom_stores.len(), p.dom_proofs.len());
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "riemann_transport").unwrap();
        assert!(out.contains(if reverse {
            "Litex.riemannIntegralReverseCandidate"
        } else {
            "Litex.riemannIntegralLocalAgreement"
        }));
        assert_eq!(out, c.compile_run(&run, "riemann_transport").unwrap());
    }
}

#[test]
fn riemann_transport_requires_every_original_pipeline_stage() {
    for source in SOURCES {
        for change in 0..9 {
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
                7 => {
                    p.builtin.as_mut().unwrap().requirements.pop();
                }
                _ => p.builtin.as_mut().unwrap().conclusions.clear(),
            }
            assert!(
                c.compile_run(&run, "changed_riemann_transport_stage")
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn riemann_transport_preserves_positive_candidates_and_every_original_argument() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for goal in [false, true] {
            for change in 0..5 {
                let (mut run, c) = super::execute(source);
                let b = invocation(&mut run).builtin.as_mut().unwrap();
                let f = if goal {
                    &mut b.conclusions[0]
                } else {
                    &mut b.requirements[if i == 0 { 3 } else { 6 }]
                };
                let Fact::AtomicFact(f) = f else { panic!() };
                if change == 4 {
                    *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap();
                } else {
                    let AtomicFact::HasRiemannIntegralFact(p) = f else {
                        panic!()
                    };
                    match change {
                        0 => p.function = super::number_object("99"),
                        1 => p.lower = super::number_object("99"),
                        2 => p.upper = super::number_object("99"),
                        _ => p.value = super::number_object("99"),
                    }
                }
                assert!(
                    c.compile_run(&run, "changed_riemann_transport_candidate")
                        .is_err(),
                    "{i}/{goal}/{change}"
                );
            }
        }
    }
}

#[test]
fn riemann_transport_preserves_original_function_contexts_and_interval_orientation() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for index in 0..if i == 0 { 3 } else { 6 } {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
                Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                    std::mem::swap(&mut p.left, &mut p.right)
                }
                _ => panic!(),
            }
            assert!(
                c.compile_run(&run, "changed_riemann_transport_context")
                    .is_err(),
                "{i}/{index}"
            );
        }
    }
}

#[test]
fn riemann_transport_retains_original_signed_multiplier_and_endpoint_order() {
    for change in 0..4 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(p)) = &mut b.conclusions[0] else {
            panic!()
        };
        match change {
            0 => std::mem::swap(&mut p.lower, &mut p.upper),
            _ => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) = &mut p.value else {
                    panic!()
                };
                match change {
                    1 => std::mem::swap(&mut m.left, &mut m.right),
                    2 => m.left = Box::new(super::number_object("1")),
                    _ => m.right = Box::new(super::number_object("99")),
                }
            }
        }
        assert!(
            c.compile_run(&run, "changed_riemann_orientation").is_err(),
            "{change}"
        );
    }
}

#[test]
fn riemann_transport_keeps_original_interval_equation_binder_subjects_and_polarity() {
    for change in 0..8 {
        let (mut run, c) = super::execute(SOURCES[1]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let guard = b.requirements[0].clone();
        let Obj::Identifier(IdentifierObj::Plain { id: captured, .. }) = &b.arguments[0] else {
            panic!()
        };
        let captured = *captured;
        let Fact::ForallFact(p) = &mut b.requirements[7] else {
            panic!()
        };
        match change {
            0 => {
                p.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            1 => p.typed_parameters.groups[0].params[0].id = captured,
            2 => p.dom_facts.push(guard),
            3 => p.then_facts.clear(),
            _ => {
                let ExistOrAndChainAtomicFact::AtomicFact(f) = &mut p.then_facts[0] else {
                    panic!()
                };
                if change == 7 {
                    *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap();
                } else {
                    let AtomicFact::EqualFact(eq) = f else {
                        panic!()
                    };
                    match change {
                        4 => std::mem::swap(&mut eq.left, &mut eq.right),
                        5 => eq.left = super::number_object("99"),
                        _ => eq.right = super::number_object("99"),
                    }
                }
            }
        }
        assert!(
            c.compile_run(&run, "changed_riemann_interval_equation")
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn riemann_transport_requires_original_source_and_target_formation_and_domains() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for target in [false, true] {
            for change in 0..5 {
                let (mut run, c) = super::execute(source);
                let wd = if target {
                    let FactWellDefinedProof::AtomicExceptEquality(wd) =
                        &mut invocation(&mut run).conclusions_wd[0]
                    else {
                        panic!()
                    };
                    wd
                } else {
                    let FactWellDefinedProof::AtomicExceptEquality(wd) =
                        &mut body(&mut run).assumed_dom_facts[0].well_defined
                    else {
                        panic!()
                    };
                    wd
                };
                let d = wd.as_detailed_mut().unwrap();
                if change == 4 {
                    d.well_defined_of_each_parameter.pop();
                } else {
                    let PredicateDomainProof::FunctionAnalysis(cap) = &mut d.predicate_domain
                    else {
                        panic!("original function formation")
                    };
                    match change {
                        0 => {
                            cap.requirements.pop();
                        }
                        1 => cap.requirements.swap(0, 1),
                        2 => cap.function_domain.domain = Obj::StandardSet(StandardSet::C),
                        _ => {
                            let Fact::AtomicFact(AtomicFact::SubsetFact(p)) =
                                &mut cap.requirements[2].requirement
                            else {
                                panic!()
                            };
                            p.right = Obj::StandardSet(StandardSet::C);
                        }
                    }
                }
                assert!(
                    c.compile_run(&run, "changed_riemann_transport_formation")
                        .is_err(),
                    "{i}/{target}/{change}"
                );
            }
        }
    }
}

#[test]
fn riemann_transport_rejects_future_candidate_and_pointwise_citations() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let proof = super::atomic_proof_mut(&mut p.dom_proofs[if i == 0 { 3 } else { 6 }]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
            &mut proof.searched_proof
        else {
            panic!()
        };
        cite.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_riemann_candidate").is_err());
    }
    let (mut run, c) = super::execute(SOURCES[1]);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let VerifyFactResult::ForallFact(proof) = &mut p.dom_proofs[7] else {
        panic!()
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
        proof.as_mut()
    else {
        panic!()
    };
    proof.cite_fact_id = future;
    assert!(c.compile_run(&run, "future_riemann_equation").is_err());
}

#[test]
fn riemann_transport_replays_nested_signed_literal_identity_in_final_citations() {
    for source in [SOURCES[0], VARIANTS[0].0] {
        let (mut run, c) = super::execute(source);
        let all = body(&mut run);
        let proof = super::atomic_proof_mut(&mut all.conclusion_proofs[0]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &proof.searched_proof
        else {
            panic!()
        };
        assert!(matches!(
            &cite.why_parameters_of_known_fact_are_equal_to_givens[3],
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
        ));
        let out = c.compile_run(&run, "signed_integral_identity").unwrap();
        assert!(out.contains("M.neg_numbers"));
        assert!(out.contains("_known_argument_eq_3"));
    }
}

#[test]
fn riemann_transport_source_requires_actual_candidate_and_interval_equations() {
    for (i, original) in SOURCES.into_iter().enumerate() {
        for change in 0..if i == 0 { 1 } else { 2 } {
            let source = if change == 0 {
                original.replace("        $has_riemann_integral(f,a,b,v)\n", "")
            } else {
                original.replace(
                    "        forall x '[min(a,b),max(a,b)]:\n            f(x)=g(x)\n",
                    "",
                )
            };
            let command =
                parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
            let mut runtime = Runtime::new_with_result_detail(
                command,
                crate::result_detail::OutputDetail::Detailed,
            );
            let run = runtime.run_litex_code(&source).unwrap();
            assert!(!run.success);
            assert!(super::LitexToLeanCompiler::new(runtime)
                .compile_run(&run, "unproved_riemann_transport")
                .is_err());
        }
    }
}
