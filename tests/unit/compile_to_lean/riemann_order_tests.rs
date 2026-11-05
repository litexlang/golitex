use super::antiderivative_tests::body;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SOURCES: [&str; 2] = [
    r#"# Pointwise comparison on the closed interval orders the two recorded integral candidates.
thm riemann_builtin_compare:
    ? forall f,g fn(x R) R,a,b,v,w R:
        a<=b
        $has_riemann_integral(f,a,b,v)
        $has_riemann_integral(g,a,b,w)
        forall x '[a,b]:
            f(x)<=g(x)
        =>:
            v<=w
    release thm riemann_integral_compare(f,g,a,b,v,w)
"#,
    r#"# Bound the recorded integral by a pointwise absolute bound over its sorted interval.
thm riemann_builtin_absolute_bound:
    ? forall f fn(x R) R,a,b,v,c R:
        $has_riemann_integral(f,a,b,v)
        0<=c
        forall x '[min(a,b),max(a,b)]:
            abs(f(x))<=c
        =>:
            abs(v)<=c*abs(b-a)
    release thm riemann_integral_bound(f,a,b,v,c)
"#,
];
const VARIANTS: [(&str, bool); 5] = [
    (
        r#"# Keep the positive-domain function and establish each original point's domain guard.
thm riemann_builtin_compare_independent_domains:
    ? forall f fn(x R) R,g fn(x R+) R,v,w R:
        '[1,3] $subset R+
        $has_riemann_integral(f,1,3,v)
        $has_riemann_integral(g,1,3,w)
        forall x '[1,3]:
            x $in R+
            =>:
                f(x)<=g(x)
        =>:
            v<=w
    claim:
        ? forall x '[1,3]:
            x $in R+
        x>=1
        x>0
        x $in R+
    claim:
        ? forall x '[1,3]:
            f(x)<=g(x)
        x $in R+
        f(x)<=g(x)
    release thm riemann_integral_compare(f,g,1,3,v,w)
"#,
        true,
    ),
    (
        r#"# Comparison also retains both original candidates on an equal-endpoint interval.
thm riemann_builtin_compare_zero_width:
    ? forall f,g fn(x R) R,a,v,w R:
        $has_riemann_integral(f,a,a,v)
        $has_riemann_integral(g,a,a,w)
        forall x '[a,a]:
            f(x)<=g(x)
        =>:
            v<=w
    release thm riemann_integral_compare(f,g,a,a,v,w)
"#,
        true,
    ),
    (
        r#"# Retain the guarded function while establishing every original interval point's domain.
thm riemann_builtin_absolute_bound_guarded:
    ? forall f fn(x R:x>0) R,a,b,v,c R:
        '[min(a,b),max(a,b)] $subset {t R:t>0}
        $has_riemann_integral(f,a,b,v)
        0<=c
        forall x '[min(a,b),max(a,b)]:
            x>0
            =>:
                abs(f(x))<=c
        =>:
            abs(v)<=c*abs(b-a)
    claim:
        ? forall x '[min(a,b),max(a,b)]:
            x>0
        x $in {t R:t>0}
        x>0
    claim:
        ? forall x '[min(a,b),max(a,b)]:
            abs(f(x))<=c
        x>0
        abs(f(x))<=c
    release thm riemann_integral_bound(f,a,b,v,c)
"#,
        false,
    ),
    (
        r#"# The absolute integral bound preserves the absolute width of a reversed interval.
thm riemann_builtin_absolute_bound_reversed:
    ? forall f fn(x R) R,v,c R:
        $has_riemann_integral(f,3,1,v)
        0<=c
        forall x '[min(3,1),max(3,1)]:
            abs(f(x))<=c
        =>:
            abs(v)<=c*abs(1-3)
    release thm riemann_integral_bound(f,3,1,v,c)
"#,
        false,
    ),
    (
        r#"# An equal-endpoint candidate has an absolute bound of zero width.
thm riemann_builtin_absolute_bound_zero_width:
    ? forall f fn(x R) R,a,v,c R:
        $has_riemann_integral(f,a,a,v)
        0<=c
        forall x '[min(a,a),max(a,a)]:
            abs(f(x))<=c
        =>:
            abs(v)<=c*abs(a-a)
    release thm riemann_integral_bound(f,a,a,v,c)
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
    panic!("original ordered-integral invocation")
}

#[test]
fn riemann_order_replays_original_ten_and_seven_stage_schemas() {
    for (s, compare) in [(SOURCES[0], true), (SOURCES[1], false)]
        .into_iter()
        .chain(VARIANTS)
    {
        let (mut run, c) = super::execute(s);
        let p = invocation(&mut run);
        assert_eq!(
            p.builtin.as_ref().unwrap().theorem,
            if compare {
                BuiltinTheoremId::RiemannIntegralCompare
            } else {
                BuiltinTheoremId::RiemannIntegralBound
            }
        );
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), if compare { 10 } else { 7 });
        assert_eq!(p.dom_proofs.len(), p.dom_stores.len());
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "ordered_integrals").unwrap();
        assert!(out.contains(if compare {
            "Litex.riemannIntegralLocalCompare"
        } else {
            "Litex.riemannIntegralAbsoluteBound"
        }));
        assert_eq!(out, c.compile_run(&run, "ordered_integrals").unwrap());
    }
}

#[test]
fn riemann_order_requires_all_original_ordered_proofs_stores_and_goal_formation() {
    for s in SOURCES {
        for change in 0..9 {
            let (mut run, c) = super::execute(s);
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
                c.compile_run(&run, "missing_integral_order_stage").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn riemann_order_keeps_both_positive_candidates_and_each_function_endpoint_value() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for index in if i == 0 { vec![7, 8] } else { vec![3] } {
            for change in 0..5 {
                let (mut run, c) = super::execute(s);
                let b = invocation(&mut run).builtin.as_mut().unwrap();
                let Fact::AtomicFact(f) = &mut b.requirements[index] else {
                    panic!()
                };
                if change == 4 {
                    *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap()
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
                    c.compile_run(&run, "changed_ordered_candidate").is_err(),
                    "{i}/{index}/{change}"
                );
            }
        }
    }
}

#[test]
fn riemann_order_retains_complete_domains_endpoint_order_and_nonnegative_real_bound() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for index in if i == 0 {
            vec![0, 1, 2, 3, 4, 5, 6]
        } else {
            vec![0, 1, 2, 4, 5]
        } {
            let (mut run, c) = super::execute(s);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
                Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                    std::mem::swap(&mut p.left, &mut p.right)
                }
                Fact::AtomicFact(AtomicFact::LessEqualFact(p)) => {
                    std::mem::swap(&mut p.left, &mut p.right)
                }
                _ => panic!(),
            }
            assert!(
                c.compile_run(&run, "changed_ordered_context").is_err(),
                "{i}/{index}"
            );
        }
    }
}

#[test]
fn riemann_order_keeps_original_local_comparison_binder_functions_and_polarity() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for change in 0..8 {
            let (mut run, c) = super::execute(s);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let guard = b.requirements[0].clone();
            let Obj::Identifier(IdentifierObj::Plain { id: captured, .. }) = &b.arguments[0] else {
                panic!()
            };
            let captured = *captured;
            let Fact::ForallFact(p) = b.requirements.last_mut().unwrap() else {
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
                        *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap()
                    } else {
                        let AtomicFact::LessEqualFact(eq) = f else {
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
                c.compile_run(&run, "changed_local_order").is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn riemann_order_preserves_goal_orientation_absolute_candidate_and_width() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for change in 0..4 {
            let (mut run, c) = super::execute(s);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(f) = &mut b.conclusions[0] else {
                panic!()
            };
            if change == 3 {
                *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap()
            } else {
                let AtomicFact::LessEqualFact(p) = f else {
                    panic!()
                };
                match change {
                    0 => std::mem::swap(&mut p.left, &mut p.right),
                    1 => p.left = super::number_object("99"),
                    _ => p.right = super::number_object("99"),
                }
            }
            assert!(
                c.compile_run(&run, "changed_ordered_goal").is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn riemann_order_requires_original_candidate_function_formation() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for index in if i == 0 { vec![1, 2] } else { vec![0] } {
            for change in 0..4 {
                let (mut run, c) = super::execute(s);
                let FactWellDefinedProof::AtomicExceptEquality(wd) =
                    &mut body(&mut run).assumed_dom_facts[index].well_defined
                else {
                    panic!()
                };
                let d = wd.as_detailed_mut().unwrap();
                if change == 3 {
                    d.well_defined_of_each_parameter.pop();
                } else {
                    let PredicateDomainProof::FunctionAnalysis(p) = &mut d.predicate_domain else {
                        panic!()
                    };
                    match change {
                        0 => {
                            p.requirements.pop();
                        }
                        1 => p.requirements.swap(0, 1),
                        _ => p.function_domain.domain = Obj::StandardSet(StandardSet::C),
                    }
                }
                assert!(
                    c.compile_run(&run, "changed_ordered_formation").is_err(),
                    "{i}/{index}/{change}"
                );
            }
        }
    }
}

#[test]
fn riemann_order_rejects_future_candidate_and_local_comparison_citations() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for index in if i == 0 { vec![7, 8, 9] } else { vec![3, 6] } {
            let (mut run, c) = super::execute(s);
            let p = invocation(&mut run);
            let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
            if index == if i == 0 { 9 } else { 6 } {
                let VerifyFactResult::ForallFact(proof) = &mut p.dom_proofs[index] else {
                    panic!()
                };
                let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(
                    proof,
                )) = proof.as_mut()
                else {
                    panic!()
                };
                proof.cite_fact_id = future;
            } else {
                let proof = super::atomic_proof_mut(&mut p.dom_proofs[index]);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut proof.searched_proof
                else {
                    panic!()
                };
                cite.cite_fact_id = future;
            }
            assert!(
                c.compile_run(&run, "future_ordered_fact").is_err(),
                "{i}/{index}"
            );
        }
    }
}

#[test]
fn riemann_order_source_requires_the_actual_candidates_and_local_comparison() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for equation in [false, true] {
            let source = if equation {
                if i == 0 {
                    s.replace("        forall x '[a,b]:\n            f(x)<=g(x)\n", "")
                } else {
                    s.replace(
                        "        forall x '[min(a,b),max(a,b)]:\n            abs(f(x))<=c\n",
                        "",
                    )
                }
            } else {
                s.replace("        $has_riemann_integral(f,a,b,v)\n", "")
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
                .compile_run(&run, "missing_integral_order_evidence")
                .is_err());
        }
    }
}
