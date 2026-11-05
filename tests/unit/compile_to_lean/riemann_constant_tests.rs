use super::antiderivative_tests::body;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SOURCES: [&str; 4] = [
    r#"# Integrate the supplied function from its constant values on the integration interval.
thm riemann_builtin_constant:
    ? forall f fn(x R) R,a,b,c R:
        forall x '[min(a,b),max(a,b)]:
            f(x)=c
        =>:
            $has_riemann_integral(f,a,b,c*(b-a))
    release thm riemann_integral_constant(f,a,b,c)
"#,
    r#"# Establish each domain guard before using constancy only on the integration interval.
thm riemann_builtin_constant_guarded:
    ? forall f fn(x R:x>0) R,a,b,c R:
        '[min(a,b),max(a,b)] $subset {t R:t>0}
        forall x '[min(a,b),max(a,b)]:
            x>0
            =>:
                f(x)=c
        =>:
            $has_riemann_integral(f,a,b,c*(b-a))
    claim:
        ? forall x '[min(a,b),max(a,b)]:
            x>0
        x $in {t R:t>0}
        x>0
    claim:
        ? forall x '[min(a,b),max(a,b)]:
            f(x)=c
        x>0
        f(x)=c
    release thm riemann_integral_constant(f,a,b,c)
"#,
    r#"# A reversed constant-function integral keeps its signed endpoint difference.
thm riemann_builtin_constant_reversed:
    ? forall f fn(x R) R,c R:
        forall x '[min(3,1),max(3,1)]:
            f(x)=c
        =>:
            $has_riemann_integral(f,3,1,c*(1-3))
    release thm riemann_integral_constant(f,3,1,c)
"#,
    r#"# The original one-point constant-value equation also covers equal endpoints.
thm riemann_builtin_constant_zero_width:
    ? forall f fn(x R) R,a,c R:
        forall x '[min(a,a),max(a,a)]:
            f(x)=c
        =>:
            $has_riemann_integral(f,a,a,c*(a-a))
    release thm riemann_integral_constant(f,a,a,c)
"#,
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
    panic!("original constant-integral invocation")
}

#[test]
fn riemann_constant_replays_original_five_stage_interval_local_schemas() {
    for source in SOURCES {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(
            p.builtin.as_ref().unwrap().theorem,
            BuiltinTheoremId::RiemannIntegralConstant
        );
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), 5);
        assert_eq!(p.dom_stores.len(), 5);
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "constant_integral").unwrap();
        assert!(out.contains("Litex.riemannIntegralConstantCandidate"));
        assert_eq!(out, c.compile_run(&run, "constant_integral").unwrap());
    }
}

#[test]
fn riemann_constant_requires_each_original_ordered_pipeline_stage() {
    for change in 0..10 {
        let (mut run, c) = super::execute(SOURCES[0]);
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
            8 => p.builtin.as_mut().unwrap().conclusions.clear(),
            _ => p.builtin.as_mut().unwrap().theorem = BuiltinTheoremId::RiemannIntegralPower,
        }
        assert!(
            c.compile_run(&run, "missing_constant_stage").is_err(),
            "{change}"
        );
    }
}

#[test]
fn riemann_constant_preserves_original_endpoint_domain_and_constant_realness() {
    for index in 0..4 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        match &mut b.requirements[index] {
            Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
            Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                std::mem::swap(&mut p.left, &mut p.right)
            }
            _ => panic!(),
        }
        assert!(
            c.compile_run(&run, "changed_constant_domain").is_err(),
            "{index}"
        );
    }
}

#[test]
fn riemann_constant_keeps_exact_positive_goal_function_endpoints_and_area_order() {
    for change in 0..8 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(f) = &mut b.conclusions[0] else {
            panic!()
        };
        if change == 7 {
            *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap();
        } else {
            let AtomicFact::HasRiemannIntegralFact(p) = f else {
                panic!()
            };
            match change {
                0 => p.function = super::number_object("99"),
                1 => p.lower = super::number_object("99"),
                2 => p.upper = super::number_object("99"),
                _ => {
                    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) = &mut p.value else {
                        panic!()
                    };
                    match change {
                        3 => std::mem::swap(&mut m.left, &mut m.right),
                        4 => m.left = Box::new(super::number_object("99")),
                        _ => {
                            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) =
                                m.right.as_mut()
                            else {
                                panic!()
                            };
                            if change == 5 {
                                std::mem::swap(&mut s.left, &mut s.right)
                            } else {
                                s.right = Box::new(super::number_object("99"))
                            }
                        }
                    }
                }
            }
        }
        assert!(
            c.compile_run(&run, "changed_constant_area").is_err(),
            "{change}"
        );
    }
}

#[test]
fn riemann_constant_keeps_fresh_interval_equation_binder_and_original_subjects() {
    for change in 0..8 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let guard = b.requirements[0].clone();
        let Obj::Identifier(IdentifierObj::Plain { id: captured, .. }) = &b.arguments[0] else {
            panic!()
        };
        let captured = *captured;
        let Fact::ForallFact(p) = &mut b.requirements[4] else {
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
            c.compile_run(&run, "changed_constant_equation").is_err(),
            "{change}"
        );
    }
}

#[test]
fn riemann_constant_requires_original_goal_formation_and_complete_domain_capture() {
    for change in 0..5 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut invocation(&mut run).conclusions_wd[0]
        else {
            panic!()
        };
        let d = wd.as_detailed_mut().unwrap();
        if change == 4 {
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
                2 => p.function_domain.domain = Obj::StandardSet(StandardSet::C),
                _ => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(q)) =
                        &mut p.requirements[2].requirement
                    else {
                        panic!()
                    };
                    q.right = Obj::StandardSet(StandardSet::C);
                }
            }
        }
        assert!(
            c.compile_run(&run, "changed_constant_formation").is_err(),
            "{change}"
        );
    }
}

#[test]
fn riemann_constant_rejects_future_constant_and_interval_equation_citations() {
    for index in [3, 4] {
        let (mut run, c) = super::execute(SOURCES[0]);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        if index == 3 {
            let proof = super::atomic_proof_mut(&mut p.dom_proofs[index]);
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut proof.searched_proof
            else {
                panic!()
            };
            cite.cite_fact_id = future;
        } else {
            let VerifyFactResult::ForallFact(proof) = &mut p.dom_proofs[index] else {
                panic!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
                proof.as_mut()
            else {
                panic!()
            };
            proof.cite_fact_id = future;
        }
        assert!(
            c.compile_run(&run, "future_constant_evidence").is_err(),
            "{index}"
        );
    }
}

#[test]
fn riemann_constant_source_requires_the_actual_interval_equation() {
    let source = SOURCES[0].replace(
        "        forall x '[min(a,b),max(a,b)]:\n            f(x)=c\n",
        "",
    );
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    let run = runtime.run_litex_code(&source).unwrap();
    assert!(!run.success);
    assert!(super::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "unproved_constant_equation")
        .is_err());
}
