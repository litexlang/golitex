use super::antiderivative_tests::body;
use crate::execute::execute_by_stmt::{
    ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;
const SOURCES: [&str; 6] = [
    r#"# Compose the supplied primitive and inner function using their recorded derivatives.
thm antiderivative_builtin_compose:
    ? forall F,f,g,dg,H,h fn(x R) R:
        $is_antiderivative_on(F,f,R)
        forall x R:
            $has_derivative_at(g,x,dg(x))
        forall x R:
            H(x)=F(g(x))
            h(x)=f(g(x))*dg(x)
        =>:
            $is_antiderivative_on(H,h,R)
    release thm antiderivative_compose(F,f,g,dg,H,h,R,R)
"#,
    r#"# Retain both distinct open regions and the complete image condition of the inner function.
thm antiderivative_builtin_compose_intervals:
    ? forall F,f,g,dg,H,h fn(x R) R,a,b,c,d R:
        a<b
        c<d
        $is_antiderivative_on(F,f,'(c,d))
        forall x '(a,b):
            g(x) $in '(c,d)
        forall x '(a,b):
            $has_derivative_at(g,x,dg(x))
        forall x '(a,b):
            H(x)=F(g(x))
            h(x)=f(g(x))*dg(x)
        =>:
            $is_antiderivative_on(H,h,'(a,b))
    release thm antiderivative_compose(F,f,g,dg,H,h,'(a,b),'(c,d))
"#,
    r#"# Preserve the guarded inner function's original domain on the open source interval.
claim:
    ? forall chain_positive_probe '(1,2):
        chain_positive_probe $in R+
    chain_positive_probe>1
    chain_positive_probe>0
'(1,2) $subset R+
claim:
    ? forall chain_guard_probe '(1,2):
        chain_guard_probe $in {z R+:z>1}
    chain_guard_probe>1
    chain_guard_probe $in R+
    chain_guard_probe $in {z R+:z>1}
'(1,2) $subset {z R+:z>1}
{z R+:z>1} $subset R
thm antiderivative_builtin_compose_guarded:
    ? forall F,f,dg fn(x R) R,g fn(x R+:x>1) R,H,h fn(x R+) R:
        $is_antiderivative_on(F,f,R)
        forall x '(1,2):
            $has_derivative_at(g,x,dg(x))
        forall x '(1,2):
            H(x)=F(g(x))
            h(x)=f(g(x))*dg(x)
        =>:
            $is_antiderivative_on(H,h,'(1,2))
    release thm antiderivative_compose(F,f,g,dg,H,h,'(1,2),R)
"#,
    r#"# Two supplied primitives with the same derivative differ by their difference at the original base point.
thm antiderivative_builtin_difference_constant:
    ? forall F,G,f fn(x R) R,a,b,c R,x '(a,b):
        a<b
        c $in '(a,b)
        $is_antiderivative_on(F,f,'(a,b))
        $is_antiderivative_on(G,f,'(a,b))
        =>:
            F(x)-G(x)=F(c)-G(c)
    release thm antiderivative_difference_constant(F,G,f,a,b,c)
"#,
    r#"# The constant is evaluated at the supplied interior rational point, not a replacement point.
thm antiderivative_builtin_difference_constant_fractional_base:
    ? forall F,G,f fn(x R) R,x '(1,2):
        $is_antiderivative_on(F,f,'(1,2))
        $is_antiderivative_on(G,f,'(1,2))
        =>:
            F(x)-G(x)=F(3/2)-G(3/2)
    release thm antiderivative_difference_constant(F,G,f,1,2,3/2)
"#,
    r#"# Keep the independent complete domains of the two primitives on the original open interval.
claim:
    ? forall difference_positive_probe '(1,2):
        difference_positive_probe $in R+
    difference_positive_probe>1
    difference_positive_probe>0
'(1,2) $subset R+
claim:
    ? forall difference_guard_probe '(1,2):
        difference_guard_probe $in {z R+:z>1}
    difference_guard_probe>1
    difference_guard_probe $in R+
    difference_guard_probe $in {z R+:z>1}
'(1,2) $subset {z R+:z>1}
{z R+:z>1} $subset R
thm antiderivative_builtin_difference_constant_guarded:
    ? forall F fn(x R+:x>1) R,G fn(x R+) R,f fn(x R) R,x '(1,2):
        $is_antiderivative_on(F,f,'(1,2))
        $is_antiderivative_on(G,f,'(1,2))
        =>:
            F(x)-G(x)=F(3/2)-G(3/2)
    release thm antiderivative_difference_constant(F,G,f,1,2,3/2)
"#,
];
fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body(run).proof_steps[0]
    else {
        panic!()
    };
    p
}
#[test]
fn antiderivative_calculus_replays_original_real_interval_guarded_and_basepoint_schemas() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        let (mut run, c) = super::execute(s);
        let p = invocation(&mut run);
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), [31, 40, 37, 28, 28, 28][i]);
        assert_eq!(p.dom_proofs.len(), p.dom_stores.len());
        let out = c.compile_run(&run, "antiderivative_calculus").unwrap();
        assert!(out.contains(if i < 3 {
            "Litex.antiderivativeComposeFunctions"
        } else {
            "Litex.antiderivativeDifferenceConstantInterval"
        }));
        assert_eq!(out, c.compile_run(&run, "antiderivative_calculus").unwrap());
    }
}
#[test]
fn antiderivative_calculus_requires_all_original_ordered_pipeline_stages() {
    for s in [SOURCES[0], SOURCES[3]] {
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
                c.compile_run(&run, "changed_calculus_stage").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn antiderivative_calculus_keeps_original_positive_primitive_candidates() {
    for (s, indices) in [(SOURCES[0], vec![27]), (SOURCES[3], vec![26, 27])] {
        for index in indices {
            for change in 0..4 {
                let (mut run, c) = super::execute(s);
                let b = invocation(&mut run).builtin.as_mut().unwrap();
                let Fact::AtomicFact(f) = &mut b.requirements[index] else {
                    panic!()
                };
                if change == 3 {
                    *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap()
                } else {
                    let AtomicFact::NormalAtomicFact(p) = f else {
                        panic!()
                    };
                    p.body[change] = super::number_object("99");
                }
                assert!(
                    c.compile_run(&run, "changed_calculus_candidate").is_err(),
                    "{index}/{change}"
                );
            }
        }
    }
}
#[test]
fn antiderivative_calculus_preserves_full_image_derivative_and_equation_order() {
    for index in [28, 29, 30] {
        for change in 0..5 {
            let (mut run, c) = super::execute(SOURCES[0]);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let guard = b.requirements[0].clone();
            let Fact::ForallFact(p) = &mut b.requirements[index] else {
                panic!()
            };
            match change {
                0 => {
                    p.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C))
                }
                1 => p.dom_facts.push(guard),
                2 => p.then_facts.clear(),
                3 => {
                    if index == 30 {
                        p.then_facts.swap(0, 1)
                    } else {
                        let ExistOrAndChainAtomicFact::AtomicFact(f) = &mut p.then_facts[0] else {
                            panic!()
                        };
                        *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap();
                    }
                }
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(f) = &mut p.then_facts[0] else {
                        panic!()
                    };
                    match f {
                        AtomicFact::InFact(p) => p.set = Obj::StandardSet(StandardSet::C),
                        AtomicFact::HasDerivativeAtFact(p) => p.value = super::number_object("99"),
                        AtomicFact::EqualFact(p) => std::mem::swap(&mut p.left, &mut p.right),
                        _ => panic!(),
                    }
                }
            }
            assert!(
                c.compile_run(&run, "changed_chain_clause").is_err(),
                "{index}/{change}"
            );
        }
    }
}
#[test]
fn antiderivative_difference_keeps_original_order_basepoint_and_fresh_equation() {
    for change in 0..7 {
        let (mut run, c) = super::execute(SOURCES[3]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        match change {
            0 => {
                let Fact::AtomicFact(AtomicFact::LessFact(p)) = &mut b.requirements[0] else {
                    panic!()
                };
                std::mem::swap(&mut p.left, &mut p.right)
            }
            1 => {
                let Fact::AtomicFact(AtomicFact::InFact(p)) = &mut b.requirements[1] else {
                    panic!()
                };
                p.element = super::number_object("99")
            }
            _ => {
                let Fact::ForallFact(p) = &mut b.conclusions[0] else {
                    panic!()
                };
                match change {
                    2 => {
                        p.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::C))
                    }
                    3 => p.then_facts.clear(),
                    _ => {
                        let ExistOrAndChainAtomicFact::AtomicFact(f) = &mut p.then_facts[0] else {
                            panic!()
                        };
                        if change == 6 {
                            *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap()
                        } else {
                            let AtomicFact::EqualFact(p) = f else {
                                panic!()
                            };
                            if change == 4 {
                                std::mem::swap(&mut p.left, &mut p.right)
                            } else {
                                p.right = super::number_object("99")
                            }
                        }
                    }
                }
            }
        }
        assert!(
            c.compile_run(&run, "changed_difference_basepoint").is_err(),
            "{change}"
        );
    }
}
#[test]
fn antiderivative_calculus_retains_all_original_complete_contexts() {
    for (s, indices) in [
        (SOURCES[0], vec![0, 1, 4, 5, 9, 10, 13, 14, 18, 19, 22, 23]),
        (SOURCES[3], vec![2, 3, 4, 5, 6, 7, 14, 15, 16, 17, 18, 19]),
    ] {
        for index in indices {
            let (mut run, c) = super::execute(s);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
                Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                    p.right = Obj::StandardSet(StandardSet::C)
                }
                Fact::AtomicFact(AtomicFact::LessFact(p)) => {
                    std::mem::swap(&mut p.left, &mut p.right)
                }
                _ => panic!(),
            }
            assert!(
                c.compile_run(&run, "changed_calculus_context").is_err(),
                "{index}"
            );
        }
    }
}
#[test]
fn antiderivative_calculus_rejects_future_primitive_citations() {
    for (s, index) in [(SOURCES[0], 27), (SOURCES[3], 26), (SOURCES[3], 27)] {
        let (mut run, c) = super::execute(s);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let proof = super::atomic_proof_mut(&mut p.dom_proofs[index]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
            &mut proof.searched_proof
        else {
            panic!()
        };
        cite.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_calculus_candidate").is_err());
    }
}
#[test]
fn antiderivative_calculus_source_requires_the_recorded_primitive() {
    for (s, line) in [
        (SOURCES[0], "        $is_antiderivative_on(F,f,R)\n"),
        (SOURCES[3], "        $is_antiderivative_on(F,f,'(a,b))\n"),
    ] {
        let source = s.replace(line, "");
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(&source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "missing_calculus_primitive")
            .is_err());
    }
}
