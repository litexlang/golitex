use super::antiderivative_tests::{body, invocation};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::prelude::*;

const SOURCES: [&str; 3] = [
    r#"# Shift the primitive while retaining the original derivative function.
thm antiderivative_builtin_shift:
    ? forall F,f,H fn(x R) R,c R:
        $is_antiderivative_on(F,f,R)
        forall x R:
            H(x)=F(x)+c
        =>:
            $is_antiderivative_on(H,f,R)
    release thm antiderivative_shift(F,f,H,R,c)
"#,
    r#"# Add two supplied primitives and their supplied derivative functions.
thm antiderivative_builtin_add:
    ? forall F,f,G,g,H,h fn(x R) R:
        $is_antiderivative_on(F,f,R)
        $is_antiderivative_on(G,g,R)
        forall x R:
            H(x)=F(x)+G(x)
            h(x)=f(x)+g(x)
        =>:
            $is_antiderivative_on(H,h,R)
    release thm antiderivative_add(F,f,G,g,H,h,R)
"#,
    r#"# Scale the supplied primitive and derivative by an arbitrary real scalar.
thm antiderivative_builtin_scale:
    ? forall F,f,H,h fn(x R) R,c R:
        $is_antiderivative_on(F,f,R)
        forall x R:
            H(x)=c*F(x)
            h(x)=c*f(x)
        =>:
            $is_antiderivative_on(H,h,R)
    release thm antiderivative_scale(F,f,H,h,R,c)
"#,
];
const VARIANTS: [&str; 9] = [
    r#"# Shift a primitive using equality only inside an arbitrary open interval.
thm antiderivative_builtin_shift_generic:
    ? forall a,b,c R,F,f,H fn(x R) R:
        a<b
        $is_antiderivative_on(F,f,'(a,b))
        forall x '(a,b):
            H(x)=F(x)+c
        =>:
            $is_antiderivative_on(H,f,'(a,b))
    release thm antiderivative_shift(F,f,H,'(a,b),c)
"#,
    r#"# Add supplied primitives with equality restricted to an arbitrary open interval.
thm antiderivative_builtin_add_generic:
    ? forall a,b R,F,f,G,g,H,h fn(x R) R:
        a<b
        $is_antiderivative_on(F,f,'(a,b))
        $is_antiderivative_on(G,g,'(a,b))
        forall x '(a,b):
            H(x)=F(x)+G(x)
            h(x)=f(x)+g(x)
        =>:
            $is_antiderivative_on(H,h,'(a,b))
    release thm antiderivative_add(F,f,G,g,H,h,'(a,b))
"#,
    r#"# Scale supplied functions using equality only on an arbitrary open interval.
thm antiderivative_builtin_scale_generic:
    ? forall a,b,c R,F,f,H,h fn(x R) R:
        a<b
        $is_antiderivative_on(F,f,'(a,b))
        forall x '(a,b):
            H(x)=c*F(x)
            h(x)=c*f(x)
        =>:
            $is_antiderivative_on(H,h,'(a,b))
    release thm antiderivative_scale(F,f,H,h,'(a,b),c)
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Shift a primitive with a positive domain into a supplied full-real-domain function.
thm antiderivative_builtin_shift_independent_domains:
    ? forall F fn(x R+) R,f,H fn(x R) R,c R:
        $is_antiderivative_on(F,f,'(1,2))
        forall x '(1,2):
            H(x)=F(x)+c
        =>:
            $is_antiderivative_on(H,f,'(1,2))
    release thm antiderivative_shift(F,f,H,'(1,2),c)
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Add primitives while retaining three independent positive input domains.
thm antiderivative_builtin_add_independent_domains:
    ? forall F,g,h fn(x R) R,f,G,H fn(x R+) R:
        $is_antiderivative_on(F,f,'(1,2))
        $is_antiderivative_on(G,g,'(1,2))
        forall x '(1,2):
            H(x)=F(x)+G(x)
            h(x)=f(x)+g(x)
        =>:
            $is_antiderivative_on(H,h,'(1,2))
    release thm antiderivative_add(F,f,G,g,H,h,'(1,2))
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Scale a positive-domain primitive while keeping the result and coefficient domains independent.
thm antiderivative_builtin_scale_independent_domains:
    ? forall F,h fn(x R+) R,f,H fn(x R) R,c R:
        $is_antiderivative_on(F,f,'(1,2))
        forall x '(1,2):
            H(x)=c*F(x)
            h(x)=c*f(x)
        =>:
            $is_antiderivative_on(H,h,'(1,2))
    release thm antiderivative_scale(F,f,H,h,'(1,2),c)
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Establish the original guarded input domain and its interval coverage.
claim:
    ? forall anti_guard_probe '(1,2):
        anti_guard_probe $in {z R+: z>1}
    anti_guard_probe>1
    anti_guard_probe $in R+
    anti_guard_probe $in {z R+: z>1}
'(1,2) $subset {z R+: z>1}
{z R+: z>1} $subset R

# Shift into a supplied function with a strictly guarded positive domain.
thm antiderivative_builtin_shift_guarded:
    ? forall F,f fn(x R) R,H fn(x R+: x>1) R,c R:
        $is_antiderivative_on(F,f,'(1,2))
        forall x '(1,2):
            H(x)=F(x)+c
        =>:
            $is_antiderivative_on(H,f,'(1,2))
    release thm antiderivative_shift(F,f,H,'(1,2),c)
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Establish the original guarded input domain and its interval coverage.
claim:
    ? forall anti_guard_probe '(1,2):
        anti_guard_probe $in {z R+: z>1}
    anti_guard_probe>1
    anti_guard_probe $in R+
    anti_guard_probe $in {z R+: z>1}
'(1,2) $subset {z R+: z>1}
{z R+: z>1} $subset R

# Add a guarded primitive without equating its domain with the other functions.
thm antiderivative_builtin_add_guarded:
    ? forall F,f,g,h fn(x R) R,G fn(x R+: x>1) R,H fn(x R+) R:
        $is_antiderivative_on(F,f,'(1,2))
        $is_antiderivative_on(G,g,'(1,2))
        forall x '(1,2):
            H(x)=F(x)+G(x)
            h(x)=f(x)+g(x)
        =>:
            $is_antiderivative_on(H,h,'(1,2))
    release thm antiderivative_add(F,f,G,g,H,h,'(1,2))
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Establish the original guarded input domain and its interval coverage.
claim:
    ? forall anti_guard_probe '(1,2):
        anti_guard_probe $in {z R+: z>1}
    anti_guard_probe>1
    anti_guard_probe $in R+
    anti_guard_probe $in {z R+: z>1}
'(1,2) $subset {z R+: z>1}
{z R+: z>1} $subset R

# Scale a guarded primitive using equations only on the smaller open interval.
thm antiderivative_builtin_scale_guarded:
    ? forall F fn(x R+: x>1) R,f,H fn(x R) R,h fn(x R+) R,c R:
        $is_antiderivative_on(F,f,'(1,2))
        forall x '(1,2):
            H(x)=c*F(x)
            h(x)=c*f(x)
        =>:
            $is_antiderivative_on(H,h,'(1,2))
    release thm antiderivative_scale(F,f,H,h,'(1,2),c)
"#,
];

#[test]
fn antiderivative_algebra_replays_original_functions_and_ordered_schemas() {
    for (i, source) in SOURCES.into_iter().chain(VARIANTS).enumerate() {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(
            p.builtin.as_ref().unwrap().theorem,
            [
                BuiltinTheoremId::AntiderivativeShift,
                BuiltinTheoremId::AntiderivativeAdd,
                BuiltinTheoremId::AntiderivativeScale,
            ][i % 3]
        );
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), if i < 3 { 12 } else { 15 });
        assert_eq!(p.dom_stores.len(), p.dom_proofs.len());
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "antiderivative_algebra").unwrap();
        assert!(out.contains(
            [
                "Litex.antiderivativeShiftFunction",
                "Litex.antiderivativeAddFunctions",
                "Litex.antiderivativeScaleFunctions"
            ][i % 3]
        ));
        assert_eq!(out, c.compile_run(&run, "antiderivative_algebra").unwrap());
        if i >= 3 {
            assert!(out.contains("Litex.realOpenIntervalRegionInterior"));
        }
        if i >= 6 {
            assert!(out.contains("Litex.positiveRealPredicate"));
        }
    }
}

#[test]
fn antiderivative_algebra_requires_every_original_pipeline_stage() {
    for source in SOURCES.into_iter().chain(VARIANTS[..3].iter().copied()) {
        for change in 0..12 {
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
                8 => p.builtin.as_mut().unwrap().conclusions.clear(),
                9 => p.builtin.as_mut().unwrap().theorem = BuiltinTheoremId::AntiderivativeRestrict,
                10 => {
                    let n = p.dom_proofs.len();
                    p.dom_proofs.swap(n - 1, n - 2);
                }
                _ => {
                    let n = p.dom_stores.len();
                    p.dom_stores.swap(n - 1, n - 2);
                }
            }
            assert!(
                c.compile_run(&run, "changed_antiderivative_algebra_stage")
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn antiderivative_algebra_preserves_positive_source_second_and_target_candidates() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for slot in if i == 1 {
            vec![9, 10, usize::MAX]
        } else {
            vec![9, usize::MAX]
        } {
            for change in 0..4 {
                let (mut run, c) = super::execute(source);
                let b = invocation(&mut run).builtin.as_mut().unwrap();
                let fact = if slot == usize::MAX {
                    &mut b.conclusions[0]
                } else {
                    &mut b.requirements[slot]
                };
                let Fact::AtomicFact(f) = fact else { panic!() };
                if change == 3 {
                    *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap();
                } else {
                    let AtomicFact::NormalAtomicFact(p) = f else {
                        panic!()
                    };
                    p.body[change] = super::number_object("99");
                }
                assert!(
                    c.compile_run(&run, "changed_antiderivative_algebra_candidate")
                        .is_err(),
                    "{i}/{slot}/{change}"
                );
            }
        }
    }
}

#[test]
fn antiderivative_algebra_preserves_real_scalar_and_its_original_position() {
    for source in [SOURCES[0], SOURCES[2]] {
        for change in 0..3 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            if change == 2 {
                b.requirements.swap(9, 10);
            } else {
                let Fact::AtomicFact(AtomicFact::InFact(p)) = &mut b.requirements[10] else {
                    panic!()
                };
                if change == 0 {
                    p.element = super::number_object("99");
                } else {
                    p.set = Obj::StandardSet(StandardSet::C);
                }
            }
            assert!(
                c.compile_run(&run, "changed_antiderivative_scalar")
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn antiderivative_algebra_preserves_exact_pointwise_binder_region_and_equation_order() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in 0..9 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let guard = b.requirements[0].clone();
            let Obj::Identifier(IdentifierObj::Plain { id: captured, .. }) = &b.arguments[0] else {
                panic!()
            };
            let captured = *captured;
            let Fact::ForallFact(p) = &mut b.requirements[11] else {
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
                4 if i > 0 => p.then_facts.swap(0, 1),
                4 => p.then_facts.push(p.then_facts[0].clone()),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut p.then_facts[0]
                    else {
                        panic!()
                    };
                    match change {
                        5 => std::mem::swap(&mut eq.left, &mut eq.right),
                        6 => eq.left = super::number_object("99"),
                        7 => eq.right = super::number_object("99"),
                        _ => match &mut eq.right {
                            Obj::ArithmeticOperator(ArithmeticOperator::Add(op)) => {
                                std::mem::swap(&mut op.left, &mut op.right)
                            }
                            Obj::ArithmeticOperator(ArithmeticOperator::Mul(op)) => {
                                std::mem::swap(&mut op.left, &mut op.right)
                            }
                            _ => panic!(),
                        },
                    }
                }
            }
            assert!(
                c.compile_run(&run, "changed_antiderivative_pointwise")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn antiderivative_algebra_requires_original_complete_context_and_interval_stages() {
    for (i, source) in SOURCES
        .into_iter()
        .chain(VARIANTS[..3].iter().copied())
        .enumerate()
    {
        for index in 0..if i < 3 { 9 } else { 12 } {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
                Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                    p.right = Obj::StandardSet(StandardSet::C)
                }
                Fact::AtomicFact(AtomicFact::LessFact(p)) => {
                    std::mem::swap(&mut p.left, &mut p.right)
                }
                _ => panic!("{index}"),
            }
            assert!(
                c.compile_run(&run, "changed_antiderivative_original_context")
                    .is_err(),
                "{i}/{index}"
            );
        }
    }
}

#[test]
fn antiderivative_algebra_rejects_future_pointwise_and_second_candidate_citations() {
    for source in SOURCES {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let VerifyFactResult::ForallFact(proof) = &mut p.dom_proofs[11] else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
            proof.as_mut()
        else {
            panic!()
        };
        proof.cite_fact_id = future;
        assert!(c
            .compile_run(&run, "future_antiderivative_formula")
            .is_err());
    }
    let (mut run, c) = super::execute(SOURCES[1]);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let proof = super::atomic_proof_mut(&mut p.dom_proofs[10]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut proof.searched_proof
    else {
        panic!()
    };
    cite.cite_fact_id = future;
    assert!(c.compile_run(&run, "future_antiderivative_second").is_err());
}

#[test]
fn antiderivative_algebra_rejects_missing_original_formation_in_second_and_target() {
    for target in [false, true] {
        for change in 0..5 {
            let (mut run, c) = super::execute(SOURCES[1]);
            let wd = if target {
                let FactWellDefinedProof::AtomicExceptEquality(wd) =
                    &mut invocation(&mut run).conclusions_wd[0]
                else {
                    panic!()
                };
                wd
            } else {
                let FactWellDefinedProof::AtomicExceptEquality(wd) =
                    &mut body(&mut run).assumed_dom_facts[1].well_defined
                else {
                    panic!()
                };
                wd
            };
            let PredicateDomainProof::ByRequirements(req) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("original formation")
            };
            let offset = req.len() - 8;
            match change {
                0 => {
                    req.pop();
                }
                1 => req.swap(offset, offset + 4),
                2 => {
                    let Fact::AtomicFact(AtomicFact::InFact(p)) = &mut req[offset].requirement
                    else {
                        panic!()
                    };
                    p.element = super::number_object("99");
                }
                3 => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(p)) =
                        &mut req[offset + 3].requirement
                    else {
                        panic!()
                    };
                    p.right = Obj::StandardSet(StandardSet::C);
                }
                _ => {
                    wd.as_detailed_mut()
                        .unwrap()
                        .well_defined_of_each_parameter
                        .pop();
                }
            }
            assert!(
                c.compile_run(&run, "changed_antiderivative_formation")
                    .is_err(),
                "{target}/{change}"
            );
        }
    }
}

#[test]
fn antiderivative_algebra_source_requires_actual_candidates_and_pointwise_equations() {
    for (i, original) in SOURCES.into_iter().enumerate() {
        for remove in 0..if i == 1 { 3 } else { 2 } {
            let source = if remove == 0 {
                original.replace("        $is_antiderivative_on(F,f,R)\n", "")
            } else if remove == 2 {
                original.replace("        $is_antiderivative_on(G,g,R)\n", "")
            } else {
                let start = original.find("        forall x R:\n").unwrap();
                let end = original[start..].find("        =>:\n").unwrap() + start;
                format!("{}{}", &original[..start], &original[end..])
            };
            let command =
                parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
            let mut runtime = Runtime::new_with_result_detail(
                command,
                crate::result_detail::OutputDetail::Detailed,
            );
            let run = runtime.run_litex_code(&source).unwrap();
            assert!(!run.success, "{i}/{remove}");
            assert!(super::LitexToLeanCompiler::new(runtime)
                .compile_run(&run, "unproved_antiderivative_algebra")
                .is_err());
        }
    }
}

#[test]
fn antiderivative_algebra_second_formation_cannot_borrow_a_future_predicate() {
    let (mut run, c) = super::execute(SOURCES[1]);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let proof = super::atomic_proof_mut(&mut p.dom_proofs[10]);
    let PredicateDomainProof::ByKnownFact(cite) = &mut proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .predicate_domain
    else {
        panic!("original scoped predicate formation citation")
    };
    cite.cite_fact_id = future;
    assert!(c
        .compile_run(&run, "future_antiderivative_formation")
        .is_err());
}
