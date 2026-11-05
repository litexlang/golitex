use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

const SOURCES: [&str; 4] = [
    r#"# Differentiate a pointwise sum of real multivariable functions in one coordinate.
thm partial_builtin_algebra_add:
    ? forall f,g,h fn(x cart_n(R,2)) R,p cart_n(R,2),a,b R:
        $has_partial_derivative_at(f,p,2,1,a)
        $has_partial_derivative_at(g,p,2,1,b)
        forall q cart_n(R,2):
            h(q)=f(q)+g(q)
        =>:
            $has_partial_derivative_at(h,p,2,1,a+b)
    release thm partial_at_add(f,g,h,p,2,1,a,b)
"#,
    r#"# Differentiate a pointwise difference of real multivariable functions in one coordinate.
thm partial_builtin_algebra_subtract:
    ? forall f,g,h fn(x cart_n(R,2)) R,p cart_n(R,2),a,b R:
        $has_partial_derivative_at(f,p,2,1,a)
        $has_partial_derivative_at(g,p,2,1,b)
        forall q cart_n(R,2):
            h(q)=f(q)-g(q)
        =>:
            $has_partial_derivative_at(h,p,2,1,a-b)
    release thm partial_at_subtract(f,g,h,p,2,1,a,b)
"#,
    r#"# Apply the product rule to a pointwise product of real multivariable functions.
thm partial_builtin_algebra_multiply:
    ? forall f,g,h fn(x cart_n(R,2)) R,p cart_n(R,2),a,b R:
        $has_partial_derivative_at(f,p,2,1,a)
        $has_partial_derivative_at(g,p,2,1,b)
        forall q cart_n(R,2):
            h(q)=f(q)*g(q)
        =>:
            $has_partial_derivative_at(h,p,2,1,a*g(p)+f(p)*b)
    release thm partial_at_multiply(f,g,h,p,2,1,a,b)
"#,
    r#"# Apply the quotient rule where the denominator function never vanishes on its declared domain.
thm partial_builtin_algebra_divide:
    ? forall f,g,h fn(x cart_n(R,2)) R,p cart_n(R,2),a,b R:
        forall q cart_n(R,2):
            g(q)!=0
        $has_partial_derivative_at(f,p,2,1,a)
        $has_partial_derivative_at(g,p,2,1,b)
        forall q cart_n(R,2):
            h(q)=f(q)/g(q)
        =>:
            $has_partial_derivative_at(h,p,2,1,(a*g(p)-f(p)*b)/g(p)/g(p))
    release thm partial_at_divide(f,g,h,p,2,1,a,b)
"#,
];

#[test]
fn partial_algebra_replays_original_native_schemas_deterministically() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(
            p.builtin.as_ref().unwrap().theorem,
            [
                BuiltinTheoremId::PartialAtAdd,
                BuiltinTheoremId::PartialAtSubtract,
                BuiltinTheoremId::PartialAtMultiply,
                BuiltinTheoremId::PartialAtDivide
            ][i]
        );
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), 21 + usize::from(i == 3));
        assert_eq!(p.dom_stores.len(), p.dom_proofs.len());
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "partial_algebra").unwrap();
        assert!(out.contains(&format!(
            "Litex.partialDerivative{}Functions",
            ["Add", "Sub", "Mul", "Div"][i]
        )));
        assert!(out.contains("_partial_formula"));
        assert_eq!(out, c.compile_run(&run, "partial_algebra").unwrap());
    }
}

#[test]
fn partial_algebra_requires_original_ordered_pipeline_stages() {
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
                2 => p.dom_proofs.swap(0, 6),
                3 => p.dom_stores.swap(0, 6),
                4 => p.conclusions_wd.clear(),
                5 => p.theorem_derivation = TheoremDerivationProof::UserTheorem,
                6 => p.builtin.as_mut().unwrap().requirements.swap(18, 19),
                7 => {
                    p.builtin.as_mut().unwrap().arguments.pop();
                }
                _ => p.builtin.as_mut().unwrap().conclusions.clear(),
            }
            assert!(
                c.compile_run(&run, "changed_partial_stage").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn partial_algebra_keeps_original_function_point_axis_and_coefficients() {
    for source in SOURCES {
        for candidate in [18, 19, usize::MAX] {
            for arg in 0..5 {
                let (mut run, c) = super::execute(source);
                let b = invocation(&mut run).builtin.as_mut().unwrap();
                let fact = if candidate == usize::MAX {
                    &mut b.conclusions[0]
                } else {
                    &mut b.requirements[candidate]
                };
                let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = fact else {
                    panic!()
                };
                let mut args = p
                    .relation
                    .argument_refs()
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>();
                args[arg] = super::number_object("99");
                p.relation = p.relation.with_arguments(&args);
                assert!(
                    c.compile_run(&run, "changed_partial_candidate").is_err(),
                    "{candidate}/{arg}"
                );
            }
        }
    }
}

#[test]
fn partial_algebra_preserves_all_three_contexts_and_original_function_captures() {
    for source in SOURCES {
        for index in 0..18 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
                Fact::AtomicFact(AtomicFact::EqualFact(p)) => p.right = super::number_object("99"),
                Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                    p.right = Obj::StandardSet(StandardSet::C)
                }
                _ => panic!("context {index}"),
            }
            assert!(
                c.compile_run(&run, "changed_partial_context").is_err(),
                "{index}"
            );
        }
        for index in [18, 19] {
            for change in 0..4 {
                let (mut run, c) = super::execute(source);
                let p = invocation(&mut run);
                let Some(InferResult::AtomicFact(
                    InferAtomicFactResult::MultivariableAnalysisFact(rules),
                )) = &mut p.dom_stores[index].infer
                else {
                    panic!()
                };
                let InferMultivariableAnalysisFactResult::Definition(capture) = &mut rules[0];
                match change {
                    0 => capture.function_domain = None,
                    1 => capture.derived.clear(),
                    2 => capture.source_fact_id = capture.derived[0].primary_fact_id(),
                    _ => {
                        capture.function_domain.as_mut().unwrap().signature.ret_set =
                            Box::new(Obj::StandardSet(StandardSet::C))
                    }
                }
                assert!(
                    c.compile_run(&run, "changed_partial_capture").is_err(),
                    "{index}/{change}"
                );
            }
        }
    }
}

#[test]
fn partial_algebra_retains_original_pointwise_equation_and_binder_scope() {
    for source in SOURCES {
        for change in 0..6 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::ForallFact(p) = &mut b.requirements[20] else {
                panic!()
            };
            match change {
                0 => {
                    p.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                1 => {
                    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &b.arguments[3] else {
                        panic!()
                    };
                    p.typed_parameters.groups[0].params[0].id = *id;
                }
                2 => p.dom_facts.push(p.then_facts[0].clone().into()),
                3 => p.then_facts.clear(),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut p.then_facts[0]
                    else {
                        panic!()
                    };
                    if change == 4 {
                        std::mem::swap(&mut eq.left, &mut eq.right);
                    } else {
                        eq.right = super::number_object("99");
                    }
                }
            }
            assert!(
                c.compile_run(&run, "changed_partial_formula").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn partial_algebra_requires_original_goal_formation_and_real_coefficient() {
    for source in SOURCES {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0] else {
                panic!()
            };
            let PredicateDomainProof::MultivariableAnalysis(f) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!()
            };
            match change {
                0 => {
                    f.requirements.pop();
                }
                1 => {
                    f.function_domain.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C))
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::InFact(p)) =
                        &mut f.requirements[if change == 2 { 0 } else { 6 }].requirement
                    else {
                        panic!()
                    };
                    p.set = Obj::StandardSet(StandardSet::C);
                }
            }
            assert!(
                c.compile_run(&run, "changed_partial_formation").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn partial_algebra_cannot_cite_its_future_conclusion_as_a_formula() {
    for source in SOURCES {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let VerifyFactResult::ForallFact(proof) = &mut p.dom_proofs[20] else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
            proof.as_mut()
        else {
            panic!()
        };
        proof.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_partial_formula").is_err());
    }
}

#[test]
fn partial_algebra_division_retains_original_nonzero_denominator() {
    for change in 0..3 {
        let (mut run, c) = super::execute(SOURCES[3]);
        let p = invocation(&mut run);
        match change {
            0 => {
                p.dom_proofs.pop();
            }
            _ => {
                let Fact::AtomicFact(AtomicFact::NotEqualFact(f)) =
                    &mut p.builtin.as_mut().unwrap().requirements[21]
                else {
                    panic!()
                };
                if change == 1 {
                    f.left = super::number_object("99");
                } else {
                    f.right = super::number_object("99");
                }
            }
        }
        assert!(c.compile_run(&run, "changed_partial_nonzero").is_err());
    }
}

#[test]
fn partial_algebra_rejects_missing_derivative_premises() {
    for source in SOURCES {
        for premise in [
            "        $has_partial_derivative_at(f,p,2,1,a)\n",
            "        $has_partial_derivative_at(g,p,2,1,b)\n",
        ] {
            let source = source.replace(premise, "");
            let command =
                parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
            let mut runtime = Runtime::new_with_result_detail(
                command,
                crate::result_detail::OutputDetail::Detailed,
            );
            let run = runtime.run_litex_code(&source).unwrap();
            assert!(!run.success);
            assert!(super::LitexToLeanCompiler::new(runtime)
                .compile_run(&run, "unproved_partial")
                .is_err());
        }
    }
}
