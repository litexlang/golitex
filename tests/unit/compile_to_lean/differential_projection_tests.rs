use super::antiderivative_tests::body;
use crate::execute::execute_by_stmt::{
    ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SOURCES: [&str; 3] = [
    r#"# Project the original scalar differential onto an arbitrary source coordinate.
thm scalar_differential_builtin_partial:
    ? forall n N+,f fn(x cart_n(R,n)) R,p cart_n(R,n),A matrix(R,1,n),k closed_range(1,n):
        $has_scalar_differential_at(f,p,n,A)
        =>:
            $has_partial_derivative_at(f,p,n,k,A(1,k))
    release thm scalar_differential_at_partial(f,p,n,A,k)
"#,
    r#"# Keep the differential matrix's original first row as the resulting gradient function.
thm scalar_differential_builtin_gradient:
    ? forall n N+,f fn(x cart_n(R,n)) R,p cart_n(R,n),A matrix(R,1,n):
        $has_scalar_differential_at(f,p,n,A)
        =>:
            $has_gradient_at(f,p,n,fn(k closed_range(1,n)) R {A(1,k)})
    release thm scalar_differential_at_gradient(f,p,n,A)
"#,
    r#"# Preserve the supplied total derivative matrix in every original Jacobian coordinate.
thm total_derivative_builtin_jacobian:
    ? forall n,m N+,f fn(x cart_n(R,n)) cart_n(R,m),p cart_n(R,n),A matrix(R,m,n):
        $has_total_derivative_at(f,p,n,m,A)
        =>:
            $has_jacobian_at(f,p,n,m,A)
    release thm total_derivative_at_jacobian(f,p,n,m,A)
"#,
];
const GUARDED: [&str; 3] = [
    r#"# Retain the original guarded domain when projecting the differential's second coordinate.
thm scalar_differential_builtin_partial_guarded:
    ? forall f fn(x cart_n(R,2):x(1)>0) R,p cart_n(R,2),A matrix(R,1,2):
        p(1)>0
        $has_scalar_differential_at(f,p,2,A)
        =>:
            $has_partial_derivative_at(f,p,2,2,A(1,2))
    release thm scalar_differential_at_partial(f,p,2,A,2)
"#,
    r#"# The gradient projection retains the guarded function and exact original matrix row.
thm scalar_differential_builtin_gradient_guarded:
    ? forall f fn(x cart_n(R,2):x(1)>0) R,p cart_n(R,2),A matrix(R,1,2):
        p(1)>0
        $has_scalar_differential_at(f,p,2,A)
        =>:
            $has_gradient_at(f,p,2,fn(k closed_range(1,2)) R {A(1,k)})
    release thm scalar_differential_at_gradient(f,p,2,A)
"#,
    r#"# Retain the rectangular derivative matrix and the original guarded vector-function domain.
thm total_derivative_builtin_jacobian_guarded:
    ? forall f fn(x cart_n(R,2):x(1)>0) cart_n(R,3),p cart_n(R,2),A matrix(R,3,2):
        p(1)>0
        $has_total_derivative_at(f,p,2,3,A)
        =>:
            $has_jacobian_at(f,p,2,3,A)
    release thm total_derivative_at_jacobian(f,p,2,3,A)
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
fn differential_projections_replay_original_generic_and_guarded_schemas() {
    for sources in [SOURCES, GUARDED] {
        for (i, s) in sources.into_iter().enumerate() {
            let (mut run, c) = super::execute(s);
            let p = invocation(&mut run);
            assert!(matches!(
                p.theorem_derivation,
                TheoremDerivationProof::NativeSchema
            ));
            assert_eq!(p.dom_proofs.len(), if i == 2 { 7 } else { 6 });
            assert_eq!(p.dom_proofs.len(), p.dom_stores.len());
            assert_eq!(p.conclusions_wd.len(), 1);
            let out = c.compile_run(&run, "differential_projection").unwrap();
            assert!(out.contains(
                [
                    "Litex.scalarDifferentialPartialCandidate",
                    "Litex.scalarDifferentialGradientRow",
                    "Litex.totalDifferentialJacobianCandidate"
                ][i]
            ));
            assert_eq!(out, c.compile_run(&run, "differential_projection").unwrap());
        }
    }
}

#[test]
fn differential_projections_require_original_ordered_pipeline_stages() {
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
                c.compile_run(&run, "changed_projection_stage").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn differential_projections_keep_original_positive_candidates_and_goal_arguments() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for goal in [false, true] {
            for change in 0..5 {
                let (mut run, c) = super::execute(s);
                let b = invocation(&mut run).builtin.as_mut().unwrap();
                let fact = if goal {
                    &mut b.conclusions[0]
                } else {
                    b.requirements.last_mut().unwrap()
                };
                let Fact::AtomicFact(f) = fact else { panic!() };
                if change == 4 {
                    *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap()
                } else {
                    let AtomicFact::MultivariableAnalysisFact(p) = f else {
                        panic!()
                    };
                    macro_rules! endpoint {
                        ($value:expr,$dimension:ident) => {
                            match change {
                                0 => &mut $value.function,
                                1 => &mut $value.point,
                                2 => &mut $value.$dimension,
                                _ => &mut $value.value,
                            }
                        };
                    }
                    let field = match &mut p.relation {
                        MultivariableAnalysisRelation::ScalarDifferentialAt(q) => {
                            endpoint!(q, dimension)
                        }
                        MultivariableAnalysisRelation::TotalDerivativeAt(q) => {
                            endpoint!(q, input_dimension)
                        }
                        MultivariableAnalysisRelation::PartialDerivativeAt(q) => {
                            endpoint!(q, dimension)
                        }
                        MultivariableAnalysisRelation::GradientAt(q) => endpoint!(q, dimension),
                        MultivariableAnalysisRelation::JacobianAt(q) => {
                            endpoint!(q, input_dimension)
                        }
                        _ => panic!(),
                    };
                    *field = super::number_object("99");
                }
                assert!(
                    c.compile_run(&run, "changed_projection_subject").is_err(),
                    "{i}/{goal}/{change}"
                );
            }
        }
    }
}

#[test]
fn differential_projections_keep_original_context_carriers_and_point_membership() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        for index in 0..if i == 2 { 6 } else { 5 } {
            let (mut run, c) = super::execute(s);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
                Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                    p.right = Obj::StandardSet(StandardSet::C)
                }
                Fact::AtomicFact(AtomicFact::EqualFact(p)) => {
                    p.right = Obj::StandardSet(StandardSet::C)
                }
                _ => panic!(),
            }
            assert!(
                c.compile_run(&run, "changed_projection_context").is_err(),
                "{i}/{index}"
            );
        }
    }
}

#[test]
fn differential_projections_require_original_definition_inference_and_complete_domain() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for s in SOURCES {
        for change in 0..5 {
            let (mut run, c) = super::execute(s);
            let p = invocation(&mut run);
            let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
            let store = p.dom_stores.last_mut().unwrap();
            if change == 0 {
                store.infer = None
            } else {
                let Some(InferResult::AtomicFact(
                    InferAtomicFactResult::MultivariableAnalysisFact(rules),
                )) = &mut store.infer
                else {
                    panic!()
                };
                let [InferMultivariableAnalysisFactResult::Definition(cap)] = rules.as_mut_slice()
                else {
                    panic!()
                };
                match change {
                    1 => {
                        cap.derived.pop();
                    }
                    2 => cap.source_fact_id = future,
                    3 => cap.function_domain = None,
                    _ => {
                        cap.function_domain
                            .as_mut()
                            .unwrap()
                            .signature
                            .set_bound_parameters
                            .groups[0]
                            .param_type = Box::new(Obj::StandardSet(StandardSet::C))
                    }
                }
            }
            assert!(
                c.compile_run(&run, "changed_projection_capture").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn differential_gradient_keeps_fresh_exact_first_row_function() {
    for change in 0..5 {
        let (mut run, c) = super::execute(SOURCES[1]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Obj::Identifier(IdentifierObj::Plain { id: captured, .. }) = &b.arguments[0] else {
            panic!()
        };
        let captured = *captured;
        let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = &mut b.conclusions[0]
        else {
            panic!()
        };
        let MultivariableAnalysisRelation::GradientAt(p) = &mut p.relation else {
            panic!()
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(g)) = &mut p.value else {
            panic!()
        };
        match change {
            0 => {
                g.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::C))
            }
            1 => g.body.set_bound_parameters.groups[0].params[0].id = captured,
            2 => g.body.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            3 => g.equal_to = Box::new(super::number_object("99")),
            _ => {
                let Obj::FnObj(f) = g.equal_to.as_mut() else {
                    panic!()
                };
                *f.body[0][0] = super::number_object("2");
            }
        }
        assert!(
            c.compile_run(&run, "changed_gradient_row").is_err(),
            "{change}"
        );
    }
}

#[test]
fn differential_partial_requires_original_coordinate_membership_formation() {
    for change in 0..4 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut invocation(&mut run).conclusions_wd[0]
        else {
            panic!()
        };
        let d = wd.as_detailed_mut().unwrap();
        if change == 3 {
            d.well_defined_of_each_parameter.pop();
        } else {
            let PredicateDomainProof::MultivariableAnalysis(cap) = &mut d.predicate_domain else {
                panic!()
            };
            match change {
                0 => {
                    cap.requirements.pop();
                }
                1 => cap.requirements.swap(4, 5),
                _ => {
                    let Fact::AtomicFact(AtomicFact::InFact(p)) =
                        &mut cap.requirements[5].requirement
                    else {
                        panic!()
                    };
                    p.set = Obj::StandardSet(StandardSet::C);
                }
            }
        }
        assert!(
            c.compile_run(&run, "changed_projection_axis_formation")
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn differential_projections_reject_future_candidate_citations() {
    for s in SOURCES {
        let (mut run, c) = super::execute(s);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let proof = super::atomic_proof_mut(p.dom_proofs.last_mut().unwrap());
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
            &mut proof.searched_proof
        else {
            panic!()
        };
        cite.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_projection_candidate").is_err());
    }
}

#[test]
fn differential_projection_source_requires_the_recorded_differential() {
    for (i, s) in SOURCES.into_iter().enumerate() {
        let source = s.replace(
            if i == 2 {
                "        $has_total_derivative_at(f,p,n,m,A)\n"
            } else {
                "        $has_scalar_differential_at(f,p,n,A)\n"
            },
            "",
        );
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(&source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "missing_differential_projection_candidate")
            .is_err());
    }
}
