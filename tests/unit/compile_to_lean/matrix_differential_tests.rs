use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::TheoremDerivationProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

const SOURCES: [&str; 3] = [
    r#"# The divergence of a vector field is the trace of its supplied Jacobian.
thm jacobian_builtin_divergence:
    ? forall F fn(x cart_n(R,2)) cart_n(R,2),p cart_n(R,2),J matrix(R,2,2):
        $has_jacobian_at(F,p,2,2,J)
        =>:
            $has_divergence_at(F,p,2,trace(J,2))
    release thm jacobian_at_divergence(F,p,2,J)
"#,
    r#"# The Laplacian is the trace of the supplied Hessian with ordered second partials.
thm hessian_builtin_laplacian:
    ? forall f fn(x cart_n(R,2)) R,p cart_n(R,2),H matrix(R,2,2):
        $has_hessian_at(f,p,2,H)
        =>:
            $has_laplacian_at(f,p,2,trace(H,2))
    release thm hessian_at_laplacian(f,p,2,H)
"#,
    r#"# The curl uses the original ordered differences of the supplied Jacobian entries.
thm jacobian_builtin_curl:
    ? forall F fn(x cart_n(R,3)) cart_n(R,3),p cart_n(R,3),J matrix(R,3,3):
        $has_jacobian_at(F,p,3,3,J)
        =>:
            $has_curl_at(F,p,(J(3,2)-J(2,3),J(1,3)-J(3,1),J(2,1)-J(1,2)))
    release thm jacobian_at_curl(F,p,J)
"#,
];
const VARIANTS: [(&str, usize); 5] = [
    (
        r#"# The divergence trace formula retains an arbitrary positive dimension.
thm jacobian_builtin_divergence_generic:
    ? forall n N+,F fn(x cart_n(R,n)) cart_n(R,n),p cart_n(R,n),J matrix(R,n,n):
        $has_jacobian_at(F,p,n,n,J)
        =>:
            $has_divergence_at(F,p,n,trace(J,n))
    release thm jacobian_at_divergence(F,p,n,J)
"#,
        0,
    ),
    (
        r#"# The Laplacian trace formula retains an arbitrary positive dimension.
thm hessian_builtin_laplacian_generic:
    ? forall n N+,f fn(x cart_n(R,n)) R,p cart_n(R,n),H matrix(R,n,n):
        $has_hessian_at(f,p,n,H)
        =>:
            $has_laplacian_at(f,p,n,trace(H,n))
    release thm hessian_at_laplacian(f,p,n,H)
"#,
        1,
    ),
    (
        r#"# The divergence trace bridge preserves the original positive-coordinate guard.
thm jacobian_builtin_divergence_guarded:
    ? forall F fn(x cart_n(R,2): x(1)>0) cart_n(R,2),p cart_n(R,2),J matrix(R,2,2):
        p(1)>0
        $has_jacobian_at(F,p,2,2,J)
        =>:
            $has_divergence_at(F,p,2,trace(J,2))
    release thm jacobian_at_divergence(F,p,2,J)
"#,
        0,
    ),
    (
        r#"# The Laplacian trace bridge preserves the original positive-coordinate guard.
thm hessian_builtin_laplacian_guarded:
    ? forall f fn(x cart_n(R,2): x(1)>0) R,p cart_n(R,2),H matrix(R,2,2):
        p(1)>0
        $has_hessian_at(f,p,2,H)
        =>:
            $has_laplacian_at(f,p,2,trace(H,2))
    release thm hessian_at_laplacian(f,p,2,H)
"#,
        1,
    ),
    (
        r#"# The curl bridge preserves the original guard and all three ordered coordinate differences.
thm jacobian_builtin_curl_guarded:
    ? forall F fn(x cart_n(R,3): x(1)>0) cart_n(R,3),p cart_n(R,3),J matrix(R,3,3):
        p(1)>0
        $has_jacobian_at(F,p,3,3,J)
        =>:
            $has_curl_at(F,p,(J(3,2)-J(2,3),J(1,3)-J(3,1),J(2,1)-J(1,2)))
    release thm jacobian_at_curl(F,p,J)
"#,
        2,
    ),
];
fn capture(
    p: &mut crate::execute::execute_by_stmt::ExecReleaseThmStmtSuccess,
    index: usize,
) -> &mut crate::store_fact_and_infer::InferMultivariableAnalysisDefinitionResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &mut p.dom_stores[index].infer
    else {
        panic!()
    };
    let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_mut_slice() else {
        panic!()
    };
    capture
}

#[test]
fn matrix_differential_replays_original_concrete_generic_and_guarded_projections() {
    for (source, i) in SOURCES
        .into_iter()
        .enumerate()
        .map(|(i, s)| (s, i))
        .chain(VARIANTS)
    {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(
            p.builtin.as_ref().unwrap().theorem,
            [
                BuiltinTheoremId::JacobianAtDivergence,
                BuiltinTheoremId::HessianAtLaplacian,
                BuiltinTheoremId::JacobianAtCurl
            ][i]
        );
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), if i == 1 { 6 } else { 7 });
        assert_eq!(p.dom_stores.len(), p.dom_proofs.len());
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "matrix_differential").unwrap();
        assert!(out.contains(
            [
                "Litex.divergenceOfJacobianMatrix",
                "Litex.laplacianOfHessianMatrix",
                "Litex.curlOfJacobianMatrix"
            ][i]
        ));
        assert_eq!(out, c.compile_run(&run, "matrix_differential").unwrap());
    }
}

#[test]
fn matrix_differential_requires_every_original_ordered_pipeline_stage() {
    for source in SOURCES {
        for change in 0..10 {
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
                _ => p.builtin.as_mut().unwrap().theorem = BuiltinTheoremId::JacobianAtUnique,
            }
            assert!(
                c.compile_run(&run, "changed_matrix_projection_stage")
                    .is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn matrix_differential_preserves_positive_candidate_function_point_dimensions_and_matrix() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        let context = if i == 1 { 5 } else { 6 };
        for change in 0..if i == 1 { 5 } else { 6 } {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(fact) = &mut b.requirements[context] else {
                panic!()
            };
            if change == if i == 1 { 4 } else { 5 } {
                *fact = crate::ast::fact::negate_atomic_fact(fact, fact.fact_id()).unwrap();
            } else {
                let AtomicFact::MultivariableAnalysisFact(p) = fact else {
                    panic!()
                };
                let mut args = p
                    .relation
                    .argument_refs()
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>();
                args[change] = super::number_object("99");
                p.relation = p.relation.with_arguments(&args);
            }
            assert!(
                c.compile_run(&run, "changed_matrix_projection_source")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn matrix_differential_requires_original_dimension_carrier_and_point_context() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for index in 0..if i == 1 { 5 } else { 6 } {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            match &mut b.requirements[index] {
                Fact::AtomicFact(AtomicFact::InFact(p)) => p.set = Obj::StandardSet(StandardSet::C),
                Fact::AtomicFact(AtomicFact::SubsetFact(p)) => {
                    p.right = Obj::StandardSet(StandardSet::C)
                }
                Fact::AtomicFact(AtomicFact::EqualFact(p)) => p.right = super::number_object("99"),
                _ => panic!("{index}"),
            }
            assert!(
                c.compile_run(&run, "changed_matrix_projection_context")
                    .is_err(),
                "{i}/{index}"
            );
        }
    }
}

#[test]
fn matrix_differential_requires_original_complete_domain_and_definition_inference() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in 0..6 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let context = if i == 1 { 5 } else { 6 };
            let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
            let cap = capture(p, context);
            match change {
                0 => cap.function_domain = None,
                1 => {
                    cap.derived.pop();
                }
                2 => cap.source_fact_id = future,
                3 => {
                    cap.function_domain.as_mut().unwrap().signature.ret_set =
                        Box::new(Obj::StandardSet(StandardSet::C))
                }
                4 => {
                    cap.function_domain
                        .as_mut()
                        .unwrap()
                        .signature
                        .set_bound_parameters
                        .groups[0]
                        .param_type = Box::new(Obj::StandardSet(StandardSet::C))
                }
                _ => {
                    let g = &mut cap
                        .function_domain
                        .as_mut()
                        .unwrap()
                        .signature
                        .set_bound_parameters
                        .groups[0];
                    g.params.push(g.params[0].clone());
                }
            }
            assert!(
                c.compile_run(&run, "changed_matrix_projection_capture")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn matrix_differential_preserves_exact_trace_order_matrix_and_goal_subject() {
    for source in [SOURCES[0], SOURCES[1]] {
        for change in 0..6 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = &mut b.conclusions[0]
            else {
                panic!()
            };
            let mut args = p
                .relation
                .argument_refs()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            if change < 3 {
                args[change] = super::number_object("99");
            } else {
                let Obj::MatrixOperator(MatrixOperator::Trace(t)) = &mut args[3] else {
                    panic!()
                };
                match change {
                    3 => t.matrix = Box::new(super::number_object("99")),
                    4 => t.order = Box::new(super::number_object("99")),
                    _ => std::mem::swap(&mut t.matrix, &mut t.order),
                }
            }
            p.relation = p.relation.with_arguments(&args);
            assert!(
                c.compile_run(&run, "changed_trace_projection").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn matrix_differential_preserves_curl_coordinate_order_signs_and_indices() {
    for change in 0..7 {
        let (mut run, c) = super::execute(SOURCES[2]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = &mut b.conclusions[0]
        else {
            panic!()
        };
        let mut args = p
            .relation
            .argument_refs()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        let Obj::ProductShape(ProductShape::Tuple(t)) = &mut args[2] else {
            panic!()
        };
        match change {
            0 => t.args.swap(0, 1),
            1 => {
                t.args.pop();
            }
            2 => t.args[0] = Box::new(super::number_object("99")),
            _ => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) = t.args[0].as_mut() else {
                    panic!()
                };
                match change {
                    3 => std::mem::swap(&mut s.left, &mut s.right),
                    4 => s.left = Box::new(super::number_object("99")),
                    5 => s.right = Box::new(super::number_object("99")),
                    _ => s.right = s.left.clone(),
                }
            }
        }
        p.relation = p.relation.with_arguments(&args);
        assert!(
            c.compile_run(&run, "changed_curl_projection").is_err(),
            "{change}"
        );
    }
}

#[test]
fn matrix_differential_rejects_future_candidates_and_missing_goal_formation() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in 0..3 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            if change == 0 {
                let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
                let context = if i == 1 { 5 } else { 6 };
                let proof = super::atomic_proof_mut(&mut p.dom_proofs[context]);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut proof.searched_proof
                else {
                    panic!()
                };
                cite.cite_fact_id = future;
            } else {
                let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut p.conclusions_wd[0]
                else {
                    panic!()
                };
                let detailed = wd.as_detailed_mut().unwrap();
                if change == 1 {
                    detailed.well_defined_of_each_parameter.pop();
                } else {
                    let PredicateDomainProof::MultivariableAnalysis(cap) =
                        &mut detailed.predicate_domain
                    else {
                        panic!()
                    };
                    cap.requirements.pop();
                }
            }
            assert!(
                c.compile_run(&run, "changed_projection_scope_or_wd")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn matrix_differential_source_requires_the_original_jacobian_or_hessian() {
    for original in SOURCES {
        let source = original
            .lines()
            .filter(|line| {
                !line.trim_start().starts_with("$has_jacobian_at(")
                    && !line.trim_start().starts_with("$has_hessian_at(")
            })
            .collect::<Vec<_>>()
            .join("\n")
            + "\n";
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(&source).unwrap();
        assert!(!run.success);
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "missing_projection_candidate")
            .is_err());
    }
}

#[test]
fn matrix_differential_keeps_positive_target_and_original_function_and_point() {
    for source in SOURCES {
        for change in 0..3 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let Fact::AtomicFact(f) = &mut b.conclusions[0] else {
                panic!()
            };
            if change == 2 {
                *f = crate::ast::fact::negate_atomic_fact(f, f.fact_id()).unwrap();
            } else {
                let AtomicFact::MultivariableAnalysisFact(p) = f else {
                    panic!()
                };
                let mut args = p
                    .relation
                    .argument_refs()
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>();
                args[change] = super::number_object("99");
                p.relation = p.relation.with_arguments(&args);
            }
            assert!(
                c.compile_run(&run, "changed_matrix_projection_target")
                    .is_err(),
                "{change}"
            );
        }
    }
}
