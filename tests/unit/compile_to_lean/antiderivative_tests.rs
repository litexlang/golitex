use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::execute_def_thm_stmt::ExecDefThmForallProof;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SOURCES: [&str; 5] = [
    r#"# Replay the explicit antiderivative definition on the full real line.
thm antiderivative_builtin_from_definition:
    ? forall F,f fn(x R) R:
        forall x R:
            $has_derivative_at(F,x,f(x))
        =>:
            $is_antiderivative_on(F,f,R)
    release thm antiderivative_from_definition(F,f,R)
"#,
    r#"# Project the explicit antiderivative definition at an arbitrary real point.
thm antiderivative_builtin_to_definition:
    ? forall F,f fn(x R) R,p R:
        $is_antiderivative_on(F,f,R)
        =>:
            $has_derivative_at(F,p,f(p))
    release thm antiderivative_to_definition(F,f,R)
"#,
    r#"# Restrict the original antiderivative relation to a nonempty open interval.
thm antiderivative_builtin_restrict:
    ? forall F,f fn(x R) R:
        $is_antiderivative_on(F,f,R)
        =>:
            $is_antiderivative_on(F,f,'(1,2))
    release thm antiderivative_restrict(F,f,R,'(1,2))
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Keep the primitive's full real domain and the function's positive real domain.
thm antiderivative_builtin_from_definition_independent_domains:
    ? forall F fn(x R) R,f fn(x R+) R:
        forall x '(1,2):
            $has_derivative_at(F,x,f(x))
        =>:
            $is_antiderivative_on(F,f,'(1,2))
    release thm antiderivative_from_definition(F,f,'(1,2))
"#,
    r#"# Prove interval coverage through the existing shared subset definition.
claim:
    ? forall anti_domain_probe '(1,2):
        anti_domain_probe $in R+
    anti_domain_probe>1
    1>0
    anti_domain_probe>0
'(1,2) $subset R+

# Project at an arbitrary point of the common covered interval.
thm antiderivative_builtin_to_definition_independent_domains:
    ? forall F fn(x R) R,f fn(x R+) R,p '(1,2):
        $is_antiderivative_on(F,f,'(1,2))
        =>:
            $has_derivative_at(F,p,f(p))
    release thm antiderivative_to_definition(F,f,'(1,2))
"#,
];
pub(super) fn body(run: &mut RunLitexCodeResult) -> &mut ExecDefThmForallProof {
    for statement in run.statement_results.iter_mut().rev() {
        if let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) = statement
        {
            let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
                panic!()
            };
            return p;
        }
    }
    panic!("original theorem")
}
pub(super) fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut body(run).proof_steps[0]
    else {
        panic!("original invocation")
    };
    p
}
fn original_wd(run: &mut RunLitexCodeResult, from: bool) -> &mut AtomicFactWellDefinedProof {
    let wd = if from {
        &mut invocation(run).conclusions_wd[0]
    } else {
        &mut body(run).assumed_dom_facts[0].well_defined
    };
    let FactWellDefinedProof::AtomicExceptEquality(wd) = wd else {
        panic!("original predicate WD")
    };
    wd
}

#[test]
fn antiderivative_replays_original_definition_and_restriction_schemas() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        let expected = [
            BuiltinTheoremId::AntiderivativeFromDefinition,
            BuiltinTheoremId::AntiderivativeToDefinition,
            BuiltinTheoremId::AntiderivativeRestrict,
            BuiltinTheoremId::AntiderivativeFromDefinition,
            BuiltinTheoremId::AntiderivativeToDefinition,
        ][i];
        assert_eq!(p.builtin.as_ref().unwrap().theorem, expected);
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(
            p.dom_proofs.len(),
            if i == 2 {
                11
            } else if i >= 3 {
                13
            } else {
                10
            }
        );
        assert_eq!(p.dom_stores.len(), p.dom_proofs.len());
        assert_eq!(p.conclusions_wd.len(), 1);
        let out = c.compile_run(&run, "antiderivative").unwrap();
        assert!(out.contains("Litex.IsAntiderivativeOnValue M"));
        assert!(out.contains(if i == 2 {
            "Litex.antiderivativeRestrict"
        } else if i == 0 || i == 3 {
            "Litex.antiderivativeFromDefiningClause"
        } else {
            "Litex.antiderivativeDefiningClause"
        }));
        assert_eq!(out, c.compile_run(&run, "antiderivative").unwrap());
    }
}

#[test]
fn antiderivative_requires_original_ordered_pipeline_stages() {
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
                c.compile_run(&run, "changed_antiderivative_stage").is_err(),
                "{change}"
            );
        }
    }
}

#[test]
fn antiderivative_preserves_original_defining_binder_and_derivative() {
    for (i, source) in SOURCES.into_iter().enumerate().filter(|(i, _)| *i != 2) {
        for change in 0..8 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let from = i == 0 || i == 3;
            let context = if i >= 3 { 12 } else { 9 };
            let domain_guard = b.requirements[0].clone();
            let fact = if from {
                &mut b.requirements[context]
            } else {
                &mut b.conclusions[0]
            };
            let Fact::ForallFact(p) = fact else { panic!() };
            match change {
                0 => {
                    p.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C))
                }
                1 => {
                    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &b.arguments[0] else {
                        panic!()
                    };
                    p.typed_parameters.groups[0].params[0].id = *id;
                }
                2 => p.dom_facts.push(domain_guard),
                3 => p.then_facts.clear(),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(fact) = &mut p.then_facts[0] else {
                        panic!()
                    };
                    if change == 7 {
                        *fact = crate::ast::fact::negate_atomic_fact(fact, fact.fact_id()).unwrap();
                    } else {
                        let AtomicFact::HasDerivativeAtFact(d) = fact else {
                            panic!()
                        };
                        match change {
                            4 => d.function = super::number_object("99"),
                            5 => d.point = super::number_object("99"),
                            _ => d.value = super::number_object("99"),
                        }
                    }
                }
            }
            assert!(
                c.compile_run(&run, "changed_antiderivative_definition")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn antiderivative_keeps_original_predicate_arguments_and_polarity() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let context = if i >= 3 { 12 } else { 9 };
            let fact = if i == 0 || i == 3 {
                &mut b.conclusions[0]
            } else {
                &mut b.requirements[context]
            };
            let Fact::AtomicFact(fact) = fact else {
                panic!()
            };
            if change == 3 {
                *fact = crate::ast::fact::negate_atomic_fact(fact, fact.fact_id()).unwrap();
            } else {
                let AtomicFact::NormalAtomicFact(p) = fact else {
                    panic!()
                };
                p.body[change] = super::number_object("99");
            }
            assert!(
                c.compile_run(&run, "changed_antiderivative_subject")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn antiderivative_restriction_retains_target_source_orientation_and_goal() {
    for change in 0..5 {
        let (mut run, c) = super::execute(SOURCES[2]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        if change < 3 {
            let Fact::AtomicFact(AtomicFact::SubsetFact(p)) = &mut b.requirements[10] else {
                panic!()
            };
            match change {
                0 => std::mem::swap(&mut p.left, &mut p.right),
                1 => p.left = super::number_object("99"),
                _ => p.right = super::number_object("99"),
            }
        } else {
            let Fact::AtomicFact(AtomicFact::NormalAtomicFact(p)) = &mut b.conclusions[0] else {
                panic!()
            };
            p.body[if change == 3 { 0 } else { 2 }] = super::number_object("99");
        }
        assert!(
            c.compile_run(&run, "changed_antiderivative_restriction")
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn antiderivative_preserves_independent_complete_function_domain_requirements() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in 0..10 {
            let (mut run, c) = super::execute(source);
            let wd = original_wd(&mut run, i == 0 || i == 3);
            let PredicateDomainProof::ByRequirements(req) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("original requirements")
            };
            let offset = req.len() - 8;
            match change {
                0 => {
                    req.pop();
                }
                1 => req.swap(offset, offset + 4),
                2 => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(p)) = &mut req[0].requirement
                    else {
                        panic!()
                    };
                    p.right = Obj::StandardSet(StandardSet::C);
                }
                3 | 4 => {
                    let Fact::AtomicFact(AtomicFact::InFact(p)) = &mut req[offset].requirement
                    else {
                        panic!()
                    };
                    if change == 3 {
                        p.element = super::number_object("99");
                    } else {
                        let Obj::FunctionSpace(FunctionSpace::FnSet(s)) = &mut p.set else {
                            panic!()
                        };
                        s.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
                    }
                }
                5 | 6 | 7 => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(p)) =
                        &mut req[offset + change - 4].requirement
                    else {
                        panic!()
                    };
                    p.left = Obj::StandardSet(StandardSet::C);
                }
                8 => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(p)) =
                        &mut req[offset + 7].requirement
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
                c.compile_run(&run, "changed_antiderivative_domains")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}

#[test]
fn antiderivative_rejects_missing_original_interval_endpoint_and_order_stages() {
    for source in [SOURCES[3], SOURCES[4]] {
        for index in 1..4 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            b.requirements[index] = b.requirements[0].clone();
            assert!(c
                .compile_run(&run, "changed_antiderivative_interval")
                .is_err());
        }
    }
}

#[test]
fn antiderivative_definition_cannot_cite_its_future_predicate() {
    let (mut run, c) = super::execute(SOURCES[0]);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let VerifyFactResult::ForallFact(proof) = &mut p.dom_proofs[9] else {
        panic!()
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
        proof.as_mut()
    else {
        panic!()
    };
    proof.cite_fact_id = future;
    assert!(c.compile_run(&run, "future_antiderivative").is_err());
}

#[test]
fn antiderivative_source_rejects_unproved_defining_derivatives() {
    let source = SOURCES[0].replace(
        "        forall x R:\n            $has_derivative_at(F,x,f(x))\n",
        "",
    );
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    let run = runtime.run_litex_code(&source).unwrap();
    assert!(!run.success);
    assert!(super::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "unproved_antiderivative")
        .is_err());
}

const KNOWN: [&str; 2] = [
    r#"# Replay the original quantified derivative candidate at an arbitrary point.
forall F,f fn(x R) R,p R:
    forall x R:
        $has_derivative_at(F,x,f(x))
    =>:
        $has_derivative_at(F,p,f(p))
"#,
    r#"# Replay the original quantified derivative candidate at an arbitrary point.
forall F,f fn(x R) R,p R:
    forall x R:
        not $has_derivative_at(F,x,f(x))
    =>:
        not $has_derivative_at(F,p,f(p))
"#,
];
#[test]
fn antiderivative_known_forall_derivative_uses_original_three_argument_captures() {
    for source in KNOWN {
        let (mut run, c) = super::execute(source);
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(proof) = &p.searched_proof
        else {
            panic!()
        };
        assert_eq!(proof.as_detailed().unwrap().arg_match_proofs.len(), 3);
        c.compile_run(&run, "derivative_known_forall").unwrap();
    }
}
#[test]
fn antiderivative_known_forall_derivative_retains_scope_and_instantiation_evidence() {
    for source in KNOWN {
        for change in 0..5 {
            let (mut run, c) = super::execute(source);
            let all = super::forall_proof_mut(&mut run.statement_results[0]);
            let p = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
            let future = p.fact.fact_id();
            let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(proof) =
                &mut p.searched_proof
            else {
                panic!()
            };
            let proof = proof.as_detailed_mut().unwrap();
            match change {
                0 => proof.arg_match_proofs.clear(),
                1 => proof.forall_parameters_match_what_args.clear(),
                2 => proof.forall_parameters_match_what_args[0] = super::number_object("99"),
                3 => proof.cite.fact_id = future,
                _ => {
                    proof
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements
                        .pop();
                }
            }
            assert!(
                c.compile_run(&run, "changed_derivative_instantiation")
                    .is_err(),
                "{change}"
            );
        }
    }
}
