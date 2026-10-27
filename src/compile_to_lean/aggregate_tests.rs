use crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
use crate::prelude::*;

fn execute(source: &str) -> (Runtime, RunLitexCodeResult) {
    let mut runtime = Runtime::new(
        parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap(),
    );
    let result = runtime.run_litex_code(source).unwrap();
    (runtime, result)
}

#[test]
fn aggregate_wd_captures_original_literal_or_property_signature() {
    for expression in [
        "sum(1, 3, ITERAND) = 6",
        "product(1, 3, ITERAND) = 6",
        "finite_set_sum({1, 2, 3}, ITERAND) = 6",
        "finite_set_product({1, 2, 3}, ITERAND) = 6",
    ] {
        for named in [false, true] {
            let source = if named {
                format!(
                    "have fn f(x Z) Z = x\n{}",
                    expression.replace("ITERAND", "f")
                )
            } else {
                expression.replace("ITERAND", "fn(x Z) Z {x}")
            };
            let (runtime, result) = execute(&source);
            assert!(result.success, "{source}");
            let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
                result.statement_results.last().unwrap()
            else {
                panic!()
            };
            let VerifyFactResult::Equality(p) = &p.verify_result else {
                panic!()
            };
            let VerifyEqualityResult::Success(p) = p.as_ref() else {
                panic!()
            };
            let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::IteratedOperator(p),
                ..
            } = &p.well_defined_proof.left
            else {
                panic!()
            };
            let selection = match p {
                P::Sum(p) => &p.signature_selection,
                P::Product(p) => &p.signature_selection,
                P::SumOfFiniteSet(p) => &p.signature_selection,
                P::ProductOfFiniteSet(p) => &p.signature_selection,
                _ => panic!(),
            };
            match selection.as_ref().unwrap() {
                FunctionSignatureSelection::AnonymousLiteral { signature } => {
                    assert!(!named);
                    assert_eq!(
                        signature.ret_set.as_ref(),
                        &Obj::StandardSet(StandardSet::Z)
                    );
                }
                FunctionSignatureSelection::Property { signature, fact_id } => {
                    assert!(named);
                    assert_eq!(
                        signature.ret_set.as_ref(),
                        &Obj::StandardSet(StandardSet::Z)
                    );
                    assert!(matches!(runtime.fact_by_id_in_stack(*fact_id),
                        Some(Fact::AtomicFact(AtomicFact::InFact(f)))
                        if f.element.readable_string() == "f" && f.set == Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone()))));
                }
                FunctionSignatureSelection::DeclaredField { .. } => panic!(),
            }
            let json = crate::json_output::project_run_detailed(&result, &runtime, "test", None);
            let mut projected = json
                .as_object()
                .unwrap()
                .get("statement_results")
                .unwrap()
                .as_array()
                .unwrap()
                .last()
                .unwrap();
            for field in ["verify", "well_defined", "left", "signature_selection"] {
                projected = projected.as_object().unwrap().get(field).unwrap();
            }
            let projected = projected.as_object().unwrap();
            assert_eq!(
                projected.get("signature").unwrap().as_str().unwrap(),
                Obj::FunctionSpace(FunctionSpace::FnSet(
                    selection.as_ref().unwrap().signature().clone()
                ))
                .readable_string()
            );
            match selection.as_ref().unwrap() {
                FunctionSignatureSelection::AnonymousLiteral { .. } => assert_eq!(
                    projected.get("source").unwrap().as_str().unwrap(),
                    "anonymous_literal"
                ),
                FunctionSignatureSelection::Property { fact_id, .. } => assert_eq!(
                    projected
                        .get("source")
                        .unwrap()
                        .as_object()
                        .unwrap()
                        .get("fact_id")
                        .unwrap()
                        .as_str()
                        .unwrap(),
                    fact_id.to_string()
                ),
                FunctionSignatureSelection::DeclaredField { .. } => unreachable!(),
            }
        }
    }
}

#[test]
fn aggregate_capture_preserves_domain_rejections() {
    for source in [
        "sum(3, 1, fn(x Z) Z {x}) = 0",
        "product(0, 2, fn(x R: x != 0) R {1 / x}) = 0",
        "finite_set_sum({0}, fn(x R: x != 0) R {1 / x}) = 0",
        "sum(1, 3, fn(x, y Z) Z {x + y}) = 6",
    ] {
        assert!(!execute(source).1.success, "{source}");
    }
}

#[test]
fn range_aggregate_generic_formation_and_carrier() {
    for operation in ["sum", "product"] {
        for domain in ["Z", "Q", "R", "C"] {
            let source = format!(
                "forall lower, upper Z:\n    lower <= upper\n    =>:\n        {operation}(lower, upper, fn(x {domain}) {domain} {{x}}) $in C\n"
            );
            let (runtime, run) = execute(&source);
            assert!(run.success, "{source}");
            let compiler = super::LitexToLeanCompiler::new(runtime);
            let generated = compiler.compile_run(&run, "range_aggregate").unwrap();
            assert_eq!(
                generated,
                compiler.compile_run(&run, "range_aggregate").unwrap()
            );
            assert!(generated.contains("Litex.rangeAggregate"));
        }
    }
}

#[test]
fn range_aggregate_calculation_replays_literal_and_named_terms() {
    for source in [
        "sum(1, 3, fn(x Z) Z {x}) = 6",
        "product(1, 3, fn(x Z) Z {x}) = 6",
        "sum(-2, 2, fn(x Z) Z {x * x}) = 10",
        "product(-2, 2, fn(x Z) Z {x}) = 0",
        "sum(1, 3, fn(x Z) Q {x / 2}) = 3",
        "have fn f(x Z) Z = x + 1\nsum(1, 3, f) = 9",
    ] {
        let (runtime, run) = execute(source);
        assert!(run.success, "{source}");
        let compiler = super::LitexToLeanCompiler::new(runtime);
        let lean = compiler.compile_run(&run, "aggregate_calculation").unwrap();
        assert_eq!(
            lean,
            compiler.compile_run(&run, "aggregate_calculation").unwrap()
        );
    }
}

fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    let VerifyFactResult::Equality(p) = &mut p.verify_result else {
        panic!()
    };
    let VerifyEqualityResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}

#[test]
fn range_aggregate_rejects_missing_signature_or_wd() {
    for missing in 0..5 {
        let (runtime, mut run) = execute("sum(1, 3, fn(x Z) Z {x}) = 6");
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IteratedOperator(P::Sum(p)),
            ..
        } = &mut equality(&mut run).well_defined_proof.left
        else {
            panic!()
        };
        if missing == 4 {
            p.signature_selection = None;
        } else {
            p.requirement_fact_verified.remove(missing);
        }
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_aggregate")
            .is_err());
    }
}

#[test]
fn range_aggregate_rejects_changed_calculation_evidence() {
    use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
        AggregateEvaluationResult, AggregateTermExpansion,
    };
    for changed in 0..6 {
        let (runtime, mut run) = execute("sum(1, 3, fn(x Z) Z {x}) = 6");
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::AggregateCalculation(p),
        ) = &mut equality(&mut run).searched_proof
        else {
            panic!()
        };
        let AggregateEvaluationResult::Sum(p) = &mut p.aggregate_evaluations[0] else {
            panic!()
        };
        let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
        match changed {
            0 => p.bounds.end_integer = 4,
            1 => {
                p.terms.remove(1);
            }
            2 => p.terms[0].argument = wrong,
            3 => p.terms[0].accumulated_value = wrong,
            4 => p.value = wrong,
            _ => {
                let AggregateTermExpansion::Function(p) = &mut p.terms[0].expansion else {
                    panic!()
                };
                p.expanded_body = wrong;
            }
        }
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_aggregate")
            .is_err());
    }
}

#[test]
fn finite_aggregates_replay_empty_fractional_and_named_sets() {
    for source in [
        "finite_set_sum({}, fn(x Z) Z {x}) = 0",
        "finite_set_product({}, fn(x Z) Z {x}) = 1",
        "finite_set_sum({1, 2, 3}, fn(x Z) Z {x}) = 6",
        "finite_set_product({1, 2, 3}, fn(x Z) Z {x}) = 6",
        "finite_set_sum({1 / 3, 1 / 2}, fn(x Q) Q {x}) = 5 / 6",
        "finite_set_product({1 / 3, 1 / 2}, fn(x Q) Q {x}) = 1 / 6",
        "have A set = {2, 4, 7}\nhave fn f(x Z) Z = x + 1\nfinite_set_sum(A, f) = 16",
        "forall A finite_set, f fn(x R) R:\n    A $subset R\n    =>:\n        finite_set_sum(A, f) $in R\n        finite_set_product(A, f) $in R\n",
    ] {
        let (runtime, run) = execute(source);
        assert!(run.success, "{source}");
        let compiler = super::LitexToLeanCompiler::new(runtime);
        let lean = compiler
            .compile_run(&run, "finite_aggregate")
            .unwrap_or_else(|e| panic!("{source}: {e:?}"));
        assert_eq!(
            lean,
            compiler.compile_run(&run, "finite_aggregate").unwrap()
        );
    }
}

#[test]
fn finite_aggregate_rejects_missing_wd_or_signature() {
    for missing in 0..6 {
        let (runtime, mut run) = execute("finite_set_sum({1, 2}, fn(x Z) Z {x}) = 3");
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IteratedOperator(P::SumOfFiniteSet(p)),
            ..
        } = &mut equality(&mut run).well_defined_proof.left
        else {
            panic!()
        };
        match missing {
            0..=2 => {
                p.requirement_fact_verified.remove(missing);
            }
            3..=4 => {
                p.child_obj_well_defined.remove(missing - 3);
            }
            _ => p.signature_selection = None,
        }
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "missing_finite_aggregate")
            .is_err());
    }
}

#[test]
fn finite_aggregate_rejects_altered_enumeration_and_fold() {
    use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult;
    for changed in 0..6 {
        let (runtime, mut run) = execute("finite_set_sum({1, 2}, fn(x Z) Z {x}) = 3");
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::AggregateCalculation(p),
        ) = &mut equality(&mut run).searched_proof
        else {
            panic!()
        };
        let AggregateEvaluationResult::SumOfFiniteSet(p) = &mut p.aggregate_evaluations[0] else {
            panic!()
        };
        let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
        match changed {
            0 => p.enumeration.elements.swap(0, 1),
            1 => {
                p.terms.remove(1);
            }
            2 => p.terms[0].argument = wrong,
            3 => p.terms[0].accumulated_value = wrong,
            4 => p.value = wrong,
            _ => p.enumeration.resolved_set = wrong,
        }
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_finite_aggregate")
            .is_err());
    }
}

#[test]
fn finite_aggregate_keeps_guard_and_fold_boundaries() {
    let source = "finite_set_sum({1, 2}, fn(x Z: x != 0) Z {x}) = 3";
    let (runtime, run) = execute(source);
    assert!(run.success);
    assert!(super::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "guarded_finite_aggregate")
        .is_err());
    assert!(
        !execute("finite_set_sum({1, 1.0}, fn(x Z) Z {x}) = 1")
            .1
            .success
    );
}

#[test]
fn finite_aggregate_named_set_finiteness_keeps_original_equality_citations() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite as Rewrite;
    for duplicate in [false, true] {
        let (runtime, mut run) =
            execute("have A set = {1, 2}\nfinite_set_sum(A, fn(x Z) Z {x}) = 3");
        assert!(run.success);
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IteratedOperator(P::SumOfFiniteSet(p)),
            ..
        } = &mut equality(&mut run).well_defined_proof.left
        else {
            panic!()
        };
        let VerifyFactResult::AtomicExceptEquality(p) = &mut p.requirement_fact_verified[0] else {
            panic!()
        };
        let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() else {
            panic!()
        };
        assert!(matches!(p.fact, AtomicFact::IsFiniteSetFact(_)));
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(p) = &mut p.searched_proof
        else {
            panic!()
        };
        let ids = match p {
            Rewrite::KnownEqualObjSubstitution(p) => &mut p.cited_equal_fact_ids,
            Rewrite::ClosedNumericEqualSubstitution(p) => &mut p.cited_equal_fact_ids,
            _ => panic!(),
        };
        assert!(!ids.is_empty());
        if duplicate {
            ids.push(ids[0]);
        } else {
            ids.clear();
        }
        let error = super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_finite_citation")
            .unwrap_err();
        assert_eq!(error.route, "AtomicRewrite/Citations");
    }
}

#[test]
fn bounded_and_general_finite_aggregates_replay_original_domains() {
    for source in [
        include_str!("../../lean/examples/bounded_finite_aggregate_closure/statement.lit"),
        include_str!("../../lean/examples/general_finite_aggregate_closure/statement.lit"),
        include_str!("../../lean/examples/bounded_finite_aggregate_values/statement.lit"),
        include_str!("../../lean/examples/integer_ranges_finite/statement.lit"),
    ] {
        let (runtime, run) = execute(source);
        assert!(run.success);
        super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "bounded_aggregates")
            .unwrap();
    }
}

#[test]
fn bounded_finite_aggregate_rejects_changed_input_signature() {
    let (runtime, mut run) = execute("finite_set_sum({1,2,3},fn(k closed_range(1,3)) Z {k}) = 6");
    assert!(run.success);
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::IteratedOperator(P::SumOfFiniteSet(p)),
        ..
    } = &mut equality(&mut run).well_defined_proof.left
    else {
        panic!("finite sum WD")
    };
    let FunctionSignatureSelection::AnonymousLiteral { signature } =
        p.signature_selection.as_mut().unwrap()
    else {
        panic!("literal summand")
    };
    signature.set_bound_parameters.groups[0].param_type =
        Box::new(Obj::StandardSet(StandardSet::Z));
    assert!(super::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "wrong_bounded_sum")
        .is_err());
}

#[test]
fn finite_aggregate_alpha_checks_original_iterand_body() {
    let (runtime, mut run) = execute(include_str!(
        "../../lean/examples/finite_aggregate_bound_names/statement.lit"
    ));
    assert!(run.success);
    let compiler = super::LitexToLeanCompiler::new(runtime);
    compiler.compile_run(&run, "valid_aggregate_alpha").unwrap();
    let eq = equality(&mut run);
    let Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(p)) = &mut eq.fact.right else {
        panic!("product endpoint")
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = p.func.as_mut() else {
        panic!("factor function")
    };
    f.equal_to = Box::new(Obj::Literal(Literal::Number(Number::new("99".into()))));
    assert!(compiler
        .compile_run(&run, "changed_aggregate_alpha")
        .is_err());
}
