use crate::prelude::*;

#[test]
fn ordered_fold_generic_carrier_compiles_from_captured_signatures() {
    let source = include_str!("../../../lean/examples/ordered_fold_carrier/statement.lit");
    let (run, compiler) = super::execute(source);
    let lean = compiler.compile_run(&run, "ordered_fold_carrier").unwrap();
    assert!(lean.contains("Litex.rangeFold"));
}

#[test]
fn ordered_fold_rejects_missing_signature_capture() {
    let (mut run, compiler) =
        super::execute("$is_set(reduce(1,3,fn(k Z) Z{k},fn(a,b Z) Z{a+b},0))");
    let p = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let ObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::IteratedOperator(
        crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef::Reduce(wd)), .. } = &mut p.well_defined_proof.well_defined_of_each_parameter[0] else { panic!("fold WD"); };
    assert!(wd.operation_signature_selection.is_some() && wd.iterand_signature_selection.is_some());
    wd.iterand_signature_selection = None;
    assert!(compiler
        .compile_run(&run, "missing_fold_signature")
        .is_err());
}

#[test]
fn finite_fold_generic_carrier_compiles_both_original_laws() {
    let source = include_str!("../../../lean/examples/finite_fold_carrier/statement.lit");
    let (run, compiler) = super::execute(source);
    let lean = compiler.compile_run(&run, "finite_fold_carrier").unwrap();
    assert!(lean.contains("Litex.finiteFold"));
    assert!(lean.contains("Litex.forallMembersOfRepresentations"));
}

#[test]
fn ordered_fold_calculation_replays_each_recorded_application() {
    let source = include_str!("../../../lean/examples/ordered_subtraction_fold/statement.lit");
    let (run, compiler) = super::execute(source);
    let lean = compiler
        .compile_run(&run, "ordered_subtraction_fold")
        .unwrap();
    assert!(lean.contains("Litex.rangeFoldDenote"));
    assert!(lean.contains("_step_2"));
}

#[test]
fn ordered_fold_calculation_rejects_changed_certificates() {
    use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
        AggregateEvaluationResult, FunctionApplicationExpansionProof,
    };
    for changed in 0..6 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/ordered_subtraction_fold/statement.lit"
        ));
        let equality = super::equality_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::AggregateCalculation(proof),
        ) = &mut equality.searched_proof
        else {
            panic!("calculation route");
        };
        let AggregateEvaluationResult::Reduce(p) = &mut proof.aggregate_evaluations[0] else {
            panic!("fold certificate");
        };
        let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
        match changed {
            0 => p.bounds.end_integer = 4,
            1 => {
                p.terms.remove(1);
            }
            2 => p.terms[0].argument = wrong,
            3 => p.terms[0].accumulated_value = wrong,
            4 => p.seed = wrong,
            _ => {
                let FunctionApplicationExpansionProof::Anonymous(p) =
                    &mut p.terms[0].operation.expansion
                else {
                    panic!("beta");
                };
                p.expanded_body = wrong;
            }
        }
        assert!(
            compiler
                .compile_run(&run, "changed_fold_certificate")
                .is_err(),
            "case {changed}"
        );
    }
}

#[test]
fn ordered_fold_keeps_natural_coverage_and_empty_guarded_domain() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/fold_domains/statement.lit"
    ));
    let lean = compiler.compile_run(&run, "fold_domains").unwrap();
    assert!(lean.contains("Litex.integerInNaturalAbove"));
    assert!(lean.contains("Litex.integerBoundsEmpty"));
}

#[test]
fn finite_fold_singleton_replays_the_explicit_builtin_theorem() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/finite_fold_singleton/statement.lit"
    ));
    assert!(compiler
        .compile_run(&run, "finite_fold_singleton")
        .unwrap()
        .contains("Litex.finiteFoldSingleton"));
}

#[test]
fn ordered_fold_last_step_replays_original_nonempty_endpoint_and_result() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/ordered_fold_last_step/statement.lit"
    ));
    assert!(compiler
        .compile_run(&run, "fold_last_step")
        .unwrap()
        .contains("Litex.rangeFoldLast"));
}

#[test]
fn ordered_fold_consumes_symbolic_and_each_literal_guard() {
    for source in [
        include_str!("../../../lean/examples/ordered_fold_guarded/statement.lit"),
        include_str!("../../../lean/examples/ordered_fold_guarded_literal/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler.compile_run(&run, "ordered_fold_guard").is_ok());
    }
}

#[test]
fn finite_fold_consumes_symbolic_literal_and_empty_guards() {
    for source in [
        include_str!("../../../lean/examples/finite_fold_guarded/statement.lit"),
        include_str!("../../../lean/examples/finite_fold_guarded_literal/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        assert!(compiler.compile_run(&run, "finite_fold_guard").is_ok());
    }
}

#[test]
fn ordered_fold_rejects_missing_or_reordered_literal_guards() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) =
            super::execute("$is_set(reduce(1,3,fn(k Z: k != 0) Z{k},fn(a,b Z) Z{a+b},0))");
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::IteratedOperator(
                    IteratedOperatorObjWellDefinedProofByDef::Reduce(wd),
                ),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("fold WD");
        };
        if missing {
            wd.requirement_fact_verified.pop();
        } else {
            wd.requirement_fact_verified.swap(5, 6);
        }
        assert!(compiler.compile_run(&run, "changed_ordered_guard").is_err());
    }
}

#[test]
fn finite_fold_rejects_missing_or_reordered_literal_guards() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(
            "$is_set(finite_set_reduce({1,2},fn(k Z: k != 0) Z{k},fn(a,b Z) Z{a+b},0))",
        );
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::IteratedOperator(
                    IteratedOperatorObjWellDefinedProofByDef::FiniteSetReduce(wd),
                ),
            ..
        } = &mut atom.well_defined_proof.well_defined_of_each_parameter[0]
        else {
            panic!("fold WD");
        };
        if missing {
            wd.requirement_fact_verified.pop();
        } else {
            wd.requirement_fact_verified.swap(5, 6);
        }
        assert!(compiler.compile_run(&run, "changed_finite_guard").is_err());
    }
}

#[test]
fn ordered_fold_last_step_rejects_changed_endpoint_certificate() {
    let (mut run, compiler) = super::execute(include_str!(
        "../../../lean/examples/ordered_fold_last_step/statement.lit"
    ));
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let equality = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ReduceLastStep(
        proof,
    )) = &mut equality.searched_proof
    else {
        panic!("last step");
    };
    let endpoint = super::equality_proof_mut(&mut proof.endpoint);
    endpoint.fact.right = Obj::Literal(Literal::Number(Number::new("99".into())));
    assert!(compiler.compile_run(&run, "changed_last_endpoint").is_err());
}

#[test]
fn ordered_fold_rejects_unbridged_positive_numeric_signature() {
    let (run, compiler) = super::execute(
        "forall f fn(k Z) R+, op fn(a,b R+) R+, s R+:\n    reduce(1,2,f,op,s) $in R+\n",
    );
    let error = compiler
        .compile_run(&run, "positive_fold_signature")
        .unwrap_err();
    assert!(error.to_string().contains("PositiveNumericSignature"));
}

#[test]
fn fold_detailed_result_publishes_both_original_signature_selections() {
    use crate::knowledge_base::JsonValue;
    fn find(value: &JsonValue) -> Option<(&JsonValue, &JsonValue)> {
        match value {
            JsonValue::Object(fields) => {
                if let (Some(op), Some(f)) = (
                    fields.get("operation_signature_selection"),
                    fields.get("iterand_signature_selection"),
                ) {
                    return Some((op, f));
                }
                fields.iter().find_map(|(_, value)| find(value))
            }
            JsonValue::Array(values) => values.iter().find_map(find),
            _ => None,
        }
    }
    let (run, compiler) = super::execute("$is_set(reduce(1,2,fn(k Z) Z{k},fn(a,b Z) Z{a+b},0))");
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &compiler.runtime);
    let (op, f) = find(&json).expect("detailed fold selections");
    assert!(matches!(op, JsonValue::Object(_)));
    assert!(matches!(f, JsonValue::Object(_)));
    assert_ne!(
        op, f,
        "the binary operation and unary iterand retain distinct signatures"
    );
}
