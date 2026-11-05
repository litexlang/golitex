use crate::prelude::*;

#[test]
fn ordered_fold_rejects_missing_signature_capture() {
    let (mut run, compiler) =
        super::execute("$is_set(reduce(1,3,fn(k Z) Z{k},fn(a,b Z) Z{a+b},0))");
    let p = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
    );
    let DetailedObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::IteratedOperator(
        crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef::Reduce(wd)), .. } = (&mut p.well_defined_proof.as_detailed_mut().unwrap().well_defined_of_each_parameter[0]).as_detailed_mut().unwrap() else { panic!("fold WD"); };
    assert!(wd.operation_signature_selection.is_some() && wd.iterand_signature_selection.is_some());
    wd.iterand_signature_selection = None;
    assert!(compiler
        .compile_run(&run, "missing_fold_signature")
        .is_err());
}

#[test]
fn ordered_fold_calculation_rejects_changed_certificates() {
    use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
        AggregateEvaluationResult, FunctionApplicationExpansionProof,
    };
    for changed in 0..6 {
        let (mut run, compiler) = super::execute(
            r#"# An ordered left fold subtracts 1, then 2, then 3 from zero.
reduce(1,3,fn(k Z) Z{k},fn(a,b Z) Z{a-b},0) = -6
"#,
        );
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
fn ordered_fold_rejects_missing_or_reordered_literal_guards() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef;
    for missing in [false, true] {
        let (mut run, compiler) =
            super::execute("$is_set(reduce(1,3,fn(k Z: k != 0) Z{k},fn(a,b Z) Z{a+b},0))");
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::IteratedOperator(
                    IteratedOperatorObjWellDefinedProofByDef::Reduce(wd),
                ),
            ..
        } = (&mut atom
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
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
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::IteratedOperator(
                    IteratedOperatorObjWellDefinedProofByDef::FiniteSetReduce(wd),
                ),
            ..
        } = (&mut atom
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
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
    let (mut run, compiler) = super::execute(
        r#"# A nonempty ordered fold performs its last call after folding the preceding indices.
forall a,b Z, E set, f fn(k Z) E, op fn(x,y E) E, s E:
    a <= b
    =>:
        reduce(a,b,f,op,s) = op(reduce(a,b-1,f,op,s),f(b))
"#,
    );
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

#[test]
fn range_input_coverage_fold_rejects_missing_or_changed_start_proof() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IteratedOperatorObjWellDefinedProofByDef as P;
    for missing in [false, true] {
        let (mut run, compiler) =
            super::execute("$is_set(reduce(1,3,fn(k R+) R{k},fn(a,b R) R{a+b},0))");
        let atom = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IteratedOperator(P::Reduce(wd)),
            ..
        } = atom
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0]
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("fold WD")
        };
        if missing {
            wd.requirement_fact_verified.remove(3);
        } else {
            let proof = super::atomic_proof_mut(&mut wd.requirement_fact_verified[3]);
            let AtomicFact::InFact(f) = &mut proof.fact else {
                panic!("positive membership")
            };
            f.set = Obj::StandardSet(StandardSet::N);
        }
        compiler
            .compile_run(&run, "wrong_fold_range_input")
            .expect_err("the original positive-start certificate must be retained");
    }
}
