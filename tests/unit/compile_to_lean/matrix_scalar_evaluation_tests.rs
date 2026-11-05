use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Evaluate diagonal sums, then use a computed trace in a guarded reciprocal.
have fn diagonal_sum_matrix(r,c closed_range(1,2)) R = r + c

trace(diagonal_sum_matrix,2) = 6

have fn reciprocal_score(x R: x != 0) R = 1 / x

reciprocal_score(trace(diagonal_sum_matrix,2)) = 1/6

have fn trace_eval_matrix(r,c closed_range(1,2)) R = 2 * r

eval trace(trace_eval_matrix,2)
"#,
    r#"# Evaluate finite real inner products, including conjugation and recorded coordinate calls.
have fn component_vector(k closed_range(1,2)) R = k

inner_product(component_vector,component_vector,2) = 5

have fn inner_eval_vector(k closed_range(1,2)) R = k + 1

eval inner_product(inner_eval_vector,inner_eval_vector,2)
"#,
    r#"# Evaluate two by two Frobenius norms through their nested finite sums.
have fn unit_matrix(r,c closed_range(1,2)) R = 1

frobenius_norm(unit_matrix,2,2) = 2

have fn norm_eval_matrix(r,c closed_range(1,2)) R = 2

eval frobenius_norm(norm_eval_matrix,2,2)
"#,
    r#"# Evaluate Euclidean norms of positive and negative components through square-modulus sums.
have fn three_vector(k closed_range(1,1)) R = 3

euclidean_norm(three_vector,1) = 3

have fn norm_eval_vector(k closed_range(1,1)) R = -4

eval euclidean_norm(norm_eval_vector,1)
"#,
];

fn eval(run: &mut RunLitexCodeResult) -> &mut ExecEvalStmtSuccess {
    run.statement_results
        .iter_mut()
        .find_map(|s| match s {
            ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(
                p,
            ))) => Some(p),
            _ => None,
        })
        .expect("original eval result")
}
fn number(s: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(s.into())))
}

#[test]
fn matrix_scalar_evaluation_requires_ordered_terms_and_complete_enumerations() {
    for source in SOURCES {
        for mutation in 0..7 {
            let (mut run, compiler) = super::execute(source);
            let p = eval(&mut run);
            let AggregateEvaluationResult::SumOfFiniteSet(sum) =
                p.aggregate_evaluations.last_mut().unwrap()
            else {
                panic!("original finite sum");
            };
            assert!(!sum.terms.is_empty());
            match mutation {
                0 => {
                    sum.terms.pop();
                }
                1 => {
                    sum.enumeration.elements.pop();
                }
                2 => sum.enumeration.elements[0] = number("99"),
                3 => sum.terms[0].argument = number("99"),
                4 => sum.terms[0].value = number("99"),
                5 => sum.terms[0].accumulated_value = number("99"),
                _ => sum.terms[0].nested_aggregate_evidence = 999..1000,
            }
            compiler
                .compile_run(&run, "bad_matrix_scalar_term")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn matrix_scalar_evaluation_requires_original_nested_calls_and_matrix_expansion() {
    for source in SOURCES {
        for mutation in 0..6 {
            let (mut run, compiler) = super::execute(source);
            let p = eval(&mut run);
            match mutation {
                0 => {
                    p.function_evaluations
                        .pop()
                        .expect("original coordinate call");
                }
                1 => p.function_evaluations[0].value = number("99"),
                2 => p.function_evaluations[0].application = number("99"),
                3 => p.matrix_scalar_evaluations[0].expression = number("99"),
                4 => p.matrix_scalar_evaluations[0].value = number("99"),
                _ => {
                    p.matrix_scalar_evaluations.clear();
                }
            }
            compiler
                .compile_run(&run, "bad_matrix_scalar_evaluation")
                .expect_err(&format!("mutation {mutation}"));
        }
    }
}

#[test]
fn matrix_scalar_guarded_reuse_requires_original_beta_and_operand_proofs() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
            by_parent_checked_beta::ByParentCheckedBetaObjectDefinitionProof},
    };
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let fact = super::fact_statement_mut(&mut run.statement_results[3]);
        let equal = super::equality_proof_mut(&mut fact.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                    ByParentCheckedBetaObjectDefinitionProof::OneSide(beta),
                ),
            ),
        ) = &mut equal.searched_proof
        else {
            panic!("original guarded beta");
        };
        let EqualFactSearchedProof::ByMatchingOneArgByOne(congruence) =
            beta.residual_proof.as_mut()
        else {
            panic!("original arithmetic congruence");
        };
        match mutation {
            0 => congruence.corresponding_arg_equal_proofs.clear(),
            1 => congruence.corresponding_arg_equal_proofs.swap(0, 1),
            2 => beta.expanded_body = number("99"),
            _ => beta.residual_equal.left = number("99"),
        }
        compiler
            .compile_run(&run, "bad_guarded_scalar_reuse")
            .expect_err(&format!("mutation {mutation}"));
    }
}
