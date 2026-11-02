use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/matrix_trace_evaluation/statement.lit"),
    include_str!("../../../lean/examples/finite_inner_product_evaluation/statement.lit"),
    include_str!("../../../lean/examples/frobenius_norm_evaluation/statement.lit"),
    include_str!("../../../lean/examples/euclidean_norm_evaluation/statement.lit"),
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
fn matrix_scalar_evaluation_replays_nonempty_terms_and_guarded_reuse() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let generated = compiler
            .compile_run(&run, "matrix_scalar_evaluation")
            .expect(source);
        assert_eq!(
            generated,
            compiler
                .compile_run(&run, "matrix_scalar_evaluation")
                .unwrap()
        );
        assert!(generated.contains("finiteAggregateValueList"));
    }
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
