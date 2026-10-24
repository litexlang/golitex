use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::{
    ExecHaveFnEqualCaseByCaseStmtResult, ExecHaveFnEqualCaseByCaseStmtSuccessResult,
};
use crate::prelude::*;

const ABS: &str = "have fn absolute(x R) R by cases:\n    case x >= 0: x\n    case x < 0: -x\nabsolute(-2) = 2\nabsolute(3) = 3\n";

fn declaration(run: &mut RunLitexCodeResult) -> &mut ExecHaveFnEqualCaseByCaseStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
        ExecHaveFnEqualCaseByCaseStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("case definition")
    };
    p
}

#[test]
fn piecewise_function_replays_declaration_and_selected_call() {
    let (run, compiler) = super::execute(ABS);
    let lean = compiler.compile_run(&run, "piecewise").unwrap();
    assert!(lean.contains("Litex.piecewiseFn "));
    assert!(lean.contains("Litex.piecewiseFn_call_eq"));
    assert!(lean.contains("_checked_case_guard"));
    assert!(!lean.contains("sorry"));
    assert_eq!(lean, compiler.compile_run(&run, "piecewise").unwrap());
    assert!(lean.len() < 100_000);
}

#[test]
fn piecewise_function_rejects_changed_declaration_evidence() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(ABS);
        let p = declaration(&mut run);
        match mutation {
            0 => p.statement.cases.swap(0, 1),
            1 => p.statement.equal_tos.swap(0, 1),
            2 => {
                p.disjoint.clear();
            }
            3 => p.case_return_checks[0].case_index = 1,
            4 => p.store_and_infer_result.case_defining_fact_ids.swap(0, 1),
            5 => {
                p.case_return_checks[0]
                    .binder_introduction
                    .defined_params
                    .store_and_infer_results
                    .clear();
            }
            6 => {
                let StoreFactResult::ForallFact(f) =
                    &mut p.store_and_infer_result.case_defining[0].store
                else {
                    panic!()
                };
                f.fact.dom_facts.clear();
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "mutated").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn piecewise_function_keeps_private_binders_out_of_published_scope() {
    let (mut run, compiler) = super::execute(ABS);
    let p = declaration(&mut run);
    let name = p.statement.name.id;
    let published = p.store_and_infer_result.stored_fact_ids.clone();
    let private = p
        .case_return_checks
        .iter()
        .flat_map(|p| p.binder_introduction.defined_params.stored_fact_ids.clone())
        .collect::<Vec<_>>();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(before.visible_piecewise_function(&name).is_err());
    assert!(after.visible_piecewise_function(&name).is_ok());
    for id in published {
        assert!(compiler.cited_fact_reference(id, &before).is_err());
        assert!(compiler.cited_fact_reference(id, &after).is_ok());
    }
    for id in private {
        assert!(compiler.cited_fact_reference(id, &after).is_err());
    }
}

#[test]
fn piecewise_function_rejects_invalid_source_domains() {
    for source in [
        "have fn f(x R) R by cases:\n    case x > 0: x\n    case x < 0: -x\n",
        "have fn f(x R) R by cases:\n    case x >= 0: x\n    case x <= 0: -x\n",
        "have fn f(x R) R by cases:\n    case x = 0: 1 / x\n    case x != 0: x\n",
        "have fn f(x R) N by cases:\n    case x >= 0: x\n    case x < 0: -x\n",
    ] {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
    }
}

#[test]
fn piecewise_call_retains_and_validates_the_original_branch_guard() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::EqualitySearchProofByObjectDefinition;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::EqualitySearchProofByFnApplicationObjectDefinition;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(ABS);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &mut run.statement_results[1]
        else {
            panic!()
        };
        let VerifyFactResult::Equality(result) = &mut stmt.verify_result else {
            panic!()
        };
        let VerifyEqualityResult::Success(result) = result.as_mut() else {
            panic!()
        };
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqualCaseByCase(p),
            ),
        ) = &mut result.searched_proof
        else {
            panic!("actual case unfold route")
        };
        assert_eq!(p.matched_case_index, 1);
        assert!(matches!(
            &p.guard,
            VerifyFactResult::AtomicExceptEquality(_)
        ));
        match mutation {
            0 => p.matched_case_index = 0,
            1 => p.expanded_body = Obj::StandardSet(StandardSet::R),
            2 => std::mem::swap(&mut p.guard, &mut p.residual_equal),
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_call").is_err());
    }
}

#[test]
fn piecewise_function_examples_compile_with_original_domains() {
    for source in [
        include_str!("../../../lean/examples/piecewise_total_reciprocal/statement.lit"),
        include_str!("../../../lean/examples/piecewise_larger_value/statement.lit"),
        include_str!("../../../lean/examples/piecewise_inverse_magnitude/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "piecewise_cases").unwrap();
        assert_eq!(
            output,
            compiler.compile_run(&run, "piecewise_cases").unwrap()
        );
        assert!(output.contains("Litex.piecewiseFn_call_eq"));
        assert!(output.len() < 200_000);
    }
}
