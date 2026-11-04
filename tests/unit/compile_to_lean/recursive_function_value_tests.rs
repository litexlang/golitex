use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnObjWellDefinedProof, ArithmeticOperatorObjWellDefinedProofByDef,
    FunctionSpaceObjWellDefinedProofByDef,
};
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/recursive_function_translation/statement.lit"),
    include_str!("../../../lean/examples/recursive_guarded_functions/statement.lit"),
    include_str!("../../../lean/examples/recursive_binary_functions/statement.lit"),
    include_str!("../../../lean/examples/template_recursive_functions/statement.lit"),
    include_str!("../../../lean/examples/recursive_functions_on_set/statement.lit"),
];

fn recursive(run: &mut RunLitexCodeResult) -> &mut ExecHaveFnByInducStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
        ExecHaveFnByInducStmtResult::Success(body),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    body
}

fn step_literal(
    body: &mut ExecHaveFnByInducStmtSuccessResult,
) -> &mut AnonymousFnObjWellDefinedProof {
    let crate::execute::InducCaseBodySuccess::EqualTo { well_defined, .. } =
        &mut body.case_checks.cases[1].body
    else {
        panic!()
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                wd,
            )),
        ..
    }) = well_defined.as_detailed_success_mut().unwrap()
    else {
        panic!()
    };
    wd
}

#[test]
fn recursive_function_values_replay_literals_and_curried_calls() {
    for source in SOURCES {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "recursive_function_values")
            .expect(source);
        assert!(output.contains("Litex.functionGraphValueCongr"));
        assert!(output.contains("Litex.recursiveFn_equation"));
        assert_eq!(
            output,
            compiler
                .compile_run(&run, "recursive_function_values")
                .unwrap()
        );
    }
}

#[test]
fn recursive_function_values_require_inner_binders_guards_and_all_call_stages() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(SOURCES[1]);
        compiler.compile_run(&run, "intact_inner_evidence").unwrap();
        let declaration = recursive(&mut run);
        let completed_member = declaration.store_and_infer_result.membership_fact_id;
        let literal = step_literal(declaration);
        match mutation {
            0 => literal.defined_params.store_and_infer_results.clear(),
            1 => literal.assumed_dom_facts.clear(),
            _ => {
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::ArithmeticOperator(
                            ArithmeticOperatorObjWellDefinedProofByDef::Add(add),
                        ),
                    ..
                } = literal.body_well_defined.as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                    ..
                } = add.child_obj_well_defined[0].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                match mutation {
                    2 => call.child_obj_well_defined.clear(),
                    3 => {
                        call.requirement_fact_verified.pop();
                    }
                    4 => call.requirement_fact_verified.swap(1, 2),
                    5 => call.requirement_fact_verified.swap(0, 3),
                    _ => {
                        let Some(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence::InFunctionSet {fact_id, ..}) = &mut call.domain_fn_set else {panic!()};
                        *fact_id = completed_member;
                    }
                }
            }
        }
        compiler
            .compile_run(&run, "changed_inner_evidence")
            .expect_err("only the original literal and restricted call evidence is reusable");
    }
}

#[test]
fn recursive_function_literal_captures_only_the_already_introduced_self() {
    let (mut run, _) = super::execute(SOURCES[0]);
    let declaration = recursive(&mut run);
    let id = declaration.statement.name.id;
    let before = SourcePosition::new(None, SourceOwner::RecursiveFunction(declaration), 6);
    assert!(before.visible_recursive_self(&id).is_err());
    let introduced = SourcePosition {
        before: 7,
        ..before
    };
    assert!(introduced.visible_recursive_self(&id).is_ok());
    let outer = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(outer.visible_recursive_self(&id).is_err());
}
