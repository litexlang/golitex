use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnObjWellDefinedProof, ArithmeticOperatorObjWellDefinedProofByDef,
    FunctionSpaceObjWellDefinedProofByDef,
};
use crate::execute::{ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Construct real functions recursively, adding one to the previous function.
have fn translated_functions(n N) fn(x R) R by induc n from 0:
    case n = 0: fn(x R) R {x}
    case n > 0: fn(x R) R {translated_functions(n - 1)(x) + 1}

translated_functions(0) = fn(x R) R {x}
translated_functions(1) = fn(x R) R {translated_functions(1 - 1)(x) + 1}
"#,
    r#"# Build successive sums of the reciprocal function on its nonzero domain.
have fn inverse_translates(n N) fn(x R: x != 0) R by induc n from 0:
    case n = 0: fn(x R: x != 0) R {1 / x}
    case n > 0: fn(x R: x != 0) R {inverse_translates(n - 1)(x) + 1 / x}

inverse_translates(0) = fn(x R: x != 0) R {1 / x}
"#,
    r#"# Construct binary real functions recursively, starting from addition.
have fn binary_translates(n N) fn(x, y R) R by induc n from 0:
    case n = 0: fn(x, y R) R {x + y}
    case n > 0: fn(x, y R) R {binary_translates(n - 1)(x, y) + 1}
"#,
    r#"# Capture the translation step in a recursive family of real functions.
template<step R>:
    have fn translated_by(n N) fn(x R) R by induc n from 0:
        case n = 0: fn(x R) R {x}
        case n > 0: fn(x R) R {translated_by(n - 1)(x) + step}

\translated_by<2>(0) = fn(x R) R {x}
"#,
    r#"# Recursively reuse the identity function on an arbitrary set.
have U set
have fn recursive_identities(n N) fn(x U) U by induc n from 0:
    case n = 0: fn(x U) U {x}
    case n > 0: fn(x U) U {recursive_identities(n - 1)(x)}

recursive_identities(1) $in fn(x U) U
"#,
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
