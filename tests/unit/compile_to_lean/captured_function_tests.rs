use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::AnonymousFnObjWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
    EqualitySearchProofByObjectDefinition,
    by_fn_application::{
        EqualitySearchProofByFnApplicationObjectDefinition,
        normalize_function_body::{AnonymousFunctionBodyExpansionProof, FunctionBodyExpansionProof},
    },
};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;
use std::collections::HashMap;

const BETA: &str = "have fn shifted_by(t R) fn(x R) R = fn(x R) R {x + t}\nhave captured_a R\nshifted_by(captured_a) = fn(x R) R {x + captured_a}\n";

fn definition(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecHaveFnEqualStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(p),
    )) = &mut run.statement_results[index]
    else {
        panic!("function declaration")
    };
    p
}

fn anonymous(wd: &mut ObjWellDefinedProof) -> &mut AnonymousFnObjWellDefinedProof {
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                p,
            )),
        ..
    } = wd
    else {
        panic!("original literal WD")
    };
    p
}

fn expansion(statement: &mut ExecStmtResult) -> &mut AnonymousFunctionBodyExpansionProof {
    let proof = super::equality_proof_mut(&mut super::fact_statement_mut(statement).verify_result);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::HaveFnEqual(p),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("recorded beta route")
    };
    let FunctionBodyExpansionProof::Anonymous(p) = &mut p.normalization.expansions[0] else {
        panic!("literal beta")
    };
    p
}

#[test]
fn captured_function_examples_replay_deterministically() {
    for source in [
        include_str!("../../../lean/examples/captured_shift_functions/statement.lit"),
        include_str!("../../../lean/examples/captured_division_functions/statement.lit"),
        include_str!("../../../lean/examples/captured_binary_functions/statement.lit"),
        include_str!("../../../lean/examples/nested_function_application/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "captured").unwrap();
        assert_eq!(lean, compiler.compile_run(&run, "captured").unwrap());
    }
}

#[test]
fn captured_beta_rejects_changed_signature_body_and_local_binder() {
    for change in 0..5 {
        let (mut run, compiler) = super::execute(BETA);
        let step = expansion(&mut run.statement_results[2]);
        let Obj::FnObj(call) = &step.application else {
            panic!()
        };
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = call.body[0][0].as_ref() else {
            panic!()
        };
        let caller = *id;
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &mut step.expanded_body else {
            panic!()
        };
        match change {
            0 => f.body.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            1 => {
                f.body.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::Z))
            }
            2 => f.body.set_bound_parameters.groups[0].params[0].id = caller,
            3 => f.body.set_bound_parameters.groups[0].params.clear(),
            4 => f.equal_to = Box::new(super::number_object("7")),
            _ => unreachable!(),
        }
        step.continued_body = step.expanded_body.clone();
        assert_eq!(
            compiler.compile_run(&run, "wrong_beta").unwrap_err().route,
            "FunctionDefinition/Substitution"
        );
    }
}

#[test]
fn captured_function_requires_outer_and_inner_original_guards() {
    for inner in [false, true] {
        let source =
            include_str!("../../../lean/examples/captured_division_functions/statement.lit");
        let (mut run, compiler) = super::execute(source);
        let VerifyObjWellDefinedResult::Success(wd) =
            &mut definition(&mut run, if inner { 2 } else { 0 }).anonymous_fn_well_defined
        else {
            panic!()
        };
        let outer = anonymous(wd);
        if inner {
            anonymous(&mut outer.body_well_defined)
                .assumed_dom_facts
                .clear();
        } else {
            outer.assumed_dom_facts.clear();
        }
        assert!(compiler.compile_run(&run, "missing_guard").is_err());
    }
}

#[test]
fn captured_function_rejects_binder_collisions_and_dependent_carriers() {
    for carrier in [false, true] {
        let (mut run, compiler) = super::execute(BETA);
        let outer = &definition(&mut run, 0).statement.equal_to_anonymous_fn;
        let parameter = &outer.body.set_bound_parameters.groups[0].params[0];
        let bindings = HashMap::from([(parameter.id, "_outer".to_string())]);
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(mut inner)) = *outer.equal_to.clone()
        else {
            panic!()
        };
        if carrier {
            inner.body.ret_set =
                Box::new(Obj::Identifier(IdentifierObj::from_bound_name(parameter)));
        } else {
            inner.body.set_bound_parameters.groups[0].params[0].id = parameter.id;
        }
        let position = SourcePosition::new(None, SourceOwner::Run(&run), 0);
        let error = compiler
            .compile_function_literal_value(&inner, &position, &bindings)
            .unwrap_err();
        assert_eq!(
            error.route,
            if carrier {
                "Function/CapturedSignatureCarrier"
            } else {
                "Function/CaptureBinderIdentity"
            }
        );
    }
}

#[test]
fn captured_function_beta_rejects_unrecorded_continuations() {
    let (mut run, compiler) = super::execute(BETA);
    let step = expansion(&mut run.statement_results[2]);
    step.continued_body = super::number_object("7");
    assert_eq!(
        compiler
            .compile_run(&run, "wrong_continuation")
            .unwrap_err()
            .route,
        "FunctionDefinition/Continuation"
    );
}

#[test]
fn captured_function_continuations_preserve_later_arguments() {
    for missing in [false, true] {
        let source = format!("{BETA}shifted_by(captured_a)(2) = 2 + captured_a\n");
        let (mut run, compiler) = super::execute(&source);
        let step = expansion(&mut run.statement_results[3]);
        if missing {
            step.continued_body = step.expanded_body.clone();
        } else {
            let Obj::FnObj(call) = &mut step.continued_body else {
                panic!("remaining call")
            };
            call.body[0][0] = Box::new(super::number_object("7"));
        }
        assert_eq!(
            compiler
                .compile_run(&run, "wrong_later_argument")
                .unwrap_err()
                .route,
            "FunctionDefinition/Continuation"
        );
    }
}
