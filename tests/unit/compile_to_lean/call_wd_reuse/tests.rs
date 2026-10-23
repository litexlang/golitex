use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnObjDomainFnSetEvidence, FnObjObjWellDefinedProof, PowObjWellDefinedProof,
};
use crate::prelude::*;

const SOURCE: &str =
    "have fn wd_shift(x R) R = x + 1\nforall x R:\n    wd_shift(x) ^ 2 = wd_shift(x) ^ 2\n";
const GUARDED: &str = "have fn reciprocal(x R: x != 0) R = 1 / x\nforall x R:\n    x != 0\n    =>:\n        reciprocal(x) ^ 2 = reciprocal(x) ^ 2\n";

fn power(result: &mut RunLitexCodeResult) -> &mut ObjWellDefinedProof {
    let forall = super::forall_proof_mut(&mut result.statement_results[1]);
    &mut super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result)
        .well_defined_proof
        .left
}

fn parts(proof: &mut ObjWellDefinedProof) -> &mut PowObjWellDefinedProof {
    match proof {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
                ),
            ..
        } => p,
        _ => panic!("power constructor"),
    }
}

fn requirement_call(proof: &mut ObjWellDefinedProof) -> &mut FnObjObjWellDefinedProof {
    let VerifyFactResult::AtomicExceptEquality(result) =
        &mut parts(proof).requirement_fact_verified[0]
    else {
        panic!("membership")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_mut() else {
        panic!("successful membership")
    };
    match &mut result.well_defined_proof.well_defined_of_each_parameter[0] {
        ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } => call,
        _ => panic!("separately checked call"),
    }
}

#[test]
fn arithmetic_membership_reuses_completed_call_after_validation() {
    for source in [SOURCE, GUARDED] {
        let (result, compiler) = super::execute(source);
        let output = compiler.compile_run(&result, "call_sharing").unwrap();
        assert_eq!(output.matches("Litex.call ").count(), 2, "{output}");
        assert!(output.contains("let _atomic_wd_1_0 := _wd_"));
        assert!(output.contains("let _litex_return_call := _atomic_wd_"));
    }
}

#[test]
fn repeated_call_still_validates_its_own_membership_and_guard() {
    for guard in [false, true] {
        let (mut result, compiler) = super::execute(GUARDED);
        let call = requirement_call(power(&mut result));
        if guard {
            call.requirement_fact_verified.pop();
        } else {
            call.requirement_fact_verified.remove(0);
        }
        assert!(compiler.compile_run(&result, "bad_domain").is_err());
    }
}

#[test]
fn call_alias_is_unavailable_before_its_constructor_completes() {
    let (mut result, _) = super::execute(SOURCE);
    let root = power(&mut result);
    // Take the separately checked occurrence out of the requirement while
    // keeping the completed original child for the borrowed-position check.
    let requirement = parts(root).requirement_fact_verified.remove(0);
    let VerifyFactResult::AtomicExceptEquality(r) = requirement else {
        panic!("membership")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(r) = *r else {
        panic!("success")
    };
    let ObjWellDefinedProof::ByDef {
        obj: Obj::FnObj(application),
        proof: ObjWellDefinedProofByDef::FnObj(call),
    } = &r.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("call")
    };
    let before = SourcePosition::new(None, SourceOwner::WDLocals(root, 0), 0);
    assert!(before.bound_compatible_fn_call(application, call).is_none());
    let after = SourcePosition::new(None, SourceOwner::WDLocals(root, 1), 0);
    assert!(after.bound_compatible_fn_call(application, call).is_some());
}

#[test]
fn alternative_signature_is_not_a_compatible_constructor() {
    let (mut result, _) = super::execute(SOURCE);
    let root = power(&mut result);
    let requirement = parts(root).requirement_fact_verified.remove(0);
    let VerifyFactResult::AtomicExceptEquality(r) = requirement else {
        panic!("membership")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(mut r) = *r else {
        panic!("success")
    };
    let ObjWellDefinedProof::ByDef {
        obj: Obj::FnObj(application),
        proof: ObjWellDefinedProofByDef::FnObj(call),
    } = &mut r.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("call")
    };
    let Some(FnObjDomainFnSetEvidence::InFunctionSet { fact_id, .. }) = &mut call.domain_fn_set
    else {
        panic!("signature")
    };
    *fact_id = FactId::new(u64::MAX);
    let position = SourcePosition::new(None, SourceOwner::WDLocals(root, 1), 0);
    assert!(position
        .bound_compatible_fn_call(application, call)
        .is_none());
}
