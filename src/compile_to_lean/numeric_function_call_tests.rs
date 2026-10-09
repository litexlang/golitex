use super::source_position::{SourceOwner, SourcePosition};
use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("typed source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn actual_call_wd(
    result: &RunLitexCodeResult,
) -> (
    &VerifyFactResult,
    &AtomicFactWellDefinedProof,
    &ObjWellDefinedProof,
) {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &result.statement_results[0]
    else {
        panic!("source call sethood");
    };
    let VerifyFactResult::AtomicExceptEquality(atomic) = &statement.verify_result else {
        panic!("atomic call formation");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(atomic) = atomic.as_ref() else {
        panic!("successful call formation");
    };
    (
        &statement.verify_result,
        &atomic.well_defined_proof,
        &atomic.well_defined_proof.well_defined_of_each_parameter[0],
    )
}

#[test]
fn numeric_function_call_observation_uses_original_numeric_return_hierarchy() {
    for (set, inclusion) in [
        ("N", "Litex.naturalToComplex"),
        ("Z", "Litex.integerToComplex"),
        ("Q", "Litex.rationalToComplex"),
        ("R", "Litex.realToComplex"),
        ("C", "Litex.callInOutput"),
    ] {
        let source = format!("$is_set(fn(x R) {set} {{1}}(2))");
        let (result, compiler) = checked(&source);
        let (verify, atomic, wd) = actual_call_wd(&result);
        let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
        let statement = SourcePosition::new(
            Some(&run),
            SourceOwner::Statement(&result.statement_results[0]),
            0,
        );
        let verify = SourcePosition::new(Some(&statement), SourceOwner::Verify(verify), 0);
        let atomic = SourcePosition::new(Some(&verify), SourceOwner::AtomicWD(atomic), 0);
        // The current call has not become a visible completed constructor. Its
        // own evidence must be reconstructed directly, rather than looked up.
        let observation = compiler
            .numeric_wd(wd, &atomic)
            .expect("direct certified call observation");
        assert!(observation.0.contains("Litex.NativeBridge.asComplex"));
        assert!(observation.1.contains("Litex.NativeBridge.asComplex_spec"));
        assert!(
            observation.2.contains(inclusion),
            "{set}: {}",
            observation.2
        );
        assert!(observation.2.contains("Litex.callInOutput"));
        assert!(
            observation.3.is_none(),
            "numeric membership does not record a closed evaluation certificate"
        );
    }
}

#[test]
fn numeric_function_call_real_certificate_needs_a_recorded_real_return_upper_bound() {
    for (set, inclusion) in [
        ("N", "Litex.naturalToReal"),
        ("Z", "Litex.integerToReal"),
        ("Q", "Litex.rationalToReal"),
        ("R", "Litex.callInOutput"),
        ("C", ""),
    ] {
        let (result, compiler) = checked(&format!("$is_set(fn(x R) {set} {{1}}(2))"));
        let (verify, _, wd) = actual_call_wd(&result);
        let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
        let statement = SourcePosition::new(
            Some(&run),
            SourceOwner::Statement(&result.statement_results[0]),
            0,
        );
        let formed = SourcePosition::new(Some(&statement), SourceOwner::Verify(verify), usize::MAX);
        let certificate = compiler.compile_real_membership_certificate(wd.obj(), &formed);
        if set == "C" {
            assert_eq!(
                certificate.unwrap_err().route,
                "Real/Producer",
                "the formula happens to be real, but this source only certified its C return"
            );
        } else {
            assert!(certificate.unwrap().contains(inclusion), "{set}");
        }
    }
}

#[test]
fn numeric_simultaneous_function_call_keeps_its_binary_output_law() {
    let (result, compiler) = checked("$is_set(fn(x R, y R) R {1}(3, 2))");
    let (verify, atomic, wd) = actual_call_wd(&result);
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let statement = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[0]),
        0,
    );
    let verify = SourcePosition::new(Some(&statement), SourceOwner::Verify(verify), 0);
    let atomic = SourcePosition::new(Some(&verify), SourceOwner::AtomicWD(atomic), 0);
    let observation = compiler
        .numeric_wd(wd, &atomic)
        .expect("actual binary constructor");
    assert!(observation.2.contains("Litex.call2InOutput"));
    assert!(observation.2.contains("Litex.realToComplex"));
}

#[test]
fn numeric_cached_call_alias_uses_a_preceding_constructor_for_real_arithmetic() {
    let (result, compiler) = checked("have fn numeric_shift(x R) R = x + 1\n$is_set(numeric_shift(2))\nlet numeric_result = numeric_shift(2)\nnumeric_result + 0 = numeric_result");
    let output = compiler
        .compile_run(&result, "numeric_cached_call")
        .expect("cached call alias with its original real return law");
    assert!(output.contains("Litex.NativeBridge.asComplex_spec"));
    assert!(output.contains("Litex.callInOutput"));
    assert!(output.contains("Litex.realToComplex"));
}

#[test]
fn numeric_call_observation_rejects_a_forged_selected_return() {
    let (mut result, compiler) = checked("$is_set(fn(x R) R {1}(2))");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[0]
    else {
        panic!("source call sethood");
    };
    let VerifyFactResult::AtomicExceptEquality(atomic) = &mut statement.verify_result else {
        panic!("atomic call formation");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(atomic) = atomic.as_mut() else {
        panic!("successful call formation");
    };
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = &mut atomic.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("actual call constructor");
    };
    let Some(FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }) = &mut call.domain_fn_set
    else {
        panic!("actual literal signature");
    };
    fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    let (verify, atomic, wd) = actual_call_wd(&result);
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let statement = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[0]),
        0,
    );
    let verify = SourcePosition::new(Some(&statement), SourceOwner::Verify(verify), 0);
    let atomic = SourcePosition::new(Some(&verify), SourceOwner::AtomicWD(atomic), 0);
    assert_eq!(
        compiler.numeric_wd(wd, &atomic).unwrap_err().route,
        "WD/FnObj/Signature"
    );
}
