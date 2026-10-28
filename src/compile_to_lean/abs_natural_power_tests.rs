use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AbsObjWellDefinedProof, PowObjWellDefinedProof,
};
use crate::prelude::*;

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn abs_mut(result: &mut RunLitexCodeResult) -> &mut AbsObjWellDefinedProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[0]
    else {
        panic!("actual sethood statement")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut fact.verify_result else {
        panic!("actual sethood proof")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Abs(abs),
            ),
        ..
    } = (&mut proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0])
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("original owned abs constructor")
    };
    abs
}

fn pow_mut(result: &mut RunLitexCodeResult) -> &mut PowObjWellDefinedProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[1]
    else {
        panic!("actual power statement")
    };
    let VerifyFactResult::Equality(proof) = &mut fact.verify_result else {
        panic!("actual power equality")
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Pow(pow),
            ),
        ..
    } = (&mut proof.well_defined_proof.as_detailed_mut().unwrap().left)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("original owned power constructor")
    };
    pow
}

#[test]
fn real_abs_wd_observation_closed_calculation_and_nonnegative_identity_replay() {
    let source = "$is_set(|-2|)\n|-2|=2\n|1 / 2|=1 / 2\nforall x R:\n    0 <= |x|\nclaim:\n    ? forall x R:\n        0 <= x\n        =>:\n            |x|=x\n    |x|=x\n";
    let (result, compiler) = checked(source);
    let lean = compiler
        .compile_run(&result, "real_abs_replay")
        .expect("original absolute-value routes");
    assert!(lean.contains("Litex.abs"));
    assert!(lean.contains("Litex.NativeBridge.denoteAbs"));
    assert!(lean.contains("Litex.absNonnegative"));
    assert!(lean.contains("Litex.absOfNonnegative"));
}

#[test]
fn symbolic_natural_power_preserves_original_exponent_and_observes_its_checked_membership() {
    let (result, compiler) = checked("have n N\n2^n=2^n\n");
    let lean = compiler
        .compile_run(&result, "symbolic_natural_power")
        .expect("recorded natural exponent");
    assert!(lean.contains("Litex.NativeBridge.asNat"));
    assert!(lean.contains("Litex.NativeBridge.asNat_spec"));
    assert!(lean.contains("Litex.powNatReal"));
    assert!(lean.contains("_Host_i"));
}

#[test]
fn natural_parameter_arithmetic_uses_its_actual_generic_membership() {
    let (result, compiler) = checked("have n N\nn+0=n\n");
    let lean = compiler
        .compile_run(&result, "natural_numeric_observation")
        .expect("generic natural observation");
    assert!(lean.contains("Litex.naturalToComplex"));
    assert!(lean.contains("_Host_i"));
}

#[test]
fn absolute_value_rejects_missing_original_child_and_domain_evidence() {
    let (mut result, compiler) = checked("$is_set(|-2|)\n");
    abs_mut(&mut result).child_obj_well_defined.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "abs_missing_child")
            .unwrap_err()
            .route,
        "WD/Abs"
    );
    let (mut result, compiler) = checked("$is_set(|-2|)\n");
    abs_mut(&mut result).requirement_fact_verified.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "abs_missing_domain")
            .unwrap_err()
            .route,
        "WD/Abs"
    );
}

#[test]
fn absolute_value_rejects_an_original_child_subject_changed_after_verification() {
    let (mut result, compiler) = checked("$is_set(|-2|)\n");
    let DetailedObjWellDefinedProof::ByDef { obj, .. } =
        (abs_mut(&mut result).child_obj_well_defined[0].as_mut())
            .as_detailed_mut()
            .unwrap()
    else {
        panic!("actual original number WD")
    };
    *obj = Obj::Literal(Literal::Number(Number::new("2".into())));
    assert!(compiler.compile_run(&result, "abs_other_argument").is_err());
}

#[test]
fn symbolic_power_rejects_missing_or_changed_original_natural_requirement() {
    let (mut result, compiler) = checked("have n N\n2^n=2^n\n");
    pow_mut(&mut result).requirement_fact_verified.pop();
    assert_eq!(
        compiler
            .compile_run(&result, "power_missing_natural")
            .unwrap_err()
            .route,
        "WD/Pow"
    );
    let (mut result, compiler) = checked("have n N\n2^n=2^n\n");
    let VerifyFactResult::AtomicExceptEquality(proof) =
        &mut pow_mut(&mut result).requirement_fact_verified[1]
    else {
        panic!("actual natural requirement")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual natural success")
    };
    let AtomicFact::InFact(member) = &mut proof.fact else {
        panic!("actual membership")
    };
    member.set = Obj::StandardSet(StandardSet::C);
    assert!(compiler.compile_run(&result, "power_other_domain").is_err());
}

#[test]
fn symbolic_signed_integer_exponents_replay_membership_and_base_guard() {
    let source = "have z Z\nclaim:\n    ? forall x C:\n        x != 0\n        =>:\n            x^z=x^z\n    x^z=x^z\n";
    let (result, compiler) = checked(source);
    let lean = compiler
        .compile_run(&result, "symbolic_integer_power")
        .expect("recorded integer membership and nonzero base");
    assert!(lean.contains("Classical.choose_spec"));
    assert!(lean.contains("Litex.powInt"));
}

#[test]
fn symbolic_integer_power_requires_original_membership_and_nonzero_guard() {
    let source = "have n Z\n2^n=2^n\n";
    for change in ["membership", "nonzero", "order"] {
        let (mut result, compiler) = checked(source);
        let wd = pow_mut(&mut result);
        assert_eq!(wd.requirement_fact_verified.len(), 3);
        match change {
            "membership" => {
                wd.requirement_fact_verified.remove(1);
            }
            "nonzero" => {
                wd.requirement_fact_verified.pop();
            }
            _ => wd.requirement_fact_verified.swap(0, 1),
        }
        compiler
            .compile_run(&result, "missing_integer_power_wd")
            .expect_err(change);
    }
}
