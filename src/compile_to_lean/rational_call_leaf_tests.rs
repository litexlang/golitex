use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof;
use crate::prelude::*;

const SOURCE: &str = "have fn rational_leaf_identity(x R) R=x\n\
forall x R:\n    rational_leaf_identity(x)^2-1=(rational_leaf_identity(x)-1)*(rational_leaf_identity(x)+1)\n\
have fn rational_leaf_pair(x R, y R) R=x+y\n\
forall a R, b R:\n    rational_leaf_pair(a,b)^2-1=(rational_leaf_pair(a,b)-1)*(rational_leaf_pair(a,b)+1)\n\
forall a R, b R:\n    rational_leaf_identity(a)!=0\n    rational_leaf_identity(b)!=0\n    =>:\n        1/rational_leaf_identity(a)+1/rational_leaf_identity(b)=(rational_leaf_identity(a)+rational_leaf_identity(b))/(rational_leaf_identity(a)*rational_leaf_identity(b))\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime
        .run_litex_code(source)
        .expect("original rational call source");
    assert!(result.success && result.session_error.is_none());
    (result, LitexToLeanCompiler::new(runtime))
}

fn equality(result: &mut RunLitexCodeResult, index: usize) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[index]
    else {
        panic!("original forall statement")
    };
    let VerifyFactResult::ForallFact(proof) = &mut statement.verify_result else {
        panic!("original forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_mut()
    else {
        panic!("original local introduction")
    };
    let VerifyFactResult::Equality(proof) = &mut proof.proved_then_facts[0].verify_result else {
        panic!("original equality")
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("checked equality")
    };
    proof
}

fn guarded_children(
    result: &mut RunLitexCodeResult,
) -> (&mut Vec<Fact>, &mut Vec<VerifyFactResult>) {
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
    ) = &mut equality(result, 4).searched_proof
    else {
        panic!("original selected guarded Rational strategy")
    };
    (
        &mut proof.requirement_facts,
        &mut proof.proof_of_requirement_facts,
    )
}

fn first_owned_call(result: &mut RunLitexCodeResult) -> &mut FnObjObjWellDefinedProof {
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Sub(sub),
            ),
        ..
    } = &mut equality(result, 1).well_defined_proof.left
    else {
        panic!("original left subtraction WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Pow(power),
            ),
        ..
    } = sub.child_obj_well_defined[0].as_mut()
    else {
        panic!("original left power WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = power.child_obj_well_defined[0].as_mut()
    else {
        panic!("original owned call WD")
    };
    call
}

#[test]
fn rational_normalization_replays_original_one_and_two_argument_scalar_calls() {
    let (mut result, compiler) = checked(SOURCE);
    for index in [1, 3] {
        assert!(matches!(
            equality(&mut result, index).searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
                EqualitySearchProofByCalculation::Rational {}
            ))
        ));
    }
    compiler
        .compile_run(&result, "opaque_numeric_call_leaves")
        .expect("original selected Rational certificates");
}

#[test]
fn rational_normalization_replays_the_original_two_call_nonzero_guards() {
    let (mut result, compiler) = checked(SOURCE);
    let (subjects, children) = guarded_children(&mut result);
    assert_eq!(subjects.len(), 2);
    assert_eq!(children.len(), 2);
    let lean = compiler
        .compile_run(&result, "guarded_opaque_call_leaves")
        .expect("actual guarded Rational certificate");
    assert!(lean.contains("nativeNonzeroOfDenote"));
    assert!(lean.contains("litex_normalize_rational"));
}

#[test]
fn rational_call_leaf_rejects_missing_original_nonzero_evidence() {
    let (mut result, compiler) = checked(SOURCE);
    guarded_children(&mut result).1.pop();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_call_nonzero_guard")
            .unwrap_err()
            .route,
        "Rational/Requirements"
    );
}

#[test]
fn rational_call_leaf_rejects_reordered_original_guards_and_child_identities() {
    for swap_subjects in [false, true] {
        let (mut result, compiler) = checked(SOURCE);
        let (subjects, children) = guarded_children(&mut result);
        children.swap(0, 1);
        if swap_subjects {
            subjects.swap(0, 1);
        }
        assert_eq!(
            compiler
                .compile_run(&result, "reordered_call_nonzero_guards")
                .unwrap_err()
                .route,
            if swap_subjects {
                "Arithmetic/NonzeroSubject"
            } else {
                "Rational/RequirementSubject"
            }
        );
    }
}

#[test]
fn rational_call_leaf_requires_original_constructor_domain_and_argument_evidence() {
    for remove_domain in [false, true] {
        let (mut result, compiler) = checked(SOURCE);
        let original = first_owned_call(&mut result);
        if remove_domain {
            original.domain_fn_set = None;
        } else {
            original.requirement_fact_verified.clear();
        }
        assert_eq!(
            compiler
                .compile_run(&result, "missing_call_constructor_evidence")
                .unwrap_err()
                .route,
            if remove_domain {
                "WD/FnObj/DomainEvidence"
            } else {
                "WD/FnObj/StageArity"
            }
        );
    }
}

#[test]
fn rational_normalization_still_rejects_an_unreviewed_abs_leaf_with_its_source_subject() {
    let (mut result, compiler) = checked("forall x R:\n    |x|=|x|\n");
    equality(&mut result, 0).searched_proof =
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::Rational {},
        ));
    let error = compiler
        .compile_run(&result, "unreviewed_abs_rational_leaf")
        .unwrap_err();
    assert_eq!(error.route, "Rational/ExpressionDomain");
    assert!(error.to_string().contains("original source expression"));
}
