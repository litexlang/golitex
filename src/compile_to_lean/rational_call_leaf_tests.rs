use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnObjObjWellDefinedProof, SqrtObjWellDefinedProof,
};
use crate::prelude::*;

const SOURCE: &str = "have fn rational_leaf_identity(x R) R=x\n\
forall x R:\n    rational_leaf_identity(x)^2-1=(rational_leaf_identity(x)-1)*(rational_leaf_identity(x)+1)\n\
have fn rational_leaf_pair(x R, y R) R=x+y\n\
forall a R, b R:\n    rational_leaf_pair(a,b)^2-1=(rational_leaf_pair(a,b)-1)*(rational_leaf_pair(a,b)+1)\n\
forall a R, b R:\n    rational_leaf_identity(a)!=0\n    rational_leaf_identity(b)!=0\n    =>:\n        1/rational_leaf_identity(a)+1/rational_leaf_identity(b)=(rational_leaf_identity(a)+rational_leaf_identity(b))/(rational_leaf_identity(a)*rational_leaf_identity(b))\n";

const SQRT_PRODUCT: &str = "forall x R:\n    0 <= x\n    =>:\n        sqrt(x)*sqrt(x)=sqrt(x)^2\n";
const SQRT_RADICAND_DIVISION: &str =
    "forall x R:\n    x != 0\n    0 <= 1/x\n    =>:\n        sqrt(1/x)*sqrt(1/x)=sqrt(1/x)^2\n";
const SQRT_RECIPROCALS: &str =
    "forall a R, b R:\n    0 <= a\n    0 <= b\n    sqrt(a) != 0\n    sqrt(b) != 0\n    =>:\n        1/sqrt(a)+1/sqrt(b)=(sqrt(a)+sqrt(b))/(sqrt(a)*sqrt(b))\n";

#[test]
fn rational_coordinates_observe_original_inferred_objects() {
    let source = "forall p cart(R, R):\n    p(1) + p(2) = p(2) + p(1)\n";
    let (result, compiler) = checked(source);
    let lean = compiler
        .compile_run(&result, "coordinate_observations")
        .unwrap();
    assert!(lean.contains("Litex.NativeBridge.asComplex _object_h"));
    assert!(
        !lean.contains("_litex_numeric_call"),
        "coordinate observations should consume the original inferred objects and memberships"
    );
}

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
    index: usize,
) -> (&mut Vec<Fact>, &mut Vec<VerifyFactResult>) {
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
    ) = &mut equality(result, index).searched_proof
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
    let (subjects, children) = guarded_children(&mut result, 4);
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
    for (source, index) in [(SOURCE, 4), (SQRT_RECIPROCALS, 0)] {
        let (mut result, compiler) = checked(source);
        guarded_children(&mut result, index).1.pop();
        assert_eq!(
            compiler
                .compile_run(&result, "missing_leaf_nonzero_guard")
                .unwrap_err()
                .route,
            "Rational/Requirements"
        );
    }
}

#[test]
fn rational_call_leaf_rejects_reordered_original_guards_and_child_identities() {
    for (source, index) in [(SOURCE, 4), (SQRT_RECIPROCALS, 0)] {
        for swap_subjects in [false, true] {
            let (mut result, compiler) = checked(source);
            let (subjects, children) = guarded_children(&mut result, index);
            children.swap(0, 1);
            if swap_subjects {
                subjects.swap(0, 1);
            }
            assert_eq!(
                compiler
                    .compile_run(&result, "reordered_leaf_nonzero_guards")
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

fn first_owned_sqrt(result: &mut RunLitexCodeResult) -> &mut SqrtObjWellDefinedProof {
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Mul(product),
            ),
        ..
    } = &mut equality(result, 0).well_defined_proof.left
    else {
        panic!("the original left product WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(root)),
        ..
    } = product.child_obj_well_defined[0].as_mut()
    else {
        panic!("the original first square-root WD")
    };
    root
}

#[test]
fn rational_normalization_replays_original_sqrt_leaves_without_expanding_radicands() {
    for source in [SQRT_PRODUCT, SQRT_RADICAND_DIVISION] {
        let (mut result, compiler) = checked(source);
        assert!(matches!(
            equality(&mut result, 0).searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
                EqualitySearchProofByCalculation::Rational {}
            ))
        ));
        let lean = compiler
            .compile_run(&result, "opaque_sqrt_product")
            .expect("the original selected Rational square-root certificate");
        assert!(lean.contains("Litex.sqrt") && lean.contains("Litex.NativeBridge.asComplex"));
        assert!(!lean.contains("Litex.sqrtSquareValue"));
    }
}

#[test]
fn rational_normalization_replays_original_sqrt_denominator_guards() {
    let (mut result, compiler) = checked(SQRT_RECIPROCALS);
    let (subjects, children) = guarded_children(&mut result, 0);
    assert_eq!(subjects.len(), 2);
    assert_eq!(children.len(), 2);
    let lean = compiler
        .compile_run(&result, "guarded_opaque_sqrt_leaves")
        .expect("the original selected guarded Rational square-root certificate");
    assert!(lean.contains("nativeNonzeroOfDenote"));
    assert!(lean.contains("litex_normalize_rational"));
    for index in 0..2 {
        let (_, guard) = lean
            .split_once(&format!("have _litex_nz_{index} : "))
            .expect("each original square-root denominator has its own guard");
        let (guard_type, _) = guard
            .split_once(" := Litex.NativeBridge.nativeNonzeroOfDenote")
            .expect("the guard consumes the original denotation and nonzero proof");
        assert!(
            guard_type.contains("Litex.NativeBridge.asComplex")
                && guard_type.ends_with(" : ℂ) ≠ 0"),
            "the tactic-valued observation must be typed before Lean elaborates zero: {guard_type}"
        );
    }
}

#[test]
fn rational_sqrt_leaf_requires_original_ordered_constructor_evidence() {
    for change in ["child", "requirement", "order"] {
        let (mut result, compiler) = checked(SQRT_PRODUCT);
        let original = first_owned_sqrt(&mut result);
        match change {
            "child" => original.child_obj_well_defined.clear(),
            "requirement" => original.requirement_fact_verified.clear(),
            "order" => original.requirement_fact_verified.swap(0, 1),
            _ => unreachable!(),
        }
        let error = compiler
            .compile_run(&result, "missing_sqrt_leaf_evidence")
            .expect_err("an opaque scalar still requires its original constructor evidence");
        assert_eq!(
            error.route,
            if change == "order" {
                "Arithmetic/MembershipSubject"
            } else {
                "WD/SqrtStages"
            }
        );
    }
}

#[test]
fn rational_sqrt_leaf_rejects_a_different_radicand_in_its_child_wd() {
    let (mut result, compiler) = checked(SQRT_PRODUCT);
    let child = first_owned_sqrt(&mut result).child_obj_well_defined[0].as_mut();
    match child {
        ObjWellDefinedProof::ByDef { obj, .. } | ObjWellDefinedProof::ByKnown { obj, .. } => {
            *obj = Obj::Literal(Literal::Number(Number::new("7".to_string())));
        }
    }
    let error = compiler
        .compile_run(&result, "different_sqrt_leaf_radicand")
        .expect_err("an opaque leaf cannot change the original square-root argument");
    assert_eq!(error.route, "WD/Subject");
}
