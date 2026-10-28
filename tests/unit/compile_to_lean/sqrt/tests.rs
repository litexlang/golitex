use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SqrtObjWellDefinedProof;
use crate::prelude::*;

const SQUARE: &str =
    include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/sqrt_square.lit");
const NONNEGATIVE: &str = include_str!(
    "../../../../examples/proof_nodes/atomic/by_builtin_rule/less_equal_sqrt_nonnegative.lit"
);
const SCALAR: &str = include_str!("../../../../examples/wd/obj/scalar_sqrt.lit");

#[test]
fn positive_parameter_carries_its_set_semantics_dependency() {
    let (result, compiler) = super::execute("have a R+\n");
    let output = compiler.compile_run(&result, "positive_parameter").unwrap();
    assert!(
        output.contains("[_setSemantics : Litex.SetSemantics M]"),
        "{output}"
    );
}

#[test]
fn sqrt_child_reuses_the_completed_parent_projection() {
    let (result, compiler) =
        super::execute("have a R+\n0 <= a\n$is_set(sqrt(a) + 1)\n$is_set(sqrt(a))\n");
    let output = compiler.compile_run(&result, "sqrt_child").unwrap();
    assert_eq!(output.matches("Litex.sqrt ").count(), 1, "{output}");
    assert!(output.contains(".val.left"), "{output}");
}

#[test]
fn closed_sqrt_membership_replays_its_exact_numeric_observation() {
    for source in [
        "$is_set(sqrt(4) + 1)\n$is_set(sqrt(4))\n",
        "$is_set(sqrt(1 / 4) + 1)\n",
        "$is_set(sqrt(sqrt(16)) + 1)\n",
    ] {
        let (result, compiler) = super::execute(source);
        let output = compiler.compile_run(&result, "closed_sqrt").unwrap();
        assert!(output.contains("Litex.NativeBridge.denoteSqrt"), "{output}");
        assert!(!output.contains("sorry") && !output.contains("axiom"));
    }
}

#[test]
fn reused_sqrt_still_requires_its_own_domain_evidence() {
    let (mut result, compiler) =
        super::execute("have a R+\n0 <= a\n$is_set(sqrt(a) + 1)\n$is_set(sqrt(a))\n");
    let proof = super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut result.statement_results[3]).verify_result,
    );
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(root)),
        ..
    } = (&mut proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0])
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("the child is independently checked")
    };
    root.requirement_fact_verified.pop();
    let error = compiler
        .compile_run(&result, "missing_reused_sqrt_domain")
        .unwrap_err();
    assert_eq!(error.route, "WD/SqrtStages");
}

fn square(result: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    super::equality_proof_mut(
        &mut super::fact_statement_mut(&mut result.statement_results[2]).verify_result,
    )
}

fn root_wd(result: &mut RunLitexCodeResult) -> &mut SqrtObjWellDefinedProof {
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Pow(power),
            ),
        ..
    } = (&mut square(result)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left)
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("the original square constructs a power")
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Sqrt(root)),
        ..
    } = (power.child_obj_well_defined[0].as_mut())
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("the original power constructs its square root first")
    };
    root
}

#[test]
fn sqrt_replays_existing_scalar_square_and_nonnegative_results() {
    for (name, source, law) in [
        ("sqrt_scalar", SCALAR, "Litex.sqrt"),
        ("sqrt_square", SQUARE, "Litex.sqrtSquareValue"),
        ("sqrt_nonnegative", NONNEGATIVE, "Litex.sqrtNonnegative"),
    ] {
        let (result, compiler) = super::execute(source);
        let output = compiler.compile_run(&result, name).expect(name);
        assert!(
            output.contains(law),
            "{name} must replay its original branch"
        );
        assert!(!output.contains("sorry") && !output.contains("axiom"));
    }
}

#[test]
fn sqrt_wd_rejects_missing_stages_and_reordered_requirements() {
    for change in ["child", "requirement", "order"] {
        let (mut result, compiler) = super::execute(SQUARE);
        let wd = root_wd(&mut result);
        assert_eq!(wd.child_obj_well_defined.len(), 1);
        assert_eq!(wd.requirement_fact_verified.len(), 2);
        match change {
            "child" => wd.child_obj_well_defined.clear(),
            "requirement" => wd.requirement_fact_verified.clear(),
            "order" => wd.requirement_fact_verified.swap(0, 1),
            _ => unreachable!(),
        }
        let error = compiler
            .compile_run(&result, "missing_sqrt_stage")
            .expect_err("sqrt must consume the ordered original WD stages");
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
fn sqrt_wd_rejects_a_different_child_subject() {
    let (mut result, compiler) = super::execute(SQUARE);
    super::replace_wd_subject(
        &mut root_wd(&mut result).child_obj_well_defined[0],
        super::number_object("7"),
    );
    let error = compiler
        .compile_run(&result, "wrong_sqrt_child")
        .expect_err("the constructor cannot replace its checked argument");
    assert_eq!(error.route, "WD/Subject");
}

#[test]
fn sqrt_square_rejects_missing_or_unrelated_nonnegative_proof() {
    for change in ["missing", "subject"] {
        let (mut result, compiler) = super::execute(SQUARE);
        let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SqrtSquare(
            rule,
        )) = &mut square(&mut result).searched_proof
        else {
            panic!("the existing example selects SqrtSquare")
        };
        assert_eq!(rule.proof_of_requirement_facts.len(), 1);
        let expected = if change == "missing" {
            rule.proof_of_requirement_facts.clear();
            "SqrtSquare/Requirements"
        } else {
            let child = super::atomic_proof_mut(&mut rule.proof_of_requirement_facts[0]);
            let AtomicFact::LessEqualFact(bound) = &mut child.fact else {
                panic!("the selected square child is nonnegativity")
            };
            bound.right = super::number_object("7");
            "SqrtSquare/RequirementSubject"
        };
        let error = compiler
            .compile_run(&result, "wrong_sqrt_square_requirement")
            .expect_err("the square law requires its exact selected premise");
        assert_eq!(error.route, expected);
    }
}
