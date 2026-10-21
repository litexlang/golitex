use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof;

const ANTISYMMETRY: &str = "forall x, y R:\n    x <= y\n    y <= x\n    =>:\n        x = y\n";
const POWER_ZERO: &str = "forall x R:\n    x ^ 2 = 0\n    =>:\n        x = 0\n";
const ADD_RIGHT: &str = "forall x, y R:\n    y >= 0\n    =>:\n        x <= x + y\n";
const ADD_LEFT: &str = "forall x, y R:\n    y >= 0\n    =>:\n        x <= y + x\n";

#[test]
fn geometry_scalar_rules_replay_the_selected_certificates() {
    for (source, law) in [
        (ANTISYMMETRY, "sameOfLeAntisymm"),
        (POWER_ZERO, "sameBaseZeroOfPositivePowerZero"),
        (ADD_RIGHT, "leSelfAddRight"),
        (ADD_LEFT, "leSelfAddLeft"),
    ] {
        let (result, compiler) = super::execute(source);
        assert!(
            compiler
                .compile_run(&result, "geometry_scalar")
                .unwrap()
                .contains(law),
            "{source}"
        );
    }
}

#[test]
fn geometry_antisymmetry_rejects_one_sided_evidence() {
    let (mut result, compiler) = super::execute(ANTISYMMETRY);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let eq = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(proof),
    ) = &mut eq.searched_proof
    else {
        panic!("order antisymmetry route")
    };
    let AtomicFact::LessEqualFact(fact) = &mut proof.right_le_left_proof.fact else {
        panic!("reverse weak order")
    };
    std::mem::swap(&mut fact.left, &mut fact.right);
    assert_eq!(
        compiler
            .compile_run(&result, "one_sided")
            .unwrap_err()
            .route,
        "OrderAntisymmetry/PremiseSubject"
    );
}

#[test]
fn geometry_power_zero_rejects_another_exponent_requirement() {
    let (mut result, compiler) = super::execute(POWER_ZERO);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let eq = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
            ElementaryArithmeticProof::PositivePowerZero { requirements, .. },
        ),
    ) = &mut eq.searched_proof
    else {
        panic!("positive power zero route")
    };
    let AtomicFact::InFact(member) = &mut super::atomic_proof_mut(&mut requirements[1]).fact else {
        panic!("positive exponent membership")
    };
    member.element = super::number_object("3");
    compiler
        .compile_run(&result, "changed_exponent")
        .expect_err("original power exponent required");
}

const ZERO_PRODUCT: &str = "forall a, b R:\n    a != 0\n    a*b = 0\n    =>:\n        b = 0\n";
const DIFFERENCE_ZERO: &str = "forall a, b R:\n    a = b\n    =>:\n        a-b = 0\n";

fn elementary_children(
    result: &mut RunLitexCodeResult,
    zero_product: bool,
) -> &mut Vec<VerifyFactResult> {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let eq = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    match &mut eq.searched_proof {
        EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::ZeroProductCancel(p),
        ) if zero_product => &mut p.proof_of_requirement_facts,
        EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(p),
        ) if !zero_product => &mut p.proof_of_requirement_facts,
        _ => panic!("original selected scalar rule"),
    }
}

#[test]
fn geometry_zero_product_and_difference_replay_original_children() {
    for (source, product, marker) in [
        (ZERO_PRODUCT, true, "Litex.mulNonzero"),
        (DIFFERENCE_ZERO, false, "M.sub_numbers, sub_self"),
    ] {
        let (mut result, compiler) = super::execute(source);
        assert_eq!(
            elementary_children(&mut result, product).len(),
            if product { 2 } else { 1 }
        );
        assert!(compiler
            .compile_run(&result, "scalar_replay")
            .unwrap()
            .contains(marker));
    }
}

#[test]
fn geometry_zero_product_rejects_missing_or_reversed_children() {
    for reverse in [false, true] {
        let (mut result, compiler) = super::execute(ZERO_PRODUCT);
        let children = elementary_children(&mut result, true);
        if reverse {
            children.swap(0, 1);
        } else {
            children.pop();
        }
        assert!(compiler
            .compile_run(&result, "invalid_product")
            .unwrap_err()
            .route
            .starts_with("ZeroProduct/"));
    }
}

#[test]
fn geometry_difference_zero_rejects_a_different_operand_or_missing_child() {
    for missing in [false, true] {
        let (mut result, compiler) = super::execute(DIFFERENCE_ZERO);
        let children = elementary_children(&mut result, false);
        if missing {
            children.clear();
        } else {
            super::equality_proof_mut(&mut children[0]).fact.right = super::number_object("7");
        }
        assert!(compiler
            .compile_run(&result, "invalid_difference")
            .unwrap_err()
            .route
            .starts_with("DifferenceZero/"));
    }
}

const POWER_ORDER: &str = "forall x, y R:\n    0 <= x\n    x <= y\n    =>:\n        x^2 <= y^2\n";

#[test]
fn geometry_power_order_replays_and_rejects_changed_premise_order() {
    let (mut result, compiler) = super::execute(POWER_ORDER);
    assert!(compiler
        .compile_run(&result, "power_order")
        .unwrap()
        .contains("Litex.powStructuralLe"));
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let eq = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLessEqual(p),
    ) = &mut eq.searched_proof
    else {
        panic!("actual power order strategy")
    };
    p.proof_of_requirement_facts.swap(1, 2);
    assert_eq!(
        compiler
            .compile_run(&result, "bad_power_order")
            .unwrap_err()
            .route,
        "PowerOrder/ChildSubject"
    );
}

#[test]
fn geometry_subtraction_from_addition_replays_and_rejects_an_unrelated_sum() {
    for source in [
        "forall a,b,c R:\n    a+b=c\n    =>:\n        a=c-b\n",
        "forall a,b,c R:\n    a+b=c\n    =>:\n        b=c-a\n",
        "forall a,b,c R:\n    a+b=c\n    =>:\n        c-b=a\n",
    ] {
        let (mut result, compiler) = super::execute(source);
        assert!(compiler
            .compile_run(&result, "subtract_add")
            .unwrap()
            .contains("eq_sub_iff_add_eq"));
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let eq = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(p),
        ) = &mut eq.searched_proof
        else {
            panic!("actual rearrangement rule")
        };
        super::equality_proof_mut(&mut p.proof_of_requirement_facts[0])
            .fact
            .right = super::number_object("7");
        assert!(compiler
            .compile_run(&result, "unrelated_sum")
            .unwrap_err()
            .route
            .starts_with("SubtractionFromAddition/"));
    }
}

#[test]
fn geometry_positive_left_sum_replays_and_rejects_reordered_children() {
    let (mut result, compiler) =
        super::execute("forall x,y R:\n    x>0\n    y>=0\n    =>:\n        x+y>0\n");
    assert!(compiler
        .compile_run(&result, "positive_left")
        .unwrap()
        .contains("Litex.addPositiveLeft"));
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveLeftStrict(p),
    ) = &mut proof.searched_proof
    else {
        panic!("positive-left strategy")
    };
    p.proof_of_requirement_facts.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&result, "wrong_positive_children")
            .unwrap_err()
            .route,
        "ZeroBound/ChildSubject"
    );
}

#[test]
fn geometry_negation_from_sum_zero_keeps_the_recorded_zero_endpoint() {
    for conclusion in ["a=-b", "-b=a", "b=-a", "-a=b"] {
        let source = format!("forall a,b C:\n    a+b=0\n    =>:\n        {conclusion}\n");
        let (mut result, compiler) = super::execute(&source);
        assert!(compiler
            .compile_run(&result, "inverse_from_sum")
            .unwrap()
            .contains("eq_neg_of_add_eq_zero_left"));
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let eq = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(p),
        ) = &mut eq.searched_proof
        else {
            panic!("recorded additive inverse rule")
        };
        super::equality_proof_mut(&mut p.proof_of_requirement_facts[0])
            .fact
            .right = super::number_object("7");
        assert!(compiler
            .compile_run(&result, "wrong_zero")
            .unwrap_err()
            .route
            .starts_with("SubtractionFromAddition/"));
    }
}

#[test]
fn geometry_strict_add_shift_replays_and_rejects_reversed_children() {
    let (mut result, compiler) = super::execute("forall a,b R:\n    b>0\n    =>:\n        a<a+b\n");
    assert!(compiler
        .compile_run(&result, "strict_shift")
        .unwrap()
        .contains("ltAddOfLeOfPos"));
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftWeak(p),
    ) = &mut proof.searched_proof
    else {
        panic!("selected strict shift")
    };
    p.proof_of_requirement_facts.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&result, "bad_shift")
            .unwrap_err()
            .route,
        "StrictAddShift/ChildSubject"
    );
}
