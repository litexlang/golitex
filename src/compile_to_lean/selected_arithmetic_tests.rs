use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::RealArithmeticConstructorTree;
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::IntrinsicCodomain;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::DivSharedPositiveDenomLessEqualStrategySingleStep;

#[test]
fn dvd_unified_lean_rejects_the_actual_native_rule_certificate() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let prefix = rt.run_litex_code("have d Z*,k Z").unwrap();
    assert!(prefix.success && prefix.session_error.is_none());
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$dvd(d*k,d)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    let VerifyFactResult::AtomicExceptEquality(result) =
        rt.verify_fact(&fact, VerifyState::top_level()).unwrap()
    else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = *result else {
        panic!("success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = result.searched_proof else {
        panic!("native rule")
    };
    assert_eq!(
        super::helper::unsupported_atomic_builtin(&rule).route,
        "Atomic/DvdBuiltin"
    );
}

const POSITIVE_POWER: &str =
    "claim:\n    ? forall n N:\n        (1 / 4)^n > 0\n    (1 / 4)^n > 0\n";
const ABS_EVEN: &str = "claim:\n    ? forall x R:\n        |x|^2=x^2\n    |x|^2=x^2\n";
const PREDECESSOR: &str = "claim:\n    ? forall n N:\n        n > 0\n        =>:\n            n - 1 >= 0\n    n - 1 $in N\n    n - 1 >= 0\n";
const POWER_PRODUCT: &str = "have n N\n2^(n+1)=2^n*2^1\n";
const POWER_NESTED: &str = "have n N\n(1/4)^(2^n*2)=((1/4)^(2^n))^2\n";
const WEAK_SUM: &str = "claim:\n    ? forall a R, b R:\n        0 <= a\n        0 <= b\n        =>:\n            a + b >= 0\n    a + b >= 0\n";
const MUL_MONOTONE: &str = "claim:\n    ? forall a R, b R, c R:\n        0 <= c\n        a <= b\n        =>:\n            a * c <= b * c\n    a * c <= b * c\n";
const DIV_ZERO_LOWER: &str = "claim:\n    ? forall a R, b R:\n        0 < b\n        0 <= a\n        =>:\n            0 <= a / b\n    0 <= a / b\n";
const DIV_ZERO_UPPER: &str = "claim:\n    ? forall a R, b R:\n        0 < b\n        a <= 0\n        =>:\n            a / b <= 0\n    a / b <= 0\n";

#[test]
fn sqrt_quotient_square_lean_rejects_the_unhandled_rule_certificate() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::SqrtQuotientSquareProof;

    let (mut result, mut compiler) = checked("0=0\n2^2=4*1^2\n");
    compiler
        .compile_run(&result, "sqrt_quotient_square_baseline")
        .expect("supported numeric claim before replacing its proof route");
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("sqrt(4)=2/1", compiler.runtime.current_file.clone())
        .unwrap();
    let Stmt::Fact(source) = compiler.runtime.parse(&tokens).unwrap().remove(0) else {
        panic!("source equation");
    };
    let source = compiler
        .runtime
        .verify_fact(&source, VerifyState::top_level())
        .unwrap();
    assert!(!source.is_failed());
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut result.statement_results[1]
    else {
        panic!("checked numeric equality");
    };
    let VerifyFactResult::Equality(proof) = &mut step.verify_result else {
        panic!("target equality");
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("checked target");
    };
    proof.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
            ElementaryArithmeticProof::SqrtQuotientSquare(SqrtQuotientSquareProof::new(source)),
        ),
    );
    assert_eq!(
        compiler
            .compile_run(&result, "sqrt_quotient_square_unhandled")
            .unwrap_err()
            .route,
        "Equality/BuiltinRule"
    );
}

#[test]
fn integer_quotient_remainder_lean_rejects_the_unsupported_structural_node() {
    use super::source_position::{SourceOwner, SourcePosition};

    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let prefix = rt
        .run_litex_code("have k Z\nhave a Z=2*k\na%2=(2*k)%2=0\n")
        .unwrap();
    assert!(prefix.success && prefix.session_error.is_none());
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("a/2 $in Z", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("membership");
    };
    let VerifyFactResult::AtomicExceptEquality(result) =
        rt.verify_fact(&fact, VerifyState::top_level()).unwrap()
    else {
        panic!("atomic result");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(result) = *result else {
        panic!("checked quotient");
    };
    let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
        result.searched_proof
    else {
        panic!("actual structural evidence");
    };
    assert!(matches!(
        proof.reason,
        StructuralMembershipReason::ExactIntegerDiv { .. }
    ));
    let compiler = LitexToLeanCompiler::new(rt);
    let position = SourcePosition {
        parent: None,
        owner: SourceOwner::Run(&prefix),
        before: prefix.statement_results.len(),
    };
    assert_eq!(
        compiler
            .compile_structural(&proof, &position)
            .unwrap_err()
            .route,
        "StructuralMembership/ExactIntegerDiv"
    );
}

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn first_claim_step(result: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    claim_step_at(result, 0)
}

fn claim_step_at(result: &mut RunLitexCodeResult, index: usize) -> &mut VerifyFactResult {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        proof,
    ))) = &mut result.statement_results[index]
    else {
        panic!("actual claim")
    };
    let ExecClaimBodyProof::Forall(body) = &mut proof.body else {
        panic!("actual forall body")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut body.proof_steps[0] else {
        panic!("actual body step")
    };
    &mut step.verify_result
}

fn zero_division_strategy(
    result: &mut RunLitexCodeResult,
) -> &mut DivSharedPositiveDenomLessEqualStrategySingleStep {
    let VerifyFactResult::AtomicExceptEquality(proof) = first_claim_step(result) else {
        panic!("actual zero endpoint quotient order")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLessEqual(
            proof,
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual original positive divisor strategy")
    };
    proof
}

fn selected_atomic_child(result: &mut VerifyFactResult) -> &mut AtomicFact {
    let VerifyFactResult::AtomicExceptEquality(proof) = result else {
        panic!("actual atomic requirement")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual requirement success")
    };
    &mut proof.fact
}

#[test]
fn selected_real_constructor_tree_replays_and_rejects_swapped_original_children() {
    let source = "have fn arithmetic_probe_identity(x R) R=x\nforall x R:\n    0 <= arithmetic_probe_identity(x)^2\nclaim:\n    ? forall x R:\n        arithmetic_probe_identity(x)^2-1 $in R\n    arithmetic_probe_identity(x)^2-1 $in R\n";
    let (mut result, compiler) = checked(source);
    let lean = compiler
        .compile_run(&result, "real_constructor_original_tree")
        .expect("actual real power and constructor tree");
    assert!(lean.contains("Litex.powStructuralInR"));
    let VerifyFactResult::AtomicExceptEquality(proof) = claim_step_at(&mut result, 2) else {
        panic!("actual real constructor membership")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::RealArithmeticConstructorClosure(proof),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual selected real constructor tree")
    };
    let RealArithmeticConstructorTree::Sub { left, right } = &mut proof.constructor_tree else {
        panic!("actual ordered subtraction tree")
    };
    std::mem::swap(left, right);
    assert!(compiler
        .compile_run(&result, "real_constructor_wrong_tree_order")
        .is_err());
}

fn positive_power_base(result: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    let VerifyFactResult::AtomicExceptEquality(proof) = first_claim_step(result) else {
        panic!("actual positive power")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(dual),
    ) = &mut proof.searched_proof
    else {
        panic!("actual original order dual")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut dual.proof_of_alternate_fact else {
        panic!("actual original strict less result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            LessFactSearchProofByBuiltinRule::PowPositiveFromPositiveBase(selected),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual selected positive power")
    };
    &mut selected.base_positive_proof
}

fn power_law_children(result: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut result.statement_results[1]
    else {
        panic!("actual natural power equality")
    };
    let VerifyFactResult::Equality(proof) = &mut step.verify_result else {
        panic!("actual equality result")
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("actual successful equality")
    };
    match &mut proof.searched_proof {
        EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::PowerProductSameBase(proof),
        ) => &mut proof.proof_of_requirement_facts,
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::PowerOfPower(
            proof,
        )) => &mut proof.proof_of_requirement_facts,
        _ => panic!("actual selected power law"),
    }
}

#[test]
fn actual_positive_power_even_abs_and_natural_predecessor_routes_compile() {
    for (source, bridge) in [
        (POSITIVE_POWER, "Litex.powStructuralPositiveOfPositive"),
        (ABS_EVEN, "Litex.absPowStructuralSame"),
        (PREDECESSOR, "Litex.predecessorInN"),
    ] {
        let (result, compiler) = checked(source);
        let lean = compiler
            .compile_run(&result, "selected_arithmetic_positive")
            .expect("actual arithmetic result replay");
        assert!(lean.contains(bridge));
    }
}

#[test]
fn symbolic_natural_power_laws_replay_ordered_requirements_and_original_denotations() {
    for source in [POWER_PRODUCT, POWER_NESTED, "have n N\n2^(n+1)=2^n*2\n"] {
        let (mut result, compiler) = checked(source);
        assert_eq!(power_law_children(&mut result).len(), 3);
        let lean = compiler
            .compile_run(&result, "selected_natural_power_law")
            .expect("actual symbolic natural power law");
        assert!(lean.contains("Litex.NativeBridge.denotePowStructuralNat"));
        assert!(lean.contains("Litex.NativeBridge.asNat_spec"));
        assert!(lean.contains("_litex_combined_exponent"));
        assert!(lean.contains("(Eq.symm (by"));
    }
}

#[test]
fn selected_natural_power_laws_reject_deleted_original_requirement() {
    for source in [POWER_PRODUCT, POWER_NESTED] {
        let (mut result, compiler) = checked(source);
        power_law_children(&mut result).pop();
        assert_eq!(
            compiler
                .compile_run(&result, "power_law_missing_child")
                .unwrap_err()
                .route,
            "NaturalPowerLaw/Requirements"
        );
    }
}

#[test]
fn positive_power_rejects_changed_base_or_missing_actual_child_wd() {
    let (mut result, compiler) = checked(POSITIVE_POWER);
    let VerifyFactResult::AtomicExceptEquality(child) = positive_power_base(&mut result) else {
        panic!("actual positive base child")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(child) = child.as_mut() else {
        panic!("actual child success")
    };
    let AtomicFact::LessFact(bound) = &mut child.fact else {
        panic!("actual original lower-zero orientation")
    };
    bound.right = Obj::Literal(Literal::Number(Number::new("2".into())));
    assert_eq!(
        compiler
            .compile_run(&result, "positive_power_other_base")
            .unwrap_err()
            .route,
        "PositivePower/ChildSubject"
    );
    let (mut result, compiler) = checked(POSITIVE_POWER);
    let VerifyFactResult::AtomicExceptEquality(child) = positive_power_base(&mut result) else {
        panic!("actual positive base child")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(child) = child.as_mut() else {
        panic!("actual child success")
    };
    child
        .well_defined_proof
        .well_defined_of_each_parameter
        .clear();
    assert!(compiler
        .compile_run(&result, "positive_power_missing_child_wd")
        .is_err());
}

#[test]
fn selected_natural_power_laws_reject_swapped_base_and_exponent_certificates() {
    for source in [POWER_PRODUCT, POWER_NESTED] {
        let (mut result, compiler) = checked(source);
        power_law_children(&mut result).swap(0, 1);
        assert_eq!(
            compiler
                .compile_run(&result, "power_law_wrong_order")
                .unwrap_err()
                .route,
            "NaturalPowerLaw/RequirementCarrier"
        );
    }
}

#[test]
fn selected_even_abs_rule_cannot_replace_an_odd_power_identity() {
    let (mut result, compiler) =
        checked("claim:\n    ? forall x R:\n        x^3=x^3\n    x^3=x^3\n");
    let VerifyFactResult::Equality(proof) = first_claim_step(&mut result) else {
        panic!("actual original equality")
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    proof.searched_proof = EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
            ElementaryArithmeticProof::AbsEvenPower,
        ),
    );
    assert_eq!(
        compiler
            .compile_run(&result, "wrong_abs_even_variant")
            .unwrap_err()
            .route,
        "AbsEvenPower/Constructor"
    );
}

#[test]
fn intrinsic_abs_codomain_is_selected_by_its_actual_tag_and_original_wd() {
    let source = "claim:\n    ? forall x R:\n        |x| $in R\n    |x| $in R\n";
    let (mut result, compiler) = checked(source);
    compiler
        .compile_run(&result, "intrinsic_abs_owned_codomain")
        .expect("original intrinsic Abs codomain");
    let VerifyFactResult::AtomicExceptEquality(proof) = first_claim_step(&mut result) else {
        panic!("actual abs membership")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
        &mut proof.searched_proof
    else {
        panic!("actual structural result")
    };
    assert!(matches!(
        proof.reason,
        StructuralMembershipReason::Intrinsic(IntrinsicCodomain::Abs)
    ));
    proof.reason = StructuralMembershipReason::Intrinsic(IntrinsicCodomain::Sqrt);
    assert_eq!(
        compiler
            .compile_run(&result, "intrinsic_wrong_codomain_tag")
            .unwrap_err()
            .route,
        "StructuralMembership/Intrinsic"
    );
}

#[test]
fn natural_predecessor_rejects_changed_original_positive_citation_subject() {
    let (mut result, compiler) = checked(PREDECESSOR);
    let VerifyFactResult::AtomicExceptEquality(proof) = first_claim_step(&mut result) else {
        panic!("actual membership result")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::PredecessorFromPositiveNatural(selected),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual selected predecessor")
    };
    let AtomicFact::GreaterFact(positive) = &mut selected.positive_proof.fact else {
        panic!("actual original positive orientation")
    };
    positive.left = Obj::Literal(Literal::Number(Number::new("2".into())));
    assert_eq!(
        compiler
            .compile_run(&result, "wrong_predecessor_minuend")
            .unwrap_err()
            .route,
        "NaturalPredecessor/PositiveChild"
    );
}

#[test]
fn original_weak_order_tranche_replays_exact_selected_children() {
    let source = [WEAK_SUM, MUL_MONOTONE,
        "claim:\n    ? forall a R, b R:\n        0 <= a\n        0 <= b\n        =>:\n            a * b >= 0\n    a * b >= 0\n",
        "claim:\n    ? forall a R, b R:\n        0 <= a\n        0 < b\n        =>:\n            a + b > 0\n    a + b > 0\n",
        "claim:\n    ? forall a R, b R, c R:\n        0 < c\n        a <= b\n        =>:\n            a / c <= b / c\n    a / c <= b / c\n",
        "claim:\n    ? forall a R, b R, c R:\n        0 < c\n        c * a <= b\n        =>:\n            a <= b / c\n    a <= b / c\n",
        "claim:\n    ? forall a R, b R:\n        0 <= b - a\n        =>:\n            a <= b\n    a <= b\n",
    ].join("\n");
    let (result, compiler) = checked(&source);
    let lean = compiler
        .compile_run(&result, "selected_arithmetic_weak_order")
        .expect("actual selected weak order proofs");
    for bridge in [
        "Litex.addNonnegative",
        "Litex.mulNonnegative",
        "Litex.addPositiveRight",
        "Litex.mulStructuralLeRight",
        "Litex.divStructuralLe",
        "Litex.leDivOfProductBound",
        "Litex.subNonnegativeToLe",
    ] {
        assert!(lean.contains(bridge), "{bridge}");
    }
}

#[test]
fn selected_weak_sum_rejects_deleted_or_wrong_ordered_evidence() {
    for deletion in [true, false] {
        let (mut result, compiler) = checked(WEAK_SUM);
        let VerifyFactResult::AtomicExceptEquality(proof) = first_claim_step(&mut result) else {
            panic!("actual weak sum")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
            panic!("actual success")
        };
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonnegativeSumIsNonnegative(
                proof,
            ),
        ) = &mut proof.searched_proof
        else {
            panic!("actual selected weak sum")
        };
        if deletion {
            proof.proof_of_requirement_facts.pop();
        } else {
            proof.requirement_facts.swap(0, 1);
        }
        let error = compiler
            .compile_run(&result, "weak_sum_corrupted")
            .unwrap_err();
        assert_eq!(
            error.route,
            if deletion {
                "ZeroBound/Requirements"
            } else {
                "ZeroBound/ChildSubject"
            }
        );
    }
}

#[test]
fn selected_product_monotonicity_rejects_exchanging_the_two_original_certificates() {
    let (mut result, compiler) = checked(MUL_MONOTONE);
    let VerifyFactResult::AtomicExceptEquality(proof) = first_claim_step(&mut result) else {
        panic!("actual weak product order")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            LessEqualFactSearchProofByBuiltinRule::MulRightNonnegativeMonotone(proof),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("actual selected multiplication monotonicity")
    };
    std::mem::swap(
        &mut proof.nonnegative_factor_proof,
        &mut proof.order_premise_proof,
    );
    assert_eq!(
        compiler
            .compile_run(&result, "multiplication_wrong_evidence_order")
            .unwrap_err()
            .route,
        "SelectedOrder/ChildSubject"
    );
}

#[test]
fn selected_division_zero_endpoints_retain_original_quotient_and_both_orientations() {
    for (source, law) in [
        (DIV_ZERO_LOWER.to_owned(), "Litex.divStructuralNonnegative"),
        (
            DIV_ZERO_LOWER.replace("0 <= a / b", "a / b >= 0"),
            "Litex.divStructuralNonnegative",
        ),
        (DIV_ZERO_UPPER.to_owned(), "Litex.divStructuralNonpositive"),
        (
            DIV_ZERO_UPPER.replace("a / b <= 0", "0 >= a / b"),
            "Litex.divStructuralNonpositive",
        ),
    ] {
        let (mut result, compiler) = checked(&source);
        zero_division_strategy(&mut result);
        let lean = compiler
            .compile_run(&result, "original_zero_quotient_endpoint")
            .expect("actual original quotient zero endpoint strategy");
        assert!(lean.contains(law), "{law}");
    }
}

#[test]
fn selected_division_zero_endpoints_reject_missing_swapped_and_wrong_identity_children() {
    for source in [DIV_ZERO_LOWER, DIV_ZERO_UPPER] {
        for corruption in 0..3 {
            let (mut result, compiler) = checked(source);
            let selected = zero_division_strategy(&mut result);
            let expected = match corruption {
                0 => {
                    selected.proof_of_requirement_facts.pop();
                    "DivMonotone/Requirements"
                }
                1 => {
                    selected.requirement_facts.swap(0, 1);
                    selected.proof_of_requirement_facts.swap(0, 1);
                    "SelectedOrder/ChildSubject"
                }
                _ => {
                    selected.requirement_facts.swap(0, 1);
                    "DivMonotone/RequirementCapture"
                }
            };
            assert_eq!(
                compiler
                    .compile_run(&result, "corrupted_zero_quotient_children")
                    .unwrap_err()
                    .route,
                expected
            );
        }
    }
}

#[test]
fn selected_division_zero_endpoints_reject_changed_operands_and_weakened_divisor_sign() {
    for source in [DIV_ZERO_LOWER, DIV_ZERO_UPPER] {
        for weaken in [false, true] {
            let (mut result, compiler) = checked(source);
            let selected = zero_division_strategy(&mut result);
            let child = selected_atomic_child(&mut selected.proof_of_requirement_facts[0]);
            let AtomicFact::LessFact(positive) = child else {
                panic!("actual strict original denominator sign")
            };
            if weaken {
                *child = AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: positive.fact_id,
                    left: positive.left.clone(),
                    right: positive.right.clone(),
                    line_file: positive.line_file.clone(),
                });
            } else {
                positive.right = Obj::Literal(Literal::Number(Number::new("2".into())));
            }
            selected.requirement_facts[0] = Fact::AtomicFact(child.clone());
            assert_eq!(
                compiler
                    .compile_run(&result, "corrupted_zero_quotient_sign")
                    .unwrap_err()
                    .route,
                "SelectedOrder/ChildSubject"
            );
        }
    }
}

#[test]
fn selected_division_zero_endpoints_reject_changed_original_numerator_bound() {
    for (source, zero_left) in [(DIV_ZERO_LOWER, true), (DIV_ZERO_UPPER, false)] {
        let (mut result, compiler) = checked(source);
        let selected = zero_division_strategy(&mut result);
        let child = selected_atomic_child(&mut selected.proof_of_requirement_facts[1]);
        let AtomicFact::LessEqualFact(bound) = child else {
            panic!("actual weak numerator bound")
        };
        let changed = Obj::Literal(Literal::Number(Number::new("2".into())));
        if zero_left {
            bound.right = changed;
        } else {
            bound.left = changed;
        }
        selected.requirement_facts[1] = Fact::AtomicFact(child.clone());
        assert_eq!(
            compiler
                .compile_run(&result, "corrupted_zero_quotient_numerator")
                .unwrap_err()
                .route,
            "SelectedOrder/ChildSubject"
        );
    }
}
