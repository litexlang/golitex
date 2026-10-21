use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{less_equal::LessEqualFactSearchProofByBuiltinRule, greater_equal::GreaterEqualFactSearchProofByBuiltinRule, order_complement::FromKnownOrderComplementBuiltinRuleProof,
less::LessFactSearchProofByBuiltinRule,
greater::GreaterFactSearchProofByBuiltinRule,
not_less::NotLessFactSearchProofByBuiltinRule,
not_greater::NotGreaterFactSearchProofByBuiltinRule,
not_less_equal::NotLessEqualFactSearchProofByBuiltinRule,
not_greater_equal::NotGreaterEqualFactSearchProofByBuiltinRule};

const SOURCE: &str = "forall x, y R:\n    not x > y\n    =>:\n        x <= y\n";

fn complement(result: &mut RunLitexCodeResult) -> &mut FromKnownOrderComplementBuiltinRuleProof {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            )
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
                GreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) => proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) => proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) => proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(
                NotLessFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            )
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(
                NotGreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            )
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(
                NotLessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            )
            | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(
                NotGreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(proof),
            ),
        ) => proof,
        _ => panic!("original order complement"),
    }
}

#[test]
fn weak_order_complement_consumes_the_original_real_carriers() {
    let (mut result, compiler) = super::execute(SOURCE);
    assert_eq!(complement(&mut result).real_carrier_proofs.len(), 2);
    assert!(compiler
        .compile_run(&result, "order_complement")
        .unwrap()
        .contains("le_of_not_gt"));
}

#[test]
fn weak_order_complement_rejects_exchanged_carriers_and_changed_premise() {
    for change_premise in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = complement(&mut result);
        if change_premise {
            let AtomicFact::NotGreaterFact(fact) = &mut proof.premise_proof.fact else {
                unreachable!()
            };
            std::mem::swap(&mut fact.left, &mut fact.right);
        } else {
            proof.real_carrier_proofs.swap(0, 1);
        }
        compiler
            .compile_run(&result, "invalid_complement")
            .expect_err("original premise and ordered carriers are required");
    }
}

#[test]
fn weak_order_complement_replays_greater_equal_and_rejects_wrong_carrier_order() {
    let (mut result, compiler) =
        super::execute("forall x, y R:\n    not x < y\n    =>:\n        x >= y\n");
    compiler.compile_run(&result, "ge_complement").unwrap();
    complement(&mut result).real_carrier_proofs.swap(0, 1);
    assert!(compiler.compile_run(&result, "wrong_ge_carriers").is_err());
}

#[test]
fn negative_order_complements_consume_ordered_real_carriers() {
    for (premise, conclusion) in [
        ("x <= y", "not x > y"),
        ("x >= y", "not x < y"),
        ("x < y", "not x >= y"),
        ("x > y", "not x <= y"),
    ] {
        let source = format!("forall x, y R:\n    {premise}\n    =>:\n        {conclusion}\n");
        let (mut result, compiler) = super::execute(&source);
        assert_eq!(complement(&mut result).real_carrier_proofs.len(), 2);
        compiler.compile_run(&result, "negative_order").unwrap();
        complement(&mut result).real_carrier_proofs.swap(0, 1);
        assert!(compiler
            .compile_run(&result, "wrong_negative_carriers")
            .is_err());
    }
}

#[test]
fn strict_order_complements_keep_the_original_premise_and_carrier_stages() {
    for (premise, conclusion) in [("not x >= y", "x < y"), ("not x <= y", "x > y")] {
        let source = format!("forall x, y R:\n    {premise}\n    =>:\n        {conclusion}\n");
        let (mut result, compiler) = super::execute(&source);
        assert_eq!(complement(&mut result).real_carrier_proofs.len(), 2);
        assert!(compiler
            .compile_run(&result, "strict_order")
            .unwrap()
            .contains("lt_of_not_ge"));
        complement(&mut result).real_carrier_proofs.pop();
        assert!(compiler
            .compile_run(&result, "missing_strict_carrier")
            .is_err());
    }
}

#[test]
fn strict_sum_replays_both_original_orders_and_rejects_changed_subject() {
    for output in ["b + d", "d + b"] {
        let source = format!(
            "forall a, b, c, d R:\n    a < b\n    c < d\n    =>:\n        a + c < {output}\n"
        );
        let (mut result, compiler) = super::execute(&source);
        assert!(compiler
            .compile_run(&result, "sum_strict")
            .unwrap()
            .contains("addLtAdd"));
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::SumStrictOperands(proof),
            ),
        ) = &mut proof.searched_proof
        else {
            panic!("original strict sum route");
        };
        let AtomicFact::LessFact(second) = &mut proof.second_order.fact else {
            panic!("original order");
        };
        std::mem::swap(&mut second.left, &mut second.right);
        assert!(compiler.compile_run(&result, "invalid_sum_order").is_err());
    }
}

#[test]
fn strict_multiplication_replays_selected_factor_and_operand_order() {
    for (left, right) in [
        ("z * x", "z * y"),
        ("x * z", "y * z"),
        ("x * z", "z * y"),
        ("z * x", "y * z"),
    ] {
        let source =
            format!("forall x, y, z R:\n    0 < z\n    x < y\n    =>:\n        {left} < {right}\n");
        let (mut result, compiler) = super::execute(&source);
        assert!(compiler
            .compile_run(&result, "strict_product")
            .unwrap()
            .contains("mulStructuralLt"));
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        match &mut proof.searched_proof {
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::MulLeftPositiveMonotoneStrict(p),
                ),
            ) => std::mem::swap(&mut p.positive_factor_proof, &mut p.order_premise_proof),
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::MulRightPositiveMonotoneStrict(p),
                ),
            ) => std::mem::swap(&mut p.positive_factor_proof, &mut p.order_premise_proof),
            AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonPositiveFactorLess(p),
            ) => {
                p.requirement_facts.swap(0, 1);
                p.proof_of_requirement_facts.swap(0, 1);
            }
            _ => panic!("original positive-factor route"),
        }
        assert!(compiler
            .compile_run(&result, "exchanged_product_children")
            .is_err());
    }
}

#[test]
fn strict_add_congruence_replays_original_order_and_real_common_operand() {
    for (left, right) in [("z + x", "z + y"), ("x + z", "y + z")] {
        let source = format!("forall x, y, z R:\n    x < y\n    =>:\n        {left} < {right}\n");
        let (result, compiler) = super::execute(&source);
        assert!(compiler
            .compile_run(&result, "strict_add")
            .unwrap()
            .contains("addStructuralLt"));
    }
}

#[test]
fn minus_one_flip_preserves_original_positive_operand() {
    for expression in ["(-1) * x", "x * (-1)"] {
        let source = format!("forall x R:\n    x > 0\n    =>:\n        {expression} < 0\n");
        let (mut result, compiler) = super::execute(&source);
        assert!(compiler
            .compile_run(&result, "negative_product")
            .unwrap()
            .contains("mulMinusOneNegative"));
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p),
            ),
        ) = &mut proof.searched_proof
        else {
            panic!("original minus-one rule");
        };
        let AtomicFact::GreaterFact(fact) = &mut p.premise_proof.fact else {
            panic!("original positive premise");
        };
        std::mem::swap(&mut fact.left, &mut fact.right);
        assert!(compiler
            .compile_run(&result, "wrong_negative_operand")
            .is_err());
    }
}

#[test]
fn not_equal_symmetry_replays_the_original_reversed_endpoints() {
    let (result, compiler) =
        super::execute("forall a, b cart(R, R):\n    a != b\n    =>:\n        b != a\n");
    let lean = compiler
        .compile_run(&result, "point_inequality_symmetry")
        .unwrap();
    assert!(lean.contains("_litex_same.symm"));
}

#[test]
fn negative_order_duality_preserves_polarity_and_endpoints() {
    for (known, goal) in [
        ("not x < y", "not y > x"),
        ("not x > y", "not y < x"),
        ("not x <= y", "not y >= x"),
        ("not x >= y", "not y <= x"),
    ] {
        let source = format!("forall x, y R:\n    {known}\n    =>:\n        {goal}\n");
        let (mut result, compiler) = super::execute(&source);
        let forall = super::forall_proof_mut(&mut result.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
            super::AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(dual),
        ) = &mut atomic.searched_proof
        else {
            panic!("selected negative dual")
        };
        let alternate = dual.alternate_fact.clone();
        let Fact::AtomicFact(alternate) = alternate else {
            panic!("atomic alternate")
        };
        dual.alternate_fact = Fact::AtomicFact(
            crate::ast::fact::negate_atomic_fact(&alternate, alternate.fact_id()).unwrap(),
        );
        assert_eq!(
            super::compile_run(&result, &compiler, "changed_dual")
                .unwrap_err()
                .route,
            "Order/DualSubject"
        );
        let (result, compiler) = super::execute(&source);
        super::compile_run(&result, &compiler, "negative_dual").expect("exact dual child");
    }
}
