use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::{GreaterEqualFactSearchProofByBuiltinRule, NonnegativeSumTree};

const SUM_TREE: &str =
    "forall x, y, z R:\n    x >= 0\n    y >= 0\n    z >= 0\n    =>:\n        (x + y) + z >= 0\n";

fn sum_tree(result: &mut RunLitexCodeResult) -> &mut NonnegativeSumTree {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
            GreaterEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(proof),
        ),
    ) = &mut selected(result).searched_proof
    else {
        panic!("original >= sum tree")
    };
    &mut proof.constructor_tree
}

#[test]
fn nonnegative_sum_tree_replays_nested_original_leaves() {
    let (mut result, compiler) = super::execute(SUM_TREE);
    assert!(matches!(
        sum_tree(&mut result),
        NonnegativeSumTree::Add { .. }
    ));
    let output = compiler.compile_run(&result, "nested_sum_tree").unwrap();
    assert!(output.contains("Litex.addNonnegative _litex_sum.val.left.val.left"));
}

#[test]
fn nonnegative_sum_tree_rejects_changed_shape_and_leaf_order() {
    for shape in [false, true] {
        let (mut result, compiler) = super::execute(SUM_TREE);
        let NonnegativeSumTree::Add { left, right } = sum_tree(&mut result) else {
            unreachable!()
        };
        if shape {
            std::mem::swap(left, right);
        } else {
            let NonnegativeSumTree::Add { left, right } = left.as_mut() else {
                unreachable!()
            };
            std::mem::swap(left, right);
        }
        let err = compiler.compile_run(&result, "bad_sum_tree").unwrap_err();
        assert_eq!(
            err.route,
            if shape {
                "NonnegativeSum/Shape"
            } else {
                "NonnegativeSum/Leaf"
            }
        );
    }
}

#[test]
fn nonnegative_sum_tree_rejects_changed_leaf_bound() {
    let (mut result, compiler) = super::execute(SUM_TREE);
    let NonnegativeSumTree::Add { right, .. } = sum_tree(&mut result) else {
        unreachable!()
    };
    let NonnegativeSumTree::Leaf(child) = right.as_mut() else {
        unreachable!()
    };
    let AtomicFact::GreaterEqualFact(fact) = &mut super::atomic_proof_mut(child).fact else {
        unreachable!()
    };
    fact.right = super::number_object("1");
    assert_eq!(
        compiler
            .compile_run(&result, "bad_sum_bound")
            .unwrap_err()
            .route,
        "NonnegativeSum/Leaf"
    );
}

const SUM: &str = include_str!(
    "../../../../examples/proof_nodes/atomic/by_builtin_rule/less_equal_sum_of_nonnegatives.lit"
);
const PRODUCT: &str = include_str!(
    "../../../../examples/proof_nodes/atomic/by_builtin_rule/less_equal_product_of_nonnegatives.lit"
);
const STRATEGY_SUM: &str = "claim:\n    ? forall a R, b R:\n        0 <= a\n        0 <= b\n        =>:\n            a + b >= 0\n    a + b >= 0\n";
const STRATEGY_PRODUCT: &str = "claim:\n    ? forall a R, b R:\n        0 <= a\n        0 <= b\n        =>:\n            a * b >= 0\n    a * b >= 0\n";

fn selected(result: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result)
}

fn children(
    result: &mut RunLitexCodeResult,
    sum: bool,
) -> (&mut VerifyFactResult, &mut VerifyFactResult) {
    match (&mut selected(result).searched_proof, sum) {
        (
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                    LessEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(proof),
                ),
            ),
            true,
        ) => (
            &mut proof.left_nonnegative_proof,
            &mut proof.right_nonnegative_proof,
        ),
        (
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                    LessEqualFactSearchProofByBuiltinRule::ProductOfNonnegatives(proof),
                ),
            ),
            false,
        ) => (
            &mut proof.left_nonnegative_proof,
            &mut proof.right_nonnegative_proof,
        ),
        _ => panic!("the original source must select its own nonnegative builtin"),
    }
}

#[test]
fn nonnegative_builtins_replay_the_actual_sum_and_product_children() {
    for (source, sum, law) in [
        (SUM, true, "Litex.addNonnegative"),
        (PRODUCT, false, "Litex.mulNonnegative"),
    ] {
        let (mut result, compiler) = super::execute(source);
        let (left, right) = children(&mut result, sum);
        let left = super::atomic_proof_mut(left);
        let right = super::atomic_proof_mut(right);
        assert_ne!(left.fact.fact_id(), right.fact.fact_id());
        assert_ne!(left.fact.ir(), right.fact.ir());
        let output = compiler
            .compile_run(&result, "selected_nonnegative_builtin")
            .expect("the original ordered builtin evidence");
        assert!(output.contains(law));
        assert!(output.contains("_litex_nonnegative.wd.1 _litex_nonnegative.wd.2"));
        assert!(!output.contains("sorry") && !output.contains("axiom"));
    }
}

#[test]
fn nonnegative_builtins_reject_exchanged_children() {
    for (source, sum) in [(SUM, true), (PRODUCT, false)] {
        let (mut result, compiler) = super::execute(source);
        let (left, right) = children(&mut result, sum);
        std::mem::swap(left, right);
        let error = compiler
            .compile_run(&result, "nonnegative_exchanged_children")
            .expect_err("left/right operand certificates retain their original order");
        assert_eq!(error.route, "NonnegativeBuiltin/ChildSubject");
    }
}

#[test]
fn nonnegative_builtins_reject_changed_child_operand_or_bound_direction() {
    for (source, sum) in [(SUM, true), (PRODUCT, false)] {
        for change in ["operand", "direction", "zero"] {
            let (mut result, compiler) = super::execute(source);
            let (left, _) = children(&mut result, sum);
            let AtomicFact::LessEqualFact(bound) = &mut super::atomic_proof_mut(left).fact else {
                panic!("the actual original child has a weak zero lower bound")
            };
            match change {
                "operand" => bound.right = super::number_object("7"),
                "direction" => std::mem::swap(&mut bound.left, &mut bound.right),
                "zero" => bound.left = super::number_object("1"),
                _ => unreachable!(),
            }
            let error = compiler
                .compile_run(&result, "nonnegative_changed_child")
                .expect_err("the selected child must prove its exact operand nonnegative");
            assert_eq!(error.route, "NonnegativeBuiltin/ChildSubject");
        }
    }
}

#[test]
fn nonnegative_builtins_do_not_accept_a_forged_strict_child() {
    for (source, sum) in [(SUM, true), (PRODUCT, false)] {
        let (mut result, compiler) = super::execute(source);
        let (left, _) = children(&mut result, sum);
        let proof = super::atomic_proof_mut(left);
        let AtomicFact::LessEqualFact(bound) = &proof.fact else {
            panic!("the original weak premise")
        };
        proof.fact = AtomicFact::LessFact(LessFact {
            fact_id: bound.fact_id,
            left: bound.left.clone(),
            right: bound.right.clone(),
            line_file: bound.line_file.clone(),
        });
        compiler
            .compile_run(&result, "nonnegative_forged_strength")
            .expect_err("the original weak citation cannot prove a forged strict subject");
    }
}

#[test]
fn nonnegative_builtins_retain_the_parent_constructor_wd_check() {
    for source in [SUM, PRODUCT] {
        let (mut result, compiler) = super::execute(source);
        let proof = selected(&mut result);
        super::replace_wd_subject(
            &mut proof.well_defined_proof.well_defined_of_each_parameter[1],
            super::number_object("7"),
        );
        let error = compiler
            .compile_run(&result, "nonnegative_changed_parent_wd")
            .expect_err("the selected builtin cannot replace parent object formation");
        assert_eq!(error.route, "WD/Subject");
    }
}

#[test]
fn existing_nonnegative_strategies_remain_independent_consumers() {
    for (source, law) in [
        (STRATEGY_SUM, "Litex.addNonnegative"),
        (STRATEGY_PRODUCT, "Litex.mulNonnegative"),
    ] {
        let (result, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&result, "existing_nonnegative_strategy")
            .expect("the previously supported strategy keeps its own evidence route");
        assert!(output.contains(law));
        assert!(output.contains("_litex_zero_bound"));
        assert!(!output.contains("_litex_nonnegative :="));
    }
}
