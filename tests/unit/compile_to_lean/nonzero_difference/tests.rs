use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule;

fn difference_proof_mut(result: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            NotEqualFactSearchProofByBuiltinRule::DiffNonzeroFromInequality(rule),
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("actual selected difference nonzero route");
    };
    &mut rule.operands_unequal_proof
}

#[test]
fn nonzero_difference_replays_exact_selected_child_and_generic_carriers() {
    for carrier in ["N", "Z", "Q", "R", "C"] {
        for conclusion in ["a-b!=0", "0!=a-b", "a-b!=1-1", "1-1!=a-b"] {
            let source =
                format!("forall a, b {carrier}:\n    a!=b\n    =>:\n        {conclusion}\n");
            let (mut result, compiler) = super::execute(&source);
            difference_proof_mut(&mut result);
            let output = super::compile_run(&result, &compiler, "nonzero_difference").unwrap();
            assert!(output.contains("Litex.subNonzeroOfNotSame"), "{source}");
            assert!(output.contains("Representation M"), "{source}");
            assert!(!output.contains("sorry") && !output.contains("admit"));
        }
    }
}

#[test]
fn nonzero_difference_rejects_changed_child_subject() {
    for changed in ["a", "0", "1", "reordered"] {
        let (mut result, compiler) =
            super::execute("forall a, b R:\n    a!=b\n    =>:\n        a-b!=0\n");
        let child = super::atomic_proof_mut(difference_proof_mut(&mut result));
        let AtomicFact::NotEqualFact(fact) = &mut child.fact else {
            panic!("inequality child")
        };
        if changed == "a" {
            fact.right = fact.left.clone();
        } else if changed == "reordered" {
            std::mem::swap(&mut fact.left, &mut fact.right);
        } else {
            fact.right = Obj::Literal(Literal::Number(Number::new(changed.into())));
        }
        let error = super::compile_run(&result, &compiler, "changed_difference_child").unwrap_err();
        assert!(
            error.to_string().contains("NonzeroDifference/Premise"),
            "{error}"
        );
    }
}

#[test]
fn nonzero_difference_rejects_deleted_child_producer() {
    let (mut result, compiler) =
        super::execute("forall a, b R:\n    a!=b\n    =>:\n        a-b!=0\n");
    difference_proof_mut(&mut result);
    super::forall_proof_mut(&mut result.statement_results[0])
        .assumed_dom_facts
        .clear();
    assert!(super::compile_run(&result, &compiler, "missing_difference_premise").is_err());
}

#[test]
fn nonzero_difference_rejects_nonzero_endpoint_even_with_true_child() {
    let (mut result, compiler) =
        super::execute("forall a, b R:\n    a!=b\n    =>:\n        a-b!=0\n");
    difference_proof_mut(&mut result);
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let AtomicFact::NotEqualFact(fact) = &mut atomic.fact else {
        panic!("inequality goal")
    };
    fact.right = Obj::Literal(Literal::Number(Number::new("1".into())));
    assert!(super::compile_run(&result, &compiler, "wrong_zero_endpoint").is_err());
}
