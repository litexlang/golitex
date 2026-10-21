use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equal_from_known_difference_zero::EqualFromKnownDifferenceZeroBuiltinRuleProof;
use crate::prelude::*;

const SOURCE: &str = "forall a, b C:\n    a-b=0\n    =>:\n        a=b\n";

fn selected(result: &mut RunLitexCodeResult) -> &mut EqualFromKnownDifferenceZeroBuiltinRuleProof {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let equality = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(rule),
    ) = &mut equality.searched_proof
    else {
        panic!("actual selected difference-zero rule")
    };
    rule
}

#[test]
fn difference_zero_replays_both_orientations_and_generic_carriers() {
    for carrier in ["R", "C"] {
        for premise in ["a-b=0", "0=a-b", "b-a=0", "0=b-a"] {
            let source = format!("forall a, b {carrier}:\n    {premise}\n    =>:\n        a=b\n");
            let (mut result, compiler) = super::execute(&source);
            let id = selected(&mut result).cite_fact_id;
            let output = compiler.compile_run(&result, "difference_zero").unwrap();
            assert!(output.contains("Litex.sameOfSubZero"), "{source}");
            assert!(output.contains(&format!("h_{}", id.value())));
            assert!(output.contains("Representation M"));
        }
    }
}

#[test]
fn difference_zero_rejects_missing_or_future_citation() {
    for future in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let goal_id = {
            let forall = super::forall_proof_mut(&mut result.statement_results[0]);
            super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result)
                .fact
                .fact_id
        };
        selected(&mut result).cite_fact_id = if future {
            goal_id
        } else {
            FactId::new(u64::MAX)
        };
        assert!(compiler
            .compile_run(&result, "missing_difference_zero")
            .is_err());
    }
}

#[test]
fn difference_zero_rejects_other_operands_and_nonzero_endpoint() {
    for other in ["c-d=0", "a-b=c"] {
        let source =
            format!("forall a, b, c, d C:\n    a-b=0\n    {other}\n    =>:\n        a=b\n");
        let (mut result, compiler) = super::execute(&source);
        let id = super::forall_proof_mut(&mut result.statement_results[0]).assumed_dom_facts[1]
            .store_and_infer
            .store
            .primary_fact_id();
        selected(&mut result).cite_fact_id = id;
        let error = compiler
            .compile_run(&result, "wrong_difference_zero")
            .unwrap_err();
        let expected = if other == "c-d=0" {
            "DifferenceZero/Subjects"
        } else {
            "DifferenceZero/UncapturedZeroPath"
        };
        assert_eq!(error.route, expected);
    }
}

#[test]
fn difference_zero_rejects_deleted_citation_producer() {
    let (mut result, compiler) = super::execute(SOURCE);
    selected(&mut result);
    super::forall_proof_mut(&mut result.statement_results[0])
        .assumed_dom_facts
        .clear();
    assert!(compiler
        .compile_run(&result, "deleted_difference_zero")
        .is_err());
}
