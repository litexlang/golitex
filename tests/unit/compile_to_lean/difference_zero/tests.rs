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
    for (other, expected) in [
        ("c-d=0", "DifferenceZero/Subjects"),
        ("a-b=c", "Equality/PathEndpoint"),
    ] {
        let source =
            format!("forall a, b, c, d C:\n    a-b=0\n    {other}\n    =>:\n        a=b\n");
        let (mut result, compiler) = super::execute(&source);
        let id = super::forall_proof_mut(&mut result.statement_results[0]).assumed_dom_facts[1]
            .store_and_infer
            .store
            .primary_fact_id();
        let proof = selected(&mut result);
        proof.cite_fact_id = id;
        proof.difference_on_left = true;
        // Both premises imply c=0 when `other` is a-b=c. The runtime may
        // already have selected that citation with a valid path to zero;
        // explicitly remove the path to make this a broken certificate.
        proof.zero_path.path.clear();
        let error = compiler
            .compile_run(&result, "wrong_difference_zero")
            .unwrap_err();
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

#[test]
fn difference_zero_captures_and_replays_the_remaining_zero_path() {
    for premise in ["a-b=c", "c=a-b", "b-a=c", "c=b-a"] {
        let source = format!(
            "forall a, b, c, d C:\n    {premise}\n    c=d\n    d=0\n    =>:\n        a=b\n"
        );
        let (mut result, compiler) = super::execute(&source);
        let proof = selected(&mut result);
        assert_eq!(proof.zero_path.path.len(), 2);
        let ids = proof
            .zero_path
            .path
            .iter()
            .map(|step| step.2)
            .collect::<Vec<_>>();
        let json = crate::json_output::emit_run_detailed(
            &result,
            &compiler.runtime,
            "difference_zero_path",
            None,
        );
        assert!(json.contains("\"zero_path\""));
        assert!(json.contains("\"difference_on_left\""));
        let output = compiler
            .compile_run(&result, "difference_zero_path")
            .unwrap();
        assert!(output.contains("Litex.sameOfSubZero"));
        for id in ids {
            assert!(output.contains(&format!("h_{}", id.value())));
        }
    }
}

#[test]
fn difference_zero_rejects_corrupted_zero_paths_and_selected_side() {
    let source = "forall a, b, c, d C:\n    a-b=c\n    c=d\n    d=0\n    =>:\n        a=b\n";
    for mutation in 0..5 {
        let (mut result, compiler) = super::execute(source);
        let proof = selected(&mut result);
        assert_eq!(proof.zero_path.path.len(), 2);
        match mutation {
            0 => {
                proof.zero_path.path.pop();
            }
            1 => {
                proof.zero_path.path.swap(0, 1);
            }
            2 => {
                proof.zero_path.path[0].2 = FactId::new(u64::MAX);
            }
            3 => {
                proof.zero_path.path[0].1 = proof.zero_path.path[0].0.clone();
            }
            4 => {
                proof.difference_on_left = !proof.difference_on_left;
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&result, "invalid_zero_path").is_err());
    }
}

#[test]
fn difference_zero_requires_an_actual_connection_to_zero() {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime
        .run_litex_code("forall a, b, c, d C:\n    a-b=c\n    c=d\n    =>:\n        a=b\n")
        .unwrap();
    assert!(!result.success);
}
