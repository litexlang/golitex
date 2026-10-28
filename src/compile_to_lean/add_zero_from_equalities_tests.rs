use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::add_zero_from_equalities_builtin_rule_proof::AddZeroRightFromEqualitiesBuiltinRuleProof;
use crate::prelude::*;

const SOURCE: &str = "have fn positive_identity(x R+) R+ = x\nforall x R+:\n    positive_identity(x) + 0 = x\nlet positive_anonymous = fn(x R+) R+ {x}\npositive_anonymous(1) = 1\npositive_anonymous(1) + 0 = 1\n";

fn run(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).expect("source run");
    (result, LitexToLeanCompiler::new(runtime))
}

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let (result, compiler) = run(source);
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, compiler)
}

fn selected_mut(
    result: &mut RunLitexCodeResult,
) -> &mut AddZeroRightFromEqualitiesBuiltinRuleProof {
    fn selected(
        proof: &mut EqualFactSearchedProof,
    ) -> &mut AddZeroRightFromEqualitiesBuiltinRuleProof {
        match proof {
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AddZeroRightFromEqualities(proof),
            ) => proof,
            EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::ViaPeers(proof),
            ) => selected(&mut proof.bridge.searched_proof),
            _ => panic!("actual selected AddZeroRightFromEqualities route"),
        }
    }
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(last)) = result
        .statement_results
        .last_mut()
        .expect("last source statement")
    else {
        panic!("actual last fact")
    };
    let VerifyFactResult::Equality(proof) = &mut last.verify_result else {
        panic!("actual equality result")
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("successful equality")
    };
    selected(&mut proof.searched_proof)
}

#[test]
fn add_zero_right_replays_actual_beta_and_zero_equalities_in_both_directions() {
    for (source, reversed) in [
        (SOURCE.to_string(), false),
        (
            SOURCE.replace(
                "positive_anonymous(1) + 0 = 1",
                "1 = positive_anonymous(1) + 0",
            ),
            true,
        ),
    ] {
        let (mut result, compiler) = checked(&source);
        assert_eq!(selected_mut(&mut result).reversed, reversed);
        let lean = compiler
            .compile_run(&result, "add_zero_recorded_equalities")
            .expect("actual equality certificates");
        assert!(lean.contains("Litex.addZero"));
        assert!(lean.contains("_litex_remaining"));
        assert!(lean.contains("_litex_zero"));
    }
}

#[test]
fn add_zero_right_rejects_swapped_children_and_wrong_recorded_direction() {
    let (mut result, compiler) = checked(SOURCE);
    let selected = selected_mut(&mut result);
    std::mem::swap(&mut selected.remaining_equal, &mut selected.zero_equal);
    assert_eq!(
        compiler
            .compile_run(&result, "add_zero_wrong_children")
            .unwrap_err()
            .route,
        "AddZeroRight/RequirementSubject"
    );
    let (mut result, compiler) = checked(SOURCE);
    let selected = selected_mut(&mut result);
    selected.reversed = !selected.reversed;
    assert_eq!(
        compiler
            .compile_run(&result, "add_zero_wrong_direction")
            .unwrap_err()
            .route,
        "AddZeroRight/Orientation"
    );
}

#[test]
fn add_zero_right_rejects_a_missing_successful_zero_certificate() {
    let (mut result, compiler) = checked(SOURCE);
    let (failed, _) = run("0 = 1\n");
    assert!(!failed.success && failed.session_error.is_none());
    let ExecStmtResult::Fact(ExecFactStmtResult::Failed(failed_child)) = failed
        .statement_results
        .into_iter()
        .next()
        .expect("failed fact")
    else {
        panic!("actual failed child result")
    };
    selected_mut(&mut result).zero_equal = failed_child;
    assert!(compiler
        .compile_run(&result, "add_zero_missing_child")
        .is_err());
}

#[test]
fn add_zero_left_replays_original_equalities_in_both_directions() {
    for (left, right) in [
        ("0 + positive_anonymous(1)", "1"),
        ("1", "0 + positive_anonymous(1)"),
    ] {
        let source = SOURCE.replace(
            "positive_anonymous(1) + 0 = 1",
            &format!("{left} = {right}"),
        );
        let (result, compiler) = checked(&source);
        let lean = compiler.compile_run(&result, "add_zero_left").unwrap();
        assert!(lean.contains("Litex.zeroAdd"));
    }
}
