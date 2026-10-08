use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn check(code: &str, expected: bool) {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = rt
        .run_litex_code(code)
        .expect("valid syntax and no internal error");
    assert!(result.session_error.is_none(), "{:?}", result.session_error);
    assert_eq!(
        result.success,
        expected,
        "{code}\n{}",
        crate::json_output::emit_run_detailed(&result, &rt, "showcase regression", None)
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn induction_recovers_order_and_nested_arithmetic_binders() {
    for goal in [
        "k >= k",
        "k <= k",
        "k $in Z",
        "2^k = 2^k",
        "(k + 1) * 2 = (k + 1) * 2",
        "k = k or k > k",
        "k = k = k",
    ] {
        check(&format!("by induc k from 0:\n    ? {goal}\n"), true);
    }
    check(
        "by induc k from 0:\n    ? not k > k\n    k <= k\n    k + 1 <= k + 1\n",
        true,
    );
    check("by strong_induc k from 0:\n    ? k >= k\n", true);
}

#[test]
fn induction_rejects_false_base_false_step_and_noninteger_start() {
    for code in [
        "by induc k from 0:\n    ? k > 0\n",
        "by induc k from 0:\n    ? k = 0\n",
        "by induc k from 0.5:\n    ? k = k\n",
        "by strong_induc k from 0:\n    ? k = 0\n",
    ] {
        check(code, false);
    }
    check("by induc k from 0:\n    ? k = 0\n0 = 1\n", false);
}

#[test]
fn dependent_claim_and_theorem_types_are_checked_in_order() {
    check(
        "claim:\n    ? forall A nonempty_set, a A:\n        a = a\n    a = a\n",
        true,
    );
    check("thm dependent_identity:\n    ? forall A nonempty_set, f fn(x A) A, a A:\n        f(a) = f(a)\n", true);
    check(
        "claim:\n    ? forall A nonempty_set, a A, b A:\n        a = b\n",
        false,
    );
    check(
        "claim:\n    ? forall A nonempty_set, a A:\n        a = a\n0 = 1\n",
        false,
    );
}

#[test]
fn quotient_order_requires_correct_numerator_and_strict_denominator_sign() {
    for (premises, goal) in [
        ("0 <= a\n    0 < c", "0 <= a / c"),
        ("a <= 0\n    0 < c", "a / c <= 0"),
        ("a <= 0\n    c < 0", "0 <= a / c"),
        ("0 <= a\n    c < 0", "a / c <= 0"),
    ] {
        check(
            &format!("forall a, c R:\n    {premises}\n    =>:\n        {goal}\n"),
            true,
        );
    }
    check(
        "forall a, c R:\n    0 <= a\n    c < 0\n    =>:\n        0 <= a / c\n",
        false,
    );
    check(
        "forall a, c R:\n    0 <= a\n    0 <= c\n    =>:\n        0 <= a / c\n",
        false,
    );
    check(
        "forall a, c R:\n    c != 0\n    =>:\n        0 <= a / c\n",
        false,
    );
    check(
        "forall a R:\n    a < 0\n    =>:\n        0 <= a / 2\n",
        false,
    );
}

#[test]
fn real_order_complements_require_a_known_fact() {
    for (premise, goal) in [
        ("not a <= b", "a > b"),
        ("a > b", "not a <= b"),
        ("not a >= b", "a < b"),
        ("a < b", "not a >= b"),
        ("not a < b", "a >= b"),
        ("a >= b", "not a < b"),
        ("not a > b", "a <= b"),
        ("a <= b", "not a > b"),
    ] {
        check(
            &format!("forall a, b R:\n    {premise}\n    =>:\n        {goal}\n"),
            true,
        );
    }
    for goal in ["a > b", "not a <= b", "a <= b", "not a > b"] {
        check(&format!("forall a, b R:\n    {goal}\n"), false);
    }
    check(
        "forall a, b R:\n    a <= b\n    =>:\n        a < b\n",
        false,
    );
}

#[test]
fn all_quantifier_wd_paths_introduce_dependent_groups_locally() {
    use crate::ast::stmt::Stmt;
    use crate::tokenize::Tokenizer;
    for code in [
        "forall A nonempty_set, a A:\n    a = a\n",
        "exist A nonempty_set, a A st {a = a}\n",
        "exist! A nonempty_set, a A st {a = a}\n",
        "not exist A nonempty_set, a A st {a = a}\n",
        "not forall A nonempty_set, a A:\n    a = a\n",
        "forall A nonempty_set, a A:\n    =>:\n        a = a\n    <=>:\n        a = a\n",
    ] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(fact) = &statements[0] else {
            panic!("expected a fact");
        };
        let wd = rt
            .verify_fact_well_definedness(
                fact,
                crate::execute::execute_by_stmt::proof_verify_state(),
            )
            .unwrap();
        assert!(!wd.is_failed(), "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(!rt.execution_environments_stack[0]
            .definitions
            .identifiers
            .contains_key("A"));
        assert!(!rt.execution_environments_stack[0]
            .definitions
            .identifiers
            .contains_key("a"));
    }
}

#[test]
fn order_complement_rejects_nonreal_carriers_and_keeps_premise_evidence() {
    check(
        "forall a, b C:\n    not a <= b\n    =>:\n        a > b\n",
        false,
    );
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = rt
        .run_litex_code("forall a, b R:\n    not a <= b\n    =>:\n        a > b\n")
        .unwrap();
    assert!(result.success);
    let detailed = crate::json_output::emit_run_detailed(&result, &rt, "order complement", None);
    assert!(detailed.contains("FromKnownOrderComplement"));
    assert!(detailed.contains("premise_proof"));
    assert!(detailed.contains("real_carrier_proofs"));
}

#[test]
fn positive_base_power_laws_allow_zero_natural_exponent() {
    check(
        "forall a R+, k N:\n    a^k * a^0 = a^(k + 0)\n    (a^k)^0 = a^(k * 0)\n",
        true,
    );
    check("forall a, b R+, k N:\n    (a * b)^k = a^k * b^k\n", true);
    // Zero natural powers are valid; zero negative powers remain undefined.
    check("forall k N:\n    0^k * 0^(-1) = 0^(k - 1)\n", false);
}

#[test]
fn nonnegative_integer_refinement_requires_both_premises() {
    check("forall k Z:\n    0 <= k\n    =>:\n        k $in N\n", true);
    check("forall x R:\n    0 <= x\n    =>:\n        x $in N\n", false);
    check("forall k Z:\n    k < 0\n    =>:\n        k $in N\n", false);
}

#[test]
fn converse_order_spelling_reuses_bounded_structural_strategies() {
    check(
        "forall a, b, c R:\n    a >= b\n    0 <= c\n    =>:\n        a * c >= b * c\n",
        true,
    );
    check(
        "forall a, b R:\n    a > b\n    0 <= b\n    =>:\n        a^2 > b^2\n",
        true,
    );
    check(
        "forall a, b, c R:\n    a > b\n    c < 0\n    =>:\n        a * c >= b * c\n",
        false,
    );
}

#[test]
fn showcase_exponential_induction_closes_successor_goal() {
    check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/stmt_nodes/by/by_induc_order.lit"
        )),
        true,
    );
}

#[test]
fn mixed_equality_order_chain_stores_checked_endpoints() {
    for (premises, chain, conclusion) in [
        ("a >= b\n    b = c\n    c >= d", "a >= b = c >= d", "a >= d"),
        ("a < b\n    b = c\n    c <= d", "a < b = c <= d", "a < d"),
        (
            "a = b\n    b = c\n    c > d",
            "a = b = c > d",
            "a = c\n    a > d",
        ),
    ] {
        check(&format!("claim:\n    ? forall a, b, c, d R:\n        {}\n        =>:\n            {}\n    {chain}\n", premises.replace('\n', "\n    "), conclusion.replace("\n    ", "\n            ")), true);
    }
    check("claim:\n    ? forall a, b, c R:\n        a <= b\n        b >= c\n        =>:\n            a <= c\n    a <= b >= c\n", false);
    check("claim:\n    ? forall a, b, c R:\n        a <= b\n        b = c\n        =>:\n            a < c\n    a <= b = c\n", false);
    check("claim:\n    ? forall a, b, c R:\n        a <= b\n        =>:\n            a <= c\n    a <= b = c\n", false);
}

#[test]
fn original_showcase_amgm_and_group_left_cancel() {
    check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/order/am_gm.lit"
        )),
        true,
    );
    check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/wd/fact/group_left_cancel.lit"
        )),
        true,
    );
}
