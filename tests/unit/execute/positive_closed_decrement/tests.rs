use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn positive_closed_decrements_verify_for_real_and_integer_binders() {
    for carrier in ["R", "Z"] {
        for offset in ["2", "0.25", "(1 + 1)", "(4 / 2)"] {
            let code = format!("forall x {carrier}:\n    x - {offset} < x\n");
            let run = runtime().run_litex_code(&code).unwrap();
            assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
            assert!(run.success, "{code}");
        }
    }
}

#[test]
fn zero_negative_unknown_offsets_and_nonreal_order_do_not_pass() {
    for code in [
        "forall x R:\n    x - 0 < x\n",
        "forall x R:\n    x - (-2) < x\n",
        "forall x, c R:\n    x - c < x\n",
        "forall x, y R:\n    x - 2 < y\n",
        "forall x C:\n    x - 2 < x\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(!run.success, "incorrect admission: {code}");
    }
}

#[test]
fn fibonacci_uses_the_original_two_step_recursive_domain() {
    let code = "have fn fib(n Z: n >= 0) R by induc n from 0:\n    case n < 2: 1\n    case n >= 2: fib(n - 2) + fib(n - 1)\nfib(0) = 1\nfib(1) = 1\nfib(2) = fib(0) + fib(1) = 2\n";
    let run = runtime().run_litex_code(code).unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success);
}

#[test]
fn equal_and_increasing_recursive_measures_are_rejected() {
    for recursive_arg in ["n", "n + 2", "n - (-2)"] {
        let code = format!("have fn bad(n Z: n >= 0) R by induc n from 0:\n    case n < 2: 0\n    case n >= 2: bad({recursive_arg})\n");
        let run = runtime().run_litex_code(&code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(!run.success, "incorrect recursive admission: {code}");
    }
}

#[test]
fn subtraction_evidence_records_the_actual_positive_offset() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have x R\nx - (1 + 1) < x\n").unwrap();
    assert!(run.success);
    let detail = crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt)
        .stringify();
    assert!(detail.contains("SubtractPositiveClosedLess"), "{detail}");
    assert!(detail.contains("\"normalized_subtrahend\":\"2\""), "{detail}");
    assert!(detail.contains("\"subtrahend\":\"1 + 1\""), "{detail}");
    let old = rt.run_litex_code("x - 1 < x\n").unwrap();
    assert!(old.success);
    let detail = crate::json_output::project_stmt_detailed(&old.statement_results[0], &rt)
        .stringify();
    assert!(detail.contains("SubtractOneLess"), "{detail}");
}
