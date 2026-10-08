use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn accepts_at(runtime: &mut Runtime, code: &str, level: VerifyStateLevel) -> bool {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = runtime.parse(&tokens).unwrap().remove(0) else {
        panic!("membership fact");
    };
    !runtime
        .verify_fact(&fact, VerifyState::new(level))
        .unwrap()
        .is_failed()
}

#[test]
fn anonymous_fn_in_finite_seq_constructor() {
    let mut runtime = runtime();
    let run = runtime
        .run_litex_code(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/stmt_nodes/definition/finite_sequence_record_return.lit"
        )))
        .unwrap();
    assert!(run.success && run.session_error.is_none());
}

#[test]
fn anonymous_fn_in_finite_seq_matches_exact_signature_at_builtin() {
    let mut runtime = runtime();
    assert!(runtime.run_litex_code("have value R").unwrap().success);
    assert!(accepts_at(
        &mut runtime,
        "fn(j closed_range(1, 3)) R {value} $in finite_seq(R, 3)",
        VerifyStateLevel::BuiltinRule,
    ));
    assert!(accepts_at(
        &mut runtime,
        "fn(j closed_range(1, 0)) R {value} $in finite_seq(R, 0)",
        VerifyStateLevel::BuiltinRule,
    ));
    for code in [
        "fn(j closed_range(0, 3)) R {value} $in finite_seq(R, 3)",
        "fn(j closed_range(1, 3)) R {value} $in finite_seq(Z, 3)",
    ] {
        assert!(
            !accepts_at(&mut runtime, code, VerifyStateLevel::BuiltinRule),
            "{code}"
        );
    }
}

#[test]
fn anonymous_fn_in_finite_seq_is_declared_signature_property_and_not_direct_truth() {
    let mut runtime = runtime();
    assert!(
        runtime
            .run_litex_code("have value R\n$is_set(R)")
            .unwrap()
            .success
    );
    let code = "fn(j closed_range(1, 3)) R {value} $in finite_seq(R, 3)";
    assert!(!accepts_at(&mut runtime, code, VerifyStateLevel::Direct));
    assert!(accepts_at(
        &mut runtime,
        code,
        VerifyStateLevel::KnownSpecialProperty
    ));
}

#[test]
fn anonymous_fn_in_finite_seq_constructor_keeps_length_law() {
    let mut runtime = runtime();
    let source = "$is_set(R)\nstruct WrongList<n N>:\n    length N\n    entries finite_seq(R, n)\n    <=>:\n        length = n\ntemplate<n N>:\n    have fn bad(value R) &WrongList<n> = (n + 1, fn(j closed_range(1, n)) R {value})\n";
    let run = runtime.run_litex_code(source).unwrap();
    assert!(!run.success && run.session_error.is_none());
}

#[test]
fn anonymous_fn_in_finite_seq_keeps_mandatory_body_wd() {
    let mut runtime = runtime();
    for code in [
        "fn(j closed_range(1, 1)) R {1 / 0} $in finite_seq(R, 1)",
        "fn(j closed_range(1, 0)) R {1 / 0} $in finite_seq(R, 0)",
    ] {
        let run = runtime.run_litex_code(code).unwrap();
        assert!(!run.success && run.session_error.is_none(), "{code}");
    }
}
