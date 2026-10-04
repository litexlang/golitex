use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::calculate_closed_atomic_fact::calculate_closed_atomic_fact;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
use crate::json_output::{emit_run_detailed, emit_run_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn check(source: &str, expected: bool) -> String {
    let source = source.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut rt = runtime(OutputLanguage::English);
            let result = rt.run_litex_code(&source).unwrap();
            let detailed = emit_run_detailed(&result, &rt, "eval", None);
            assert_eq!(result.success, expected, "{source}\n{detailed}");
            assert!(result.session_error.is_none(), "{source}\n{detailed}");
            detailed
        })
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn exact_roots_accept_reduced_fractional_and_decimal_exponents() {
    for source in [
        "8^(1/3)=2",
        "16^(3/4)=8",
        "(1/27)^(-1/3)=3",
        "(8/27)^(2/3)=4/9",
        "(4/9)^(1/2)=2/3",
        "8^(2/6)=2",
        "8^((-2)/(-6))=2",
        "16^(0.75)=8",
        "0.125^(1/3)=1/2",
        "(81/16)^(3/4)=27/8",
        "8^(-2/3)=1/4",
        "8^(1/3)+1/3=7/3",
        "(4/9)^(1/2)<3/4",
        "8^(1/3) $in N+",
        "8^(1/3)!=3",
        "floor((4/9)^(1/2))=0",
        "gcd(8^(1/3),6)=2",
        "((8/27)^(2/3))^(1/2)=2/3",
    ] {
        check(source, true);
    }
}

#[test]
fn root_first_avoids_unnecessary_overflow_and_factorization_limits() {
    for source in [
        "8^(100/3)=1267650600228229401496703205376",
        "8^(-100/3)=1/1267650600228229401496703205376",
        "(2^126)^(1/126)=2",
        "(1000000007^3)^(1/3)=1000000007",
        "1^(1/170141183460469231731687303715884105727)=1",
    ] {
        check(source, true);
    }
    for source in [
        "eval 8^(127/3)",
        "eval 8^(100000/3)",
        "eval 2^(1/127)",
        "eval 2^(1/170141183460469231731687303715884105727)",
    ] {
        check(source, false);
    }
}

#[test]
fn incorrect_values_irrational_results_and_invalid_domains_reject() {
    for source in [
        "8^(1/3)=3",
        "8^(1/3)=-2",
        "16^(3/4)=4",
        "(8/27)^(2/3)=2/3",
        "2^(1/3)=1",
        "eval 2^(1/3)",
        "eval (2/9)^(1/2)",
        "eval (4/3)^(1/2)",
        "(-8)^(1/3)=-2",
        "eval (-8)^(1/3)",
        "eval 0^(1/3)",
        "eval 0^(-1/3)",
        "(1/0)^(1/3)=1",
        "8^(1/0)=1",
        "0*((1/0)^(1/3))=0",
        "0*(0^(-1/3))=0",
    ] {
        check(source, false);
    }
    // Defined irrational powers may be retained as objects without evaluation.
    check("let u=2^(1/3)", true);
    check("let u=(2/9)^(1/2)", true);
}

#[test]
fn existing_integer_power_domains_keep_their_behavior() {
    for source in [
        "0^0=1",
        "0^(0/3)=1",
        "0^3=0",
        "(-2)^3=-8",
        "(-2)^(-3)=-1/8",
        "(-8)^(6/3)=64",
        "i^2=-1",
    ] {
        check(source, true);
    }
    for source in ["0^(-1)=0", "eval 2^100000"] {
        check(source, false);
    }
}

#[test]
fn eval_shares_exact_values_and_does_not_publish_facts() {
    for (source, expected) in [
        ("eval 8^(1/3)", "2"),
        ("eval 16^(3/4)", "8"),
        ("eval (1/27)^(-1/3)", "3"),
        ("eval (4/9)^(1/2)", "2 / 3"),
        ("eval 8^(-2/3)", "1 / 4"),
        ("eval 0.125^(1/3)", "1 / 2"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = rt.run_litex_code(source).unwrap();
        assert!(result.success, "{source}");
        let normal = emit_run_normal(&result, &rt, "eval", None);
        assert!(
            normal.contains(&format!("\"evaluated_object\": \"{expected}\"")),
            "{normal}"
        );
        assert!(normal.contains("\"stores\": []"), "{normal}");
        assert!(rt
            .execution_environments_stack
            .iter()
            .all(|env| env.facts.facts_by_id.is_empty()));
    }
}

#[test]
fn direct_calculation_preserves_domain_evidence_and_declines_symbols() {
    let mut rt = runtime(OutputLanguage::English);
    let tokens = Tokenizer::new()
        .tokenize("8^(1/3)=2", rt.current_file.clone())
        .unwrap();
    let statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(goal) = &statements[0] else {
        panic!("fact")
    };
    let Fact::AtomicFact(atomic) = goal else {
        panic!("atomic")
    };
    assert!(calculate_closed_atomic_fact(atomic).is_some());
    let proof = rt
        .verify_fact(goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap();
    assert!(!proof.is_failed());

    assert!(rt.run_litex_code("have x Q+").unwrap().success);
    let tokens = Tokenizer::new()
        .tokenize("x^(1/3)=2", rt.current_file.clone())
        .unwrap();
    let statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::AtomicFact(goal)) = &statements[0] else {
        panic!("atomic")
    };
    assert!(calculate_closed_atomic_fact(goal).is_none());

    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime(language);
        let result = rt.run_litex_code("8^(1/3)=2").unwrap();
        assert!(result.success);
        let detailed = emit_run_detailed(&result, &rt, "eval", None);
        assert!(detailed.contains("by_closed_calculation"), "{detailed}");
        assert!(detailed.contains("8 $in Q+"), "{detailed}");
        assert!(detailed.contains("1 / 3 $in Q"), "{detailed}");
    }
}

#[test]
fn run_examples_closed_rational_power_calculation() {
    check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/closed_rational_power_calculation.lit"
        )),
        true,
    );
}
