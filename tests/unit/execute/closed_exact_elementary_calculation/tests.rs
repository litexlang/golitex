use crate::ast::fact::Fact;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::calculate_closed_atomic_fact::calculate_closed_atomic_fact;
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
fn fractions_round_without_decimal_approximation() {
    for source in [
        "floor(-7/3)=-3",
        "ceil(-7/3)=-2",
        "floor(7/3)=2",
        "ceil(7/3)=3",
        "floor(-6/3)=-2",
        "ceil(-6/3)=-2",
        "floor(0/3)=0",
        "ceil(0/3)=0",
        "floor(1/3)=0",
        "ceil(-1/3)=0",
        "sign(1/3-1/2)=-1",
        "sign(1/3-2/6)=0",
        "sign(1/2-1/3)=1",
        "floor(1/3)+ceil(2/3)=1",
        "floor(-7/3) $in Z",
        "ceil(-1/3) $in N",
        "not floor(-7/3) $in N",
    ] {
        check(source, true);
    }
    for source in [
        "floor(-7/3)=-2",
        "ceil(-7/3)=-3",
        "sign(1/3-1/2)=1",
        "floor(1/0)=0",
    ] {
        check(source, false);
    }
}

#[test]
fn integer_operations_check_the_exact_operand_values() {
    for source in [
        "gcd((1/3)*6,8)=2",
        "lcm((1/3)*6,8)=8",
        "gcd((1/3)*(-6),8)=2",
        "quot((1/3)*(-21),3)=-3",
        "((1/3)*(-21))%3=2",
        "((1/3)*(-21))%(-3)=2",
        "factorial((1/3)*9)=6",
        "gcd(0,6)=6",
        "lcm(0,0)=0",
        "gcd(floor(-7/3),6)=3",
    ] {
        check(source, true);
    }
    for source in [
        "gcd(1/3,8)=1",
        "lcm(1/3,8)=8",
        "quot(7,0)=0",
        "quot(7,-3)=-3",
        "(1/3)%2=0",
        "7%0=0",
        "factorial(1/3)=1",
        "factorial(-1)=1",
        "gcd(0,0)=0",
    ] {
        check(source, false);
    }
}

#[test]
fn numeric_radicals_normalize_and_keep_the_principal_root() {
    for source in [
        "sqrt(1/9)=1/3",
        "sqrt(4/9)=2/3",
        "sqrt(1/2)=sqrt(2)/2",
        "sqrt(8)=2*sqrt(2)",
        "sqrt(12)+sqrt(27)=5*sqrt(3)",
        "sqrt(12)-sqrt(27)=-sqrt(3)",
        "sqrt(2)*sqrt(8)=4",
        "sqrt(2)*sqrt(3)=sqrt(6)",
        "1/sqrt(2)=sqrt(2)/2",
        "sqrt(2)^(-1)=sqrt(2)/2",
        "sqrt(2)^3=2*sqrt(2)",
        "(3-2*sqrt(2))*(3+2*sqrt(2))=1",
        "sqrt(2)+sqrt(3) != sqrt(5)",
        "sqrt(0)=0",
        "sqrt(sqrt(16))=2",
    ] {
        check(source, true);
    }
    for source in [
        "sqrt(8)=sqrt(2)",
        "sqrt(1/9)=-1/3",
        "sqrt(2)+sqrt(3)=sqrt(5)",
        "sqrt(-1)=1",
        "sqrt(1/0)=0",
        "sqrt(0)^(-1)=0",
        "1/sqrt(0)=0",
        "0*sqrt(-1)=0",
    ] {
        check(source, false);
    }
}

#[test]
fn numeric_complex_parts_share_coordinate_arithmetic() {
    for source in [
        "re((1+2*i)*(3-i))=5",
        "img((1+2*i)*(3-i))=5",
        "re((1+2*i)/(3-i))=1/10",
        "img((1+2*i)/(3-i))=7/10",
        "re((1/3+i/2)/(1+i))=5/12",
        "img((1/3+i/2)/(1+i))=1/12",
        "re((1+i)^2)=0",
        "img((1+i)^2)=2",
        "re((1+i)^(-1))=1/2",
        "img((1+i)^(-1))=-1/2",
        "1/(1+i)=(1-i)/2",
        "i^(-3)=i",
        "re((1+2*i)/(3-i)) $in Q",
        "re((1+2*i)/(3-i)) > 0",
    ] {
        check(source, true);
    }
    for source in [
        "img((1+2*i)/(3-i))=1/10",
        "re(1/(i-i))=0",
        "img(1/(i-i))=0",
        "0*re(1/(i-i))=0",
    ] {
        check(source, false);
    }
}

#[test]
fn rational_logs_use_exact_prime_valuation_ratios() {
    for source in [
        "log(4,2)=1/2",
        "log(8,4)=2/3",
        "log(1/3,27)=-3",
        "log(4,1/8)=-3/2",
        "log(4/9,8/27)=3/2",
        "log(2/3,9/4)=-2",
        "log(1/3,1)=0",
        "log(1/3,1/3)=1",
        "log(100,10)=1/2",
        "log(16,8)=3/4",
        "log(4,2)+log(8,4)=7/6",
        "log(8,4) $in Q",
        "log(1/3,27)<0",
    ] {
        check(source, true);
    }
    for source in [
        "log(8,4)=3/2",
        "log(2,3)=1",
        "log(4,2)=-1/2",
        "log(1,2)=0",
        "log(0,2)=0",
        "log(-2,4)=2",
        "log(2,0)=0",
        "log(2,-4)=2",
        "0*log(1,2)=0",
    ] {
        check(source, false);
    }
}

#[test]
fn eval_returns_exact_values_and_publishes_no_fact() {
    for (source, expected) in [
        ("eval floor(-7/3)", "-3"),
        ("eval ceil(-7/3)", "-2"),
        ("eval gcd((1/3)*6,8)", "2"),
        ("eval sqrt(1/9)", "1 / 3"),
        ("eval sqrt(12)+sqrt(27)", "5 * sqrt (3)"),
        ("eval re((1+2*i)*(3-i))", "5"),
        ("eval img((1+2*i)/(3-i))", "7 / 10"),
        ("eval (1+2*i)/(3-i)", "1 / 10 + 7 / 10 * i"),
        ("eval (1+i)^2", "2 * i"),
        ("eval i^(-3)", "i"),
        ("eval log(8,4)", "2 / 3"),
        ("eval log(1/3,27)", "-3"),
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
    }
    for source in [
        "eval floor(1/0)",
        "eval log(2,3)",
        "eval 2^100000",
        "eval re(1/(i-i))",
    ] {
        check(source, false);
    }
}

#[test]
fn pure_leaf_declines_symbolic_undefined_and_exhausted_calculations() {
    let mut rt = runtime(OutputLanguage::English);
    for source in [
        "floor(-7/3)=-3",
        "sqrt(12)+sqrt(27)=5*sqrt(3)",
        "re((1+2*i)*(3-i))=5",
        "log(8,4)=2/3",
    ] {
        let goal = atomic(&mut rt, source);
        assert!(calculate_closed_atomic_fact(&goal).is_some(), "{source}");
    }
    rt.run_litex_code("have x R").unwrap();
    for source in [
        "floor(x)=0",
        "sqrt(x)=0",
        "log(2,x)=0",
        "re(x)=0",
        "floor(1/0)=0",
        "sqrt(-1)=1",
        "log(1,2)=0",
        "gcd(0,0)=0",
        "2^100000=2",
        "sqrt(1000000007)=sqrt(1000000007)",
        "1/(1+sqrt(2))=0",
    ] {
        let goal = atomic(&mut rt, source);
        assert!(calculate_closed_atomic_fact(&goal).is_none(), "{source}");
    }
}

#[test]
fn radical_provenance_projects_in_both_languages() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = runtime(language);
        let result = rt.run_litex_code("sqrt(12)+sqrt(27)=5*sqrt(3)").unwrap();
        assert!(result.success);
        let detailed = emit_run_detailed(&result, &rt, "eval", None);
        assert!(detailed.contains("by_closed_calculation"), "{detailed}");
        assert!(
            detailed.contains("\"representation\": \"radical\""),
            "{detailed}"
        );
        assert!(detailed.matches("5 * sqrt (3)").count() >= 2, "{detailed}");
        let normal = emit_run_normal(&result, &rt, "eval", None);
        let explanation = match language {
            OutputLanguage::English => "by_closed_calculation",
            OutputLanguage::Chinese => "封闭计算",
        };
        assert!(normal.contains(explanation), "{normal}");
    }
}

#[test]
fn run_examples_closed_exact_elementary_tracers() {
    for source in [
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/closed_fraction_rounding_calculation.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/closed_radical_calculation.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/closed_complex_parts_calculation.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/closed_rational_log_calculation.lit"
        )),
    ] {
        check(source, true);
    }
}

fn atomic(rt: &mut Runtime, source: &str) -> crate::ast::fact::AtomicFact {
    let tokens = Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let statements = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::AtomicFact(fact)) = &statements[0] else {
        panic!("atomic")
    };
    fact.clone()
}
