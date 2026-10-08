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
fn real_power_wd_accepts_symbolic_positive_and_nonnegative_domains() {
    for source in [
        "forall a R+,t R:\n    a^t=a^t\n",
        "forall a R+,t R:\n    a^t $in R\n",
        "forall a R,t R+:\n    a>=0\n    =>:\n        a^t=a^t\n",
        "forall a R,t R+:\n    0<=a\n    =>:\n        a^t $in R\n",
        "forall x R+:\n    x^(1/2)=x^(1/2)\n",
        "forall t R+:\n    0^t=0^t\n",
        "forall a,t R:\n    a>0\n    =>:\n        a^t=a^t\n",
        "forall a,t R:\n    0<a\n    =>:\n        a^t=a^t\n",
        "forall x R:\n    exp(x)=e^x\n",
        "have fn real_power(a R+,t R) R=a^t\nreal_power(2,1/2)=2^(1/2)\n",
    ] {
        check(source, true);
    }
}

#[test]
fn real_power_wd_retains_actual_domain_requirements() {
    use crate::ast::fact::AtomicFact;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicExceptEqualityFactResult;
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        ArithmeticOperatorObjWellDefinedProofByDef, ObjWellDefinedProof, ObjWellDefinedProofByDef,
        VerifyObjWellDefinedResult,
    };
    use crate::execute::execute_fact_stmt::VerifyFactResult;
    for (prefix, expected) in [
        ("have a R+\nhave t R\n", vec!["a $in R+", "t $in R"]),
        (
            "have a R=0\nhave t R+\n",
            vec!["a $in R", "0 <= a", "t $in R+"],
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(prefix).unwrap().success);
        let tokens = Tokenizer::new()
            .tokenize("a^t=a^t", rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(goal))) =
            rt.parse(&tokens).unwrap().remove(0)
        else {
            panic!("power equality")
        };
        let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Pow(proof),
                ),
            ..
        }) = rt
            .verify_obj_well_definedness(&goal.left, VerifyState::top_level())
            .unwrap()
        else {
            panic!("selected power WD proof")
        };
        assert_eq!(proof.child_obj_well_defined.len(), 2);
        let actual: Vec<_> = proof
            .requirement_fact_verified
            .iter()
            .map(|requirement| {
                let VerifyFactResult::AtomicExceptEquality(result) = requirement else {
                    panic!("atomic requirement")
                };
                let VerifyAtomicExceptEqualityFactResult::Success(proved) = result.as_ref() else {
                    panic!("proved requirement")
                };
                proved.fact.readable_string()
            })
            .collect();
        assert_eq!(actual, expected);
    }
}

#[test]
fn real_power_wd_preserves_inherited_permissions() {
    use crate::ast::fact::AtomicFact;
    for (prefix, expected) in [("have a R+\nhave t R\n", true), ("have a,t R\n", false)] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(rt.run_litex_code(prefix).unwrap().success);
        let tokens = Tokenizer::new()
            .tokenize("a^t=a^t", rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(goal))) =
            rt.parse(&tokens).unwrap().remove(0)
        else {
            panic!("power equality")
        };
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
            VerifyStateLevel::BuiltinRule,
        ] {
            let proof = rt
                .verify_obj_well_definedness(&goal.left, VerifyState::new(level))
                .unwrap();
            assert_eq!(!proof.is_failed(), expected, "{prefix}: {level:?}");
        }
    }
}

#[test]
fn real_power_wd_rejects_missing_guards_and_illegal_domains() {
    for source in [
        "forall a,t R:\n    a^t=a^t\n",
        "forall a R,t R+:\n    a^t=a^t\n",
        "forall a,t R:\n    a>=0\n    =>:\n        a^t=a^t\n",
        "forall a R+,t C:\n    a^t=a^t\n",
        "(-8)^(1/3)=(-8)^(1/3)",
        "i^(1/2)=i^(1/2)",
        "0^(-1/3)=0^(-1/3)",
        "0^(-1)=0^(-1)",
        "2^i=2^i",
        "(1/0)^(1/2)=(1/0)^(1/2)",
        "8^(1/0)=8^(1/0)",
        "0^0=0",
    ] {
        check(source, false);
    }
}

#[test]
fn real_power_wd_failed_binding_is_discarded() {
    let mut rt = runtime(OutputLanguage::English);
    let failed = rt.run_litex_code("have a,t R\nlet result=a^t").unwrap();
    assert!(!failed.success && failed.session_error.is_none());
    let reused = rt
        .run_litex_code("let result=2^(1/2)\nresult=result")
        .unwrap();
    assert!(reused.success && reused.session_error.is_none());
    assert!(!rt.run_litex_code("result=0").unwrap().success);
}

#[test]
fn eval_shares_exact_values_and_publishes_the_checked_equality() {
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
        let crate::execute::ExecStmtResult::Command(
            crate::execute::execute_eval_stmt::ExecCommandStmtResult::Eval(
                crate::execute::execute_eval_stmt::ExecEvalStmtResult::Success(evaluated),
            ),
        ) = &result.statement_results[0]
        else {
            panic!("eval success");
        };
        assert!(rt
            .top_exec_env()
            .facts
            .facts_by_id
            .contains_key(&evaluated.evaluated_equal_fact.fact_id));
        let stored: Fact = evaluated.evaluated_equal_fact.clone().into();
        assert!(normal.contains(&stored.readable_string()), "{normal}");
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

#[test]
fn real_power_wd_preserves_maintained_tracer() {
    check(
        include_str!("../../../../examples/wd/pow_real_domains.lit"),
        true,
    );
}
