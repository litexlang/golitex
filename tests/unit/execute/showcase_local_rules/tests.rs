use crate::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::VerifyState;
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
fn equal(rt: &mut Runtime, source: &str) -> EqualFact {
    let tokens = Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let stmts = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(eq))) = &stmts[0] else {
        panic!("expected equality");
    };
    eq.clone()
}
fn check(code: &str, expected: bool) -> String {
    let mut rt = runtime();
    let result = rt.run_litex_code(code).unwrap();
    let detailed =
        crate::json_output::emit_run_detailed(&result, &rt, "showcase local rules", None);
    assert!(result.session_error.is_none(), "{detailed}");
    assert_eq!(result.success, expected, "{code}\n{detailed}");
    assert_eq!(rt.execution_environments_stack.len(), 1);
    detailed
}

#[test]
fn cosine_integer_offset_positive_and_evidence() {
    let detailed = check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_strategy/cos_zero_integer_offset.lit"
        )),
        true,
    );
    assert!(detailed.contains("CosZeroIntegerOffset"));
    assert!(detailed.contains("RationalWithNonzeroPremises"));
    assert!(detailed.contains("PiNonzero"));
    assert!(detailed.contains("proof_of_requirement_facts"));
    check("0 = cos(3*pi/2)", true);
}
#[test]
fn cosine_rejects_missing_integer_evidence_and_wrong_zeros() {
    for code in [
        "cos(0)=0",
        "cos(pi)=0",
        "cos(pi/3)=0",
        "forall x R:\n    cos(x)=0",
        "forall k R:\n    cos((k+1/2)*pi)=0",
    ] {
        check(code, false);
    }
}
#[test]
fn tuple_coordinates_have_independent_proofs() {
    let detailed = check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_strategy/tuple_component_calculation.lit"
        )),
        true,
    );
    assert!(detailed.contains("TupleComponentEquality"));
    assert!(detailed.contains("closed_decimal"));
    check("(1+3,2+4)=(4,7)", false);
    check("(1+3,2+4)=(4,6,0)", false);
    check("(1,2)[1]+(3,4)[1]=1+3", true);
}

#[test]
fn natural_power_laws_cover_existing_domains_and_keep_evidence() {
    let detailed = check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/natural_power_laws.lit"
        )),
        true,
    );
    for rule in [
        "PowerProductSameBase",
        "PowerOfPower",
        "PowerOfProduct",
        "proof_of_requirement_facts",
    ] {
        assert!(detailed.contains(rule), "{rule}");
    }
    for carrier in ["R+", "R-", "R*", "C*", "Z", "Q", "N"] {
        check(
            &format!("forall a {carrier}, m,n N:\n    a^(m+n)=a^m*a^n\n"),
            true,
        );
    }
    check("forall a R, n N:\n    a^n*a^n=a^(n+n)", true);
    for code in [
        "0^(-1)=1",
        "(-2)^2=-4",
        "0^0=0",
        "forall a C, m,n N:\n    a^(m+n)=a^m+a^n",
        "forall a R+, m,n R:\n    a^(m+n)=a^m*a^n",
    ] {
        check(code, false);
    }
}
#[test]
fn full_add2_chain_and_projection_boundaries() {
    let detailed = check(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_strategy/add2_calculation_chain.lit"
        )),
        true,
    );
    for node in [
        "TupleComponentEquality",
        "ArithmeticCongruence",
        "LiteralTupleProjectionMembership",
        "TupleComponentAtIndex",
    ] {
        assert!(detailed.contains(node), "{node}");
    }
    let definition = "have fn add2(u,v cart(R,R)) cart(R,R)=(u[1]+v[1],u[2]+v[2])\n";
    check(
        &format!("{definition}add2((1,2),(3,4))=(1+3,2+4)=(4,7)"),
        false,
    );
    check(&format!("{definition}add2((1,2,3),(3,4))=(4,6)"), false);
    for code in [
        "(1,-2)[2] $in N",
        "(1,2)[0]=1",
        "(1,2)[3]=1",
        "(1/0+1,2)=(1/0+1,2)",
        "1+2=1*2",
    ] {
        check(code, false);
    }
}
#[test]
fn local_strategies_respect_existing_depth_boundary() {
    use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
    let mut rt = runtime();
    let depth = StrategySearch { depth: 0 };
    let eq = equal(&mut rt, "cos(3*pi/2)=0");
    assert!(rt
        .search_equal_fact_by_cos_zero_integer_offset(&eq, depth)
        .unwrap()
        .is_none());
    let eq = equal(&mut rt, "(1+3,2+4)=(4,6)");
    assert!(rt
        .search_equal_fact_by_tuple_components(&eq, depth)
        .unwrap()
        .is_none());
    let eq = equal(&mut rt, "(1,2)[1]+(3,4)[1]=1+3");
    assert!(rt
        .search_equal_fact_by_arithmetic_congruence(&eq, depth)
        .unwrap()
        .is_none());
    // Known-only matching still cannot synthesize arithmetic coordinate proofs.
    let eq = equal(&mut rt, "(1+3,2+4)=(4,6)");
    assert!(rt
        .verify_equal_fact(&eq, VerifyState::top_level().known_only_no_wd())
        .unwrap()
        .is_failed());
}
