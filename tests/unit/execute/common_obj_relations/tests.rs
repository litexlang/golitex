use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchedProof, EqualFactSearchedProof,
    VerifyAtomicExceptEqualityFactResult, VerifyEqualityResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    VerifyForallFactProof, VerifyForallFactResult,
};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
use crate::execute::{ExecFactStmtResult, ExecStmtResult};
use crate::json_output::explain::BuiltinRuleText;
use crate::json_output::json_keys::localize_key;
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;
use std::collections::BTreeSet;

const GCD: &str =
    "forall a,b Z,d N+:\n    a!=0\n    a%d=0\n    b%d=0\n    =>:\n        gcd(a,b)%d=0\n";
const LCM: &str = "forall a,b N+,m Z:\n    m%a=0\n    m%b=0\n    =>:\n        m%lcm(a,b)=0\n";
const SIN_POS: &str = "forall x R:\n    0<x\n    x<pi\n    =>:\n        0<sin(x)\n";
const SIN_ORDER: &str =
    "forall a,b R:\n    -pi/2<=a\n    b<=pi/2\n    a<b\n    =>:\n        sin(a)<sin(b)\n";
const LCM_NONZERO: &str = "forall a,b Z*:\n    lcm(a,b)!=0\n";
const LOG_NONZERO: &str = "forall b,x R+:\n    b!=1\n    x!=1\n    =>:\n        log(b,x)!=0\n";
const POW_NONUNIT: &str = "forall b R+,n Z*:\n    b!=1\n    =>:\n        b^n!=1\n";
const LOG_CHANGE: &str =
    "forall a,b,x R+:\n    a!=1\n    b!=1\n    =>:\n        log(a,x)=log(b,x)/log(b,a)\n";
const LOG_POWER: &str = "forall b,x R+,n N+:\n    b!=1\n    =>:\n        log(b^n,x)=log(b,x)/n\n";

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}
fn check(rt: &mut Runtime, code: &str, accepted: bool) -> JsonValue {
    let run = rt.run_litex_code(code).expect("public Runtime");
    assert!(run.session_error.is_none(), "{code}");
    assert_eq!(run.success, accepted, "{code}");
    crate::json_output::project_run_detailed(&run, rt, "eval", None)
}
fn find_rule<'a>(value: &'a JsonValue, name: &str) -> Option<&'a JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields
                .keys_in_order()
                .into_iter()
                .any(|k| fields.get(&k).and_then(|v| v.as_str().ok()) == Some(name))
            {
                return Some(value);
            }
            fields
                .keys_in_order()
                .into_iter()
                .find_map(|k| find_rule(fields.get(&k).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|v| find_rule(v, name)),
        _ => None,
    }
}
fn contains_string(value: &JsonValue, text: &str) -> bool {
    match value {
        JsonValue::String(s) => s == text,
        JsonValue::Object(fields) => fields
            .keys_in_order()
            .into_iter()
            .any(|k| contains_string(fields.get(&k).unwrap(), text)),
        JsonValue::Array(items) => items.iter().any(|v| contains_string(v, text)),
        _ => false,
    }
}
fn actual_text(result: &ExecStmtResult, language: OutputLanguage) -> BuiltinRuleText {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = result else {
        panic!("fact success")
    };
    let VerifyFactResult::ForallFact(f) = &s.verify_result else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = &**f
    else {
        panic!("local forall")
    };
    match &p.proved_then_facts[0].verify_result {
        VerifyFactResult::AtomicExceptEquality(a) => {
            let VerifyAtomicExceptEqualityFactResult::Success(p) = &**a else {
                panic!("atomic success")
            };
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &p.searched_proof
            else {
                panic!("actual atomic builtin")
            };
            rule.rule_name_and_message(language)
        }
        VerifyFactResult::Equality(e) => {
            let VerifyEqualityResult::Success(p) = &**e else {
                panic!("equal success")
            };
            let EqualFactSearchedProof::ByBuiltinRule(rule) = &p.searched_proof else {
                panic!("actual equal builtin")
            };
            rule.rule_name_and_message(language)
        }
        _ => panic!("atomic family"),
    }
}

#[test]
fn common_obj_relations_actual_leaves_keep_ten_language_text_and_typed_evidence() {
    for (code, name, fields, law) in [
        (
            GCD,
            "GcdCommonDivisor",
            vec![
                "divisor_positive",
                "first_divisibility",
                "second_divisibility",
            ],
            "gcd(a,b)%d=0",
        ),
        (
            LCM,
            "LcmCommonMultiple",
            vec![
                "first_positive",
                "second_positive",
                "first_divisibility",
                "second_divisibility",
            ],
            "m%lcm(a,b)=0",
        ),
        (
            SIN_POS,
            "SinPositiveOnOpenPi",
            vec!["lower_bound", "upper_bound"],
            "0<x<pi",
        ),
        (
            SIN_ORDER,
            "SinStrictMonotoneOnHalfPi",
            vec!["left_lower_bound", "right_upper_bound", "argument_order"],
            "-pi/2<=a<b<=pi/2",
        ),
        (
            LCM_NONZERO,
            "LcmNonzeroFromNonzeroOperands",
            vec!["first_nonzero", "second_nonzero"],
            "a!=0; b!=0",
        ),
        (
            LOG_NONZERO,
            "LogNonzeroFromNonunitArgument",
            vec!["base_proof", "argument_proof"],
            "b>0; b!=1; x>0; x!=1",
        ),
        (
            POW_NONUNIT,
            "PositiveNonunitIntegerPower",
            vec!["base_proof", "exponent_integer", "exponent_nonzero"],
            "n in Z; n!=0",
        ),
        (
            LOG_CHANGE,
            "LogChangeOfBase",
            vec!["base_proof", "chosen_base_proof", "argument_positive_proof"],
            "a,c>0; a!=1; c!=1",
        ),
        (
            LOG_POWER,
            "LogBasePower",
            vec![
                "base_proof",
                "exponent_real",
                "exponent_nonzero",
                "argument_positive_proof",
            ],
            "a>0; a!=1; n in R; n!=0",
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}");
        let mut names = BTreeSet::new();
        for language in OutputLanguage::ALL {
            let text = actual_text(&run.statement_results[0], language);
            assert!(text.message.contains(law), "{}", text.message);
            assert!(
                names.insert(text.rule_name),
                "language fell back to an earlier name"
            );
            let mut localized = runtime(language);
            let json = check(&mut localized, code, true);
            let rule = find_rule(&json, name)
                .expect("actual named rule")
                .as_object()
                .unwrap();
            for field in &fields {
                assert!(
                    rule.get(&localize_key(field, language)).is_some(),
                    "{name}/{field}"
                );
            }
            assert!(rule
                .get(&localize_key("proof_of_requirement_facts", language))
                .is_none());
        }
        assert_eq!(names.len(), 10);
    }
}

#[test]
fn common_obj_relations_reverse_equalities_and_signed_inputs_pass() {
    for code in [
        GCD.replace("a!=0", "b!=0")
            .replace("gcd(a,b)%d=0", "0=gcd(a,b)%d"),
        LCM.replace("m%lcm(a,b)=0", "0=m%lcm(a,b)"),
        SIN_POS.replace("0<sin(x)", "sin(x)>0"),
        SIN_ORDER.replace("sin(a)<sin(b)", "sin(b)>sin(a)"),
        LOG_NONZERO.replace("log(b,x)!=0", "0!=log(b,x)"),
        POW_NONUNIT.replace("b^n!=1", "1!=b^n"),
        LOG_CHANGE.replace("log(a,x)=log(b,x)/log(b,a)", "log(b,x)/log(b,a)=log(a,x)"),
        LOG_POWER.replace("log(b^n,x)=log(b,x)/n", "log(b,x)/n=log(b^n,x)"),
        LOG_POWER.replace("n N+", "n Z*"),
        LCM_NONZERO.replace("lcm(a,b)!=0", "0!=lcm(a,b)"),
        "forall x R+:\n    2^(1/2)!=1\n    =>:\n        log(2^(1/2),x)=log(2,x)/(1/2)\n".into(),
    ] {
        check(&mut runtime(OutputLanguage::English), &code, true);
    }
    for guard_a in ["a<1", "1<a", "a!=1"] {
        for guard_b in ["b<1", "1<b", "b!=1"] {
            let code = LOG_CHANGE.replace("a!=1", guard_a).replace("b!=1", guard_b);
            check(&mut runtime(OutputLanguage::English), &code, true);
        }
    }
    for guard in ["b<1", "1<b", "b!=1"] {
        check(
            &mut runtime(OutputLanguage::English),
            &LOG_POWER.replace("b!=1", guard),
            true,
        );
    }
}

#[test]
fn common_obj_relations_false_missing_and_illegal_controls_reject() {
    for code in [
        GCD.replace("    b%d=0\n", ""),
        GCD.replace("gcd(a,b)%d=0", "gcd(a,b)%d=1"),
        GCD.replace("d N+", "d N"),
        GCD.replace("a,b Z", "a,b R"),
        LCM.replace("    m%b=0\n", ""),
        LCM.replace("m%lcm(a,b)=0", "m%lcm(a,b)=1"),
        LCM.replace("a,b N+", "a,b N"),
        SIN_POS.replace("0<x", "0<=x"),
        SIN_POS.replace("x<pi", "x<=pi"),
        SIN_ORDER.replace("a<b", "a<=b"),
        SIN_ORDER.replace("-pi/2<=a", "-pi<=a"),
        SIN_ORDER.replace("b<=pi/2", "b<=pi"),
        LOG_NONZERO.replace("    x!=1\n", ""),
        LOG_NONZERO.replace("log(b,x)!=0", "log(b,1)!=0"),
        POW_NONUNIT.replace("n Z*", "n Z"),
        POW_NONUNIT.replace("b^n!=1", "b^0!=1"),
        POW_NONUNIT.replace("b R+", "b R*"),
        POW_NONUNIT.replace("n Z*", "n R*"),
        LOG_CHANGE.replace("    a!=1\n", ""),
        LOG_CHANGE.replace("    b!=1\n", ""),
        LOG_CHANGE.replace("a,b,x R+", "a,b,x R"),
        LOG_POWER.replace("n N+", "n N"),
        LOG_POWER.replace("b,x R+", "b,x R"),
        LCM_NONZERO.replace("a,b Z*", "a,b Z"),
        "lcm(0,2)!=0\n".into(),
        "gcd(6,10)%3=0\n".into(),
        "30%lcm(6,10)=1\n".into(),
        "0<sin(0)\n".into(),
        "0<sin(pi)\n".into(),
        "sin(pi/2)<sin(pi)\n".into(),
        "log(1,2)!=0\n".into(),
        "forall a,x R+:\n    a<1\n    =>:\n        log(a,1/x)=(-2)*log(a,x)\n".into(),
        "forall n N+:\n    factorial(n)=product(1,n,fn(k Z) Z{k+1})\n".into(),
        "factorial(0)=product(1,0,fn(k Z) Z{k})\n".into(),
    ] {
        check(&mut runtime(OutputLanguage::English), &code, false);
    }
}

#[test]
fn common_obj_relations_search_ceiling_and_failed_rollback_hold() {
    for code in [
        GCD,
        LCM,
        SIN_POS,
        SIN_ORDER,
        LCM_NONZERO,
        LOG_NONZERO,
        POW_NONUNIT,
        LOG_CHANGE,
        LOG_POWER,
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
        ] {
            assert!(rt
                .verify_fact(&goal, VerifyState::new(level))
                .unwrap()
                .is_failed());
        }
        check(&mut rt, code, true);
        check(&mut rt, code, true);
    }
    let mut rt = runtime(OutputLanguage::English);
    for (bad, good) in [
        (GCD.replace("    b%d=0\n", ""), GCD),
        (SIN_ORDER.replace("a<b", "a<=b"), SIN_ORDER),
        (LOG_NONZERO.replace("    x!=1\n", ""), LOG_NONZERO),
        (POW_NONUNIT.replace("n Z*", "n Z"), POW_NONUNIT),
        (LOG_CHANGE.replace("    a!=1\n", ""), LOG_CHANGE),
        (LOG_POWER.replace("n N+", "n N"), LOG_POWER),
    ] {
        check(&mut rt, &bad, false);
        check(&mut rt, good, true);
        check(&mut rt, good, true);
        check(&mut rt, &bad, false);
    }
}

#[test]
fn common_obj_relations_actual_assumption_citations_survive_projection() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        for (code, name, fields) in [
            ("forall a,b Z*,d N+:\n    a%d=0\n    b%d=0\n    =>:\n        gcd(a,b)%d=0\n", "GcdCommonDivisor", vec!["first_divisibility", "second_divisibility"]),
            (SIN_POS, "SinPositiveOnOpenPi", vec!["lower_bound", "upper_bound"]),
            (SIN_ORDER, "SinStrictMonotoneOnHalfPi", vec!["left_lower_bound", "right_upper_bound", "argument_order"]),
            (LCM, "LcmCommonMultiple", vec!["first_divisibility", "second_divisibility"]),
            ("forall b,x R:\n    b>0\n    b!=1\n    x>0\n    x!=1\n    =>:\n        log(b,x)!=0\n", "LogNonzeroFromNonunitArgument", vec!["base_proof", "base_proof", "argument_proof", "argument_proof"]),
        ] {
            let json = check(&mut runtime(language), code, true);
            let key = |s| localize_key(s, language);
            let statement = &json.as_object().unwrap().get(&key("statement_results")).unwrap().as_array().unwrap()[0];
            let assumptions = statement.as_object().unwrap().get(&key("verify")).unwrap().as_object().unwrap().get(&key("assumed_dom_facts")).unwrap().as_array().unwrap();
            assert_eq!(assumptions.len(), fields.len());
            let rule = find_rule(&json, name).unwrap().as_object().unwrap();
            for (field, assumption) in fields.iter().zip(assumptions) {
                let stores = assumption.as_object().unwrap().get(&key("store_and_infer")).unwrap().as_object().unwrap().get(&key("stores")).unwrap().as_array().unwrap();
                let source_id = stores[0].as_object().unwrap().get(&key("fact_id")).unwrap().as_str().unwrap();
                assert!(contains_string(rule.get(&key(field)).unwrap(), source_id), "{name}/{field} missing {source_id}");
            }
        }
    }
}

#[test]
fn common_obj_relations_durable_tracers_and_factorial_author_proof_pass() {
    for code in [
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/proof_nodes/equal/by_builtin_rule/log_reciprocal_negative_one.lit")),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/gcd_common_divisor.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/lcm_common_multiple.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/log_change_base_positive_nonunit.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/log_base_power_positive_nonunit.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/equal/by_builtin_rule/factorial_product_relation.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/sin_positive_open_pi.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/sin_strict_monotone_half_pi.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/lcm_nonzero_operands.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/log_nonzero_nonunit_argument.lit"
        )),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/proof_nodes/atomic/by_builtin_rule/positive_nonunit_integer_power.lit"
        )),
    ] {
        check(&mut runtime(OutputLanguage::English), code, true);
    }
}
