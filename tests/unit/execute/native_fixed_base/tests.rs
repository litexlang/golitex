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

fn find_rule(value: &JsonValue, name: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields
                .keys_in_order()
                .into_iter()
                .any(|k| fields.get(&k).and_then(|v| v.as_str().ok()) == Some(name))
            {
                return Some(value.clone());
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

fn actual_leaf_text(result: &ExecStmtResult, language: OutputLanguage) -> BuiltinRuleText {
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
                panic!("actual builtin")
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
        _ => panic!("selected atomic family"),
    }
}

#[test]
fn legal_domains_directions_and_parent_wd() {
    for domain in ["R+", "N+", "Z+", "Q+"] {
        for target in ["ln(x)=log(e,x)", "log(e,x)=ln(x)"] {
            let code = format!("1<e\ne!=1\nforall x {domain}:\n    {target}\n");
            let json = check(&mut runtime(OutputLanguage::English), &code, true);
            let leaf = find_rule(&json, "LnAsEulerLog").unwrap();
            assert_eq!(leaf.as_object().unwrap().keys_in_order().len(), 2);
            assert!(contains_string(&json, "x $in R+"));
            assert!(contains_string(&json, "e != 1"));
        }
    }
    for domain in ["Z", "N", "N+", "Z+", "Z*"] {
        for target in ["exp(n)=e^n", "e^n=exp(n)"] {
            let code = format!("e $in R+\n0<e\ne!=0\nforall n {domain}:\n    {target}\n");
            let json = check(&mut runtime(OutputLanguage::English), &code, true);
            let leaf = find_rule(&json, "ExpAsEulerIntegerPower").unwrap();
            assert_eq!(leaf.as_object().unwrap().keys_in_order().len(), 2);
        }
    }
}

#[test]
fn wrong_base_arguments_and_illegal_domains_reject() {
    for code in [
        "forall x R+:\n    ln(x)=log(2,x)\n",
        "forall n N+:\n    exp(n)=2^n\n",
        "1<e\ne!=1\nforall x,y R+:\n    ln(x)=log(e,y)\n",
        "e $in R+\n0<e\ne!=0\nforall m,n Z:\n    exp(n)=e^m\n",
        "1<e\ne!=1\nln(0)=log(e,0)\n",
        "1<e\ne!=1\nforall x R:\n    ln(x)=log(e,x)\n",
        "e $in R+\n0<e\ne!=0\nforall x R:\n    exp(x)=e^x\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
}

#[test]
fn two_actual_typed_leaves_own_ten_guarded_language_outputs() {
    for (code, name, law) in [
        (
            "1<e\ne!=1\nforall x R+:\n    ln(x)=log(e,x)\n",
            "LnAsEulerLog",
            "x in R+, both sides well-defined => ln(x)=log(e,x)",
        ),
        (
            "e $in R+\n0<e\ne!=0\nforall n Z:\n    exp(n)=e^n\n",
            "ExpAsEulerIntegerPower",
            "n in Z, both sides well-defined => exp(n)=e^n",
        ),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.success);
        let json = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        assert!(find_rule(&json, name).is_some());
        for language in [
            OutputLanguage::English,
            OutputLanguage::Chinese,
            OutputLanguage::ChineseTraditional,
            OutputLanguage::French,
            OutputLanguage::Russian,
            OutputLanguage::Spanish,
            OutputLanguage::Arabic,
            OutputLanguage::Japanese,
            OutputLanguage::Korean,
            OutputLanguage::Vietnamese,
        ] {
            let text = actual_leaf_text(run.statement_results.last().unwrap(), language);
            assert!(!text.rule_name.is_empty());
            assert!(text.message.ends_with(law));
        }
    }
}

#[test]
fn inherited_ceiling_and_failure_publication() {
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, "1<e\ne!=1\n", true);
    let code = "forall x R+:\n    ln(x)=log(e,x)\n";
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
    assert!(!rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    let bad = "forall x,y R+:\n    ln(x)=log(e,y)\n";
    check(&mut rt, bad, false);
    let tokens = Tokenizer::new()
        .tokenize(bad, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    check(&mut rt, code, true);
    check(&mut rt, code, true);
    check(&mut rt, bad, false);
    check(&mut rt, code, true);
}
