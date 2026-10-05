use crate::json_output::{emit_run_detailed, emit_run_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

const PRODUCT: &str = include_str!(
    "../../../../examples/proof_nodes/equal/by_builtin_rule/finite_set_product_reindex.lit"
);
const REDUCE: &str = include_str!(
    "../../../../examples/proof_nodes/equal/by_builtin_rule/finite_set_reduce_reindex.lit"
);
const PRODUCT_GOAL: &str = "forall X,Y finite_set,g fn(y Y)X,f fn(x X)R:\n    $bijective(Y,X,g)\n    =>:\n        finite_set_product(X,f)=finite_set_product(Y,fn(y Y)R {f(g(y))})";
const REDUCE_GOAL: &str = "forall X,Y finite_set,g fn(y Y)X,f fn(x X)R,s R,op fn(a,b R)R:\n    forall a,b,c R:\n        op(op(a,b),c)=op(a,op(b,c))\n    forall a,b R:\n        op(a,b)=op(b,a)\n    $bijective(Y,X,g)\n    =>:\n        finite_set_reduce(X,f,op,s)=finite_set_reduce(Y,fn(y Y)R {f(g(y))},op,s)";

#[test]
fn original_tracers_retain_bijection_and_fold_matches() {
    for (code, rule) in [
        (PRODUCT, "FiniteSetProductReindex"),
        (REDUCE, "FiniteSetReduceReindex"),
    ] {
        let detailed = check(code, true);
        let proof =
            find_rule(&JsonValue::parse(&detailed).unwrap(), rule).expect("winning reindex rule");
        let JsonValue::Object(fields) = proof else {
            panic!("object expected");
        };
        let bijection = fields.get("bijection").unwrap().stringify_pretty();
        assert!(bijection.contains("$bijective(Y, X, g)"), "{bijection}");
        assert!(
            bijection.contains("cite_fact_id") || bijection.contains("fact_id"),
            "source citation: {bijection}"
        );
        if rule == "FiniteSetReduceReindex" {
            for field in ["operator_match", "seed_match"] {
                assert!(fields
                    .get(field)
                    .unwrap()
                    .stringify_pretty()
                    .contains("SameIr"));
            }
            assert!(count_cited_operation_laws(&JsonValue::parse(&detailed).unwrap()) >= 2);
        }
    }
}

#[test]
fn reverse_renamed_and_generic_carrier_goals() {
    check("forall A,B finite_set,map fn(index B)A,value fn(item A)C:\n    $bijective(B,A,map)\n    =>:\n        finite_set_product(B,fn(index B)C {value(map(index))})=finite_set_product(A,value)",true);
    check("forall X,Y finite_set,V nonempty_set,g fn(y Y)X,f fn(x X)V,s V,op fn(a,b V)V:\n    forall a,b,c V:\n        op(op(a,b),c)=op(a,op(b,c))\n    forall a,b V:\n        op(a,b)=op(b,a)\n    $bijective(Y,X,g)\n    =>:\n        finite_set_reduce(Y,fn(y Y)V {f(g(y))},op,s)=finite_set_reduce(X,f,op,s)",true);
    check(
        &REDUCE_GOAL
            .replace("s R,op", "s,t R,op")
            .replace("    $bijective", "    s=t\n    $bijective")
            .replace("{f(g(y))},op,s)", "{f(g(y))},op,t)"),
        true,
    );
}

#[test]
fn bijection_and_pullback_boundaries() {
    for code in [
        PRODUCT_GOAL.replace("    $bijective(Y,X,g)\n    =>:\n", ""),
        PRODUCT_GOAL.replace("$bijective", "$surjective"),
        PRODUCT_GOAL
            .replace("f fn(x X)R:", "f,h fn(x X)R:")
            .replace("{f(g(y))}", "{h(g(y))}"),
        PRODUCT_GOAL
            .replace("g fn(y Y)X", "g,h fn(y Y)X")
            .replace("{f(g(y))}", "{f(h(y))}"),
        PRODUCT_GOAL
            .replace("g fn(y Y)X", "c Y,g fn(y Y)X")
            .replace("{f(g(y))}", "{f(g(c))}"),
        PRODUCT_GOAL.replace("{f(g(y))}", "{f(g(y))+1}"),
        PRODUCT_GOAL.replace("fn(y Y)R", "fn(y X)R"),
        PRODUCT_GOAL.replace("X,Y finite_set", "X,Y nonempty_set"),
    ] {
        check(&code, false);
    }
}

#[test]
fn fold_laws_operator_seed_and_carrier_boundaries() {
    for code in [
        REDUCE_GOAL.replace("    forall a,b R:\n        op(a,b)=op(b,a)\n", ""),
        REDUCE_GOAL.replace(
            "    forall a,b,c R:\n        op(op(a,b),c)=op(a,op(b,c))\n",
            "",
        ),
        REDUCE_GOAL.replace("    $bijective(Y,X,g)\n", ""),
        REDUCE_GOAL.replace("{f(g(y))},op,s)", "{f(g(y))},op,s+1)"),
        REDUCE_GOAL
            .replace("op fn(a,b R)R", "op,other fn(a,b R)R")
            .replace("{f(g(y))},op,s)", "{f(g(y))},other,s)"),
        REDUCE_GOAL.replace("fn(y Y)R {f(g(y))}", "fn(y Y)C {i}"),
    ] {
        check(&code, false);
    }
    let other_laws = "    forall a,b,c R:\n        other(other(a,b),c)=other(a,other(b,c))\n    forall a,b R:\n        other(a,b)=other(b,a)\n";
    let wrong_op = REDUCE_GOAL
        .replace("op fn(a,b R)R", "op,other fn(a,b R)R")
        .replace(
            "    $bijective",
            &(other_laws.to_owned() + "    $bijective"),
        )
        .replace("{f(g(y))},op,s)", "{f(g(y))},other,s)");
    check(&wrong_op, false);
}

#[test]
fn failed_goals_do_not_publish_or_leak_bijection_assumptions() {
    let mut rt = runtime(OutputLanguage::English);
    let missing = PRODUCT_GOAL.replace("    $bijective(Y,X,g)\n    =>:\n", "");
    assert!(!rt.run_litex_code(&missing).unwrap().success);
    assert!(rt.run_litex_code(PRODUCT_GOAL).unwrap().success);
    assert!(!rt.run_litex_code(&missing).unwrap().success);
    assert!(
        !rt.run_litex_code(&PRODUCT_GOAL.replace("{f(g(y))}", "{f(g(y))+1}"))
            .unwrap()
            .success
    );
    assert!(rt.run_litex_code(PRODUCT_GOAL).unwrap().success);
}

#[test]
fn builtin_permission_and_read_only_search() {
    use crate::ast::fact::{AtomicFact, ExistOrAndChainAtomicFact, Fact};
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{
        VerifyFactWellDefinedResult, VerifyState, VerifyStateLevel,
    };
    use crate::tokenize::Tokenizer;
    for goal in [PRODUCT_GOAL, REDUCE_GOAL] {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new()
            .tokenize(goal, rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(Fact::ForallFact(conditional)) = &statements[0] else {
            panic!("forall expected")
        };
        let (_,local_env) = rt.run_in_local_env_and_take_env(|rt| {
            assert!(rt.introduce_typed_parameters(&conditional.typed_parameters,VerifyState::top_level())?.is_ok());
            for premise in &conditional.dom_facts {
                assert!(matches!(rt.verify_fact_well_definedness(premise,VerifyState::top_level())?,VerifyFactWellDefinedResult::Success(_)));
                rt.store_fact_and_infer(premise,VerifyState::top_level())?;
            }
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)) = &conditional.then_facts[0] else {panic!("equality expected")};
            assert!(!rt.verify_equal_fact_well_definedness(equal,VerifyState::top_level())?.is_failed());
            let before = rt.execution_environments_stack.iter().map(|e|(e.facts.facts_by_id.len(),e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
            assert!(rt.search_equal_fact_proof(equal,VerifyState::new(VerifyStateLevel::KnownSpecialProperty))?.is_none());
            let proof = rt.search_equal_fact_proof(equal,VerifyState::new(VerifyStateLevel::BuiltinRule))?.expect("enabled builtin");
            let crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof::ByBuiltinRule(rule) = proof else {panic!("builtin expected")};
            for language in [OutputLanguage::English,OutputLanguage::Chinese,OutputLanguage::ChineseTraditional,
                OutputLanguage::French,OutputLanguage::Russian,OutputLanguage::Spanish,OutputLanguage::Arabic,
                OutputLanguage::Japanese,OutputLanguage::Korean,OutputLanguage::Vietnamese] {
                let text = rule.rule_name_and_message(language);
                assert!(!text.rule_name.is_empty() && !text.message.is_empty());
                if language != OutputLanguage::English {
                    let english = rule.rule_name_and_message(OutputLanguage::English);
                    assert_ne!(text.rule_name,english.rule_name);
                    assert_ne!(text.message,english.message);
                }
            }
            let after = rt.execution_environments_stack.iter().map(|e|(e.facts.facts_by_id.len(),e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
            assert_eq!(before,after);
            Ok(())
        }).unwrap();
        assert!(!local_env.facts.facts_by_id.is_empty());
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn normal_and_detailed_consumers_cover_all_languages() {
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
        let mut rt = runtime(language);
        let run = rt.run_litex_code(PRODUCT_GOAL).unwrap();
        assert!(run.success);
        JsonValue::parse(&emit_run_normal(&run, &rt, "eval", None)).unwrap();
        JsonValue::parse(&emit_run_detailed(&run, &rt, "eval", None)).unwrap();
    }
}

#[test]
fn run_examples_finite_set_reindex_tracers() {
    for code in [PRODUCT, REDUCE] {
        check(code, true);
    }
}

fn check(source: &str, expected: bool) -> String {
    let mut rt = runtime(OutputLanguage::English);
    let run = rt.run_litex_code(source).unwrap();
    let detailed = emit_run_detailed(&run, &rt, "eval", None);
    assert_eq!(run.success, expected, "{source}\n{detailed}");
    detailed
}

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn find_rule(value: &JsonValue, rule: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(fields) => {
            if fields.get("rule").and_then(|v| v.as_str().ok()) == Some(rule) {
                return Some(value.clone());
            }
            for (_, child) in fields.iter() {
                if let Some(found) = find_rule(child, rule) {
                    return Some(found);
                }
            }
        }
        JsonValue::Array(values) => {
            for child in values {
                if let Some(found) = find_rule(child, rule) {
                    return Some(found);
                }
            }
        }
        _ => {}
    }
    None
}

fn count_cited_operation_laws(value: &JsonValue) -> usize {
    match value {
        JsonValue::Object(fields) => {
            let cited = fields.get("type").and_then(|v| v.as_str().ok()) == Some("forall")
                && fields
                    .get("fact")
                    .and_then(|v| v.as_str().ok())
                    .is_some_and(|f| f.contains("op("))
                && fields
                    .get("searched_proof")
                    .is_some_and(|proof| proof.stringify_pretty().contains("cite_fact_id"));
            usize::from(cited)
                + fields
                    .iter()
                    .map(|(_, child)| count_cited_operation_laws(child))
                    .sum::<usize>()
        }
        JsonValue::Array(values) => values.iter().map(count_cited_operation_laws).sum(),
        _ => 0,
    }
}
