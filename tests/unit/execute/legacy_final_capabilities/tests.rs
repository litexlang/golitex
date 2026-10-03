use crate::json_output::{emit_run_detailed, emit_run_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn check(source: &str, expected: bool) -> String {
    let source = source.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut rt = Runtime::new(LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            });
            let result = rt.run_litex_code(&source).unwrap();
            let json = emit_run_detailed(&result, &rt, "eval", None);
            assert_eq!(result.success, expected, "{source}\n{json}");
            json
        })
        .unwrap()
        .join()
        .unwrap()
}

fn find_rule(value: &JsonValue, rule: &str) -> Option<JsonValue> {
    match value {
        JsonValue::Object(map) => {
            if map.get("rule").and_then(|v| v.as_str().ok()) == Some(rule) {
                return Some(value.clone());
            }
            for (_, child) in map.iter() {
                if let Some(v) = find_rule(child, rule) {
                    return Some(v);
                }
            }
        }
        JsonValue::Array(array) => {
            for child in array {
                if let Some(v) = find_rule(child, rule) {
                    return Some(v);
                }
            }
        }
        _ => {}
    }
    None
}
fn evidence(json: &str, rule: &str) -> JsonValue {
    find_rule(&JsonValue::parse(json).unwrap(), rule)
        .unwrap_or_else(|| panic!("missing {rule}: {json}"))
}

const DECL: &str = "have op fn(a,b R)R\nhave f fn(k Z)R\n";
const POINTWISE: &str = "forall f,g fn(k Z)R,op fn(a,b R)R:\n    forall k Z:\n        f(k)=g(k)\n    =>:\n        reduce(1,3,f,op,0)=reduce(1,3,g,op,0)";
const REMOVE: &str = "forall S finite_set,a S,f fn(x S)R:\n    finite_set_product(S,f) = finite_set_product(set_minus(S,{a}),fn(x set_minus(S,{a}))R {f(x)})*f(a)";

#[test]
fn quarter_turn_formulas() {
    for (code, rule) in [
        ("forall x R:\n    sin(x+pi/2)=cos(x)", "SinHalfPiShift"),
        ("forall x R:\n    cos(x+pi/2)=-sin(x)", "CosHalfPiShift"),
    ] {
        evidence(&check(code, true), rule);
    }
    check(
        "forall x R:\n    cos(x)=sin(0.5*pi+x)\n    -sin(x)=cos(pi*(1/2)+x)",
        true,
    );
    for code in [
        "forall x R:\n    cos(x+pi/2)=sin(x)",
        "forall x R:\n    sin(x+pi/2)=-cos(x)",
        "forall x C:\n    sin(x+pi/2)=cos(x)",
        "forall x R:\n    sin(x+pi/3)=cos(x)",
    ] {
        check(code, false);
    }
}

#[test]
fn first_step_preserves_seed_order_and_nonemptiness() {
    let json = check(
        &format!("{DECL}reduce(1,3,f,op,0)=reduce(2,3,f,op,op(0,f(1)))"),
        true,
    );
    let node = evidence(&json, "ReduceFirstStep");
    assert_eq!(
        node.as_object()
            .unwrap()
            .get("matches")
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        5
    );
    check("forall a,b Z,f fn(k Z)R,op fn(x,y R)R,s R:\n    a<=b\n    =>:\n        reduce(a,b,f,op,s)=reduce(a+1,b,f,op,op(s,f(a)))", true);
    check(
        &format!("{DECL}reduce(2,2,f,op,4)=reduce(3,2,f,op,op(4,f(2)))"),
        true,
    );
    check("forall T set,s T,f fn(k Z)T,op fn(x,y T)T:\n    reduce(1,3,f,op,s)=reduce(2,3,f,op,op(s,f(1)))", true);
    for goal in [
        "reduce(1,3,f,op,0)=reduce(2,3,f,op,op(f(1),0))",
        "reduce(3,1,f,op,0)=reduce(4,1,f,op,op(0,f(3)))",
        "reduce(1,3,f,op,0)=reduce(3,3,f,op,op(0,f(1)))",
        "reduce(1,3,f,op,0)=reduce(2,4,f,op,op(0,f(1)))",
        "reduce(1,3,f,op,0)=reduce(2,3,f,op,op(1,f(1)))",
    ] {
        check(&format!("{DECL}{goal}"), false);
    }
    check("forall a,b Z,f fn(k Z)R,op fn(x,y R)R,s R:\n    reduce(a,b,f,op,s)=reduce(a+1,b,f,op,op(s,f(a)))", false);
}

#[test]
fn translation_preserves_interval_and_callback() {
    let json = check(
        &format!("{DECL}reduce(3,5,f,op,0)=reduce(0,2,fn(k Z)R {{f(3+k)}},op,0)"),
        true,
    );
    let node = evidence(&json, "ReduceTranslation");
    let map = node.as_object().unwrap();
    for key in [
        "shift",
        "matches",
        "parameter",
        "assumptions",
        "function_expansions",
        "pointwise",
    ] {
        assert!(map.get(key).is_some());
    }
    assert_eq!(map.get("assumptions").unwrap().as_array().unwrap().len(), 2);
    assert!(!map
        .get("function_expansions")
        .unwrap()
        .as_array()
        .unwrap()
        .is_empty());
    check("forall a,b,d Z,s R,f fn(k Z)R,op fn(x,y R)R:\n    reduce(a+d,b+d,f,op,s)=reduce(a,b,fn(j Z)R {f(j+d)},op,s)", true);
    check(
        &format!("{DECL}reduce(0,2,fn(j Z)R {{f(j+3)}},op,0)=reduce(3,5,f,op,0)"),
        true,
    );
    check(
        &format!("{DECL}reduce(-3,-1,f,op,0)=reduce(0,2,fn(j Z)R {{f(j-3)}},op,0)"),
        true,
    );
    check(
        &format!("{DECL}reduce(1,3,f,op,0)=reduce(1,3,fn(j Z)R {{f(j)}},op,0)"),
        true,
    );
    for goal in [
        "reduce(3,5,f,op,0)=reduce(0,2,fn(k Z)R {f(2+k)},op,0)",
        "reduce(3,5,f,op,0)=reduce(0,3,fn(k Z)R {f(3+k)},op,0)",
        "reduce(3,5,f,op,0)=reduce(0,2,fn(k Z)R {f(3+k)},op,1)",
        "reduce(3,5,f,op,0)=reduce(0,2,fn(k Z)R {f(3-k)},op,0)",
    ] {
        check(&format!("{DECL}{goal}"), false);
    }
}

#[test]
fn pointwise_certificate_keeps_scope_and_source() {
    let node = evidence(&check(POINTWISE, true), "ReducePointwise");
    let certificate = node
        .as_object()
        .unwrap()
        .get("certificate")
        .unwrap()
        .stringify_pretty();
    assert!(certificate.contains("cite_fact_id") && certificate.contains("parameter_renamings"));
    check("forall f,g fn(k Z)R,op fn(a,b R)R:\n    forall t Z:\n        g(t)=f(t)\n    =>:\n        reduce(1,3,f,op,0)=reduce(1,3,g,op,0)", true);
    check("forall f,g fn(k Z)R,op fn(a,b R)R:\n    forall t Z:\n        1<=t\n        t<=3\n        =>:\n            f(t)=g(t)\n    =>:\n        reduce(1,3,f,op,0)=reduce(1,3,g,op,0)", true);
    for code in [
        "forall f,g fn(k Z)R,op fn(a,b R)R:\n    reduce(1,3,f,op,0)=reduce(1,3,g,op,0)",
        "forall f,g fn(k Z)R,op fn(a,b R)R:\n    forall t Z:\n        f(t)=g(t)\n    =>:\n        reduce(1,3,f,op,0)=reduce(1,3,g,op,1)",
        "forall f,g fn(k Z)R,op fn(a,b R)R:\n    forall t Z:\n        f(t)=g(t)\n    =>:\n        reduce(1,3,f,op,0)=reduce(1,4,g,op,0)",
        "forall f,g fn(k Z)R,op fn(a,b R)R:\n    forall t Z:\n        1<=t\n        t<=2\n        =>:\n            f(t)=g(t)\n    =>:\n        reduce(1,3,f,op,0)=reduce(1,3,g,op,0)",
    ] { check(code, false); }
}

#[test]
fn member_removal_keeps_membership_restriction_and_zero() {
    let node = evidence(&check(REMOVE, true), "FiniteSetProductMemberRemoval");
    let map = node.as_object().unwrap();
    assert_eq!(map.get("premises").unwrap().as_array().unwrap().len(), 2);
    assert!(map
        .get("pointwise")
        .unwrap()
        .as_object()
        .unwrap()
        .get("function_expansions")
        .is_some());
    assert!(map.get("factor_equal").is_some());
    check("forall S finite_set,a S,f fn(x S)R:\n    f(a)*finite_set_product(set_minus(S,{a}),fn(y set_minus(S,{a}))R {f(y)})=finite_set_product(S,f)", true);
    check("forall S finite_set,a S,f fn(x S)R:\n    f(a)=0\n    =>:\n        finite_set_product(S,f)=finite_set_product(set_minus(S,{a}),fn(x set_minus(S,{a}))R {f(x)})*0", true);
    for code in [
        "forall S finite_set,a R,f fn(x union(S,{a}))R:\n    finite_set_product(S,fn(x S)R {f(x)})=finite_set_product(set_minus(S,{a}),fn(x set_minus(S,{a}))R {f(x)})*f(a)",
        "forall S finite_set,a S,f fn(x S)R:\n    finite_set_product(S,f)=finite_set_product(set_minus(S,{a}),fn(x set_minus(S,{a}))R {f(x)+1})*f(a)",
        "forall S finite_set,a S,f fn(x S)R:\n    finite_set_product(S,f)=finite_set_product(set_minus(S,{a}),fn(x set_minus(S,{a}))R {f(x)})*(f(a)+1)",
        "forall S set,a S,f fn(x S)R:\n    finite_set_product(S,f)=finite_set_product(set_minus(S,{a}),fn(x set_minus(S,{a}))R {f(x)})*f(a)",
    ] { check(code, false); }
}

#[test]
fn new_rule_explanations_are_bilingual() {
    for (source, en, zh) in [
        ("have x R\nsin(x+pi/2)=cos(x)", "Sine quarter-turn shift", "正弦的半 pi 平移"),
        ("have x R\ncos(x+pi/2)=-sin(x)", "Cosine quarter-turn shift", "余弦的半 pi 平移"),
        ("have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(1,3,f,op,0)=reduce(2,3,f,op,op(0,f(1)))", "First left-fold step", "左折叠的首项递推"),
        ("have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(3,5,f,op,0)=reduce(0,2,fn(k Z)R {f(3+k)},op,0)", "Order-preserving fold translation", "有序折叠的索引平移"),
        ("have S finite_set = {1,2}\nhave a S = 1\nhave f fn(x S)R\nfinite_set_product(S,f)=finite_set_product(set_minus(S,{a}),fn(x set_minus(S,{a}))R {f(x)})*f(a)", "Remove a member from a finite product", "有限乘积删除已有元素"),
    ] {
        for (language, text) in [(OutputLanguage::English, en), (OutputLanguage::Chinese, zh)] {
            let mut rt = Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language });
            let run = rt.run_litex_code(source).unwrap();
            assert!(run.success, "{source}\n{}", emit_run_detailed(&run, &rt, "eval", None));
            assert!(emit_run_normal(&run, &rt, "eval", None).contains(text), "{text}");
        }
    }
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_pointwise::ReducePointwiseProof;
    // Exercise the dispatcher text for the forall-consuming rule, whose Normal
    // outer quantified proof does not display its nested leaf explanation.
    for (lang, text) in [
        (OutputLanguage::English, "Pointwise fold congruence"),
        (OutputLanguage::Chinese, "有序折叠的逐点相等"),
    ] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: lang,
        });
        assert!(rt.run_litex_code("forall x R:\n    x=x").unwrap().success);
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize("forall x R:\n    x=x", rt.current_file.clone())
            .unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let crate::ast::stmt::Stmt::Fact(crate::ast::fact::Fact::ForallFact(goal)) = &statements[0]
        else {
            panic!("forall expected");
        };
        let (cite_fact_id, parameter_renamings) = rt.match_known_forall_source(goal).unwrap();
        let certificate = crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_reduce_pointwise::ReducePointwiseCertificate {
            fact: goal.clone(), cite_fact_id, parameter_renamings,
        };
        let leaf = EqualitySearchProofByBuiltinRule::ReducePointwise(ReducePointwiseProof {
            matches: vec![],
            certificate,
        });
        assert_eq!(leaf.rule_id_and_message(lang).rule_name, text);
    }
}

#[test]
fn stage_permissions_and_scoped_search_remain_bounded() {
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
    use crate::tokenize::Tokenizer;
    for (setup, goal) in [
        ("have x R\nsin(x+pi/2)=sin(x+pi/2)\ncos(x)=cos(x)", "sin(x+pi/2)=cos(x)"),
        ("have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(1,3,f,op,0)=reduce(1,3,f,op,0)\nreduce(2,3,f,op,op(0,f(1)))=reduce(2,3,f,op,op(0,f(1)))", "reduce(1,3,f,op,0)=reduce(2,3,f,op,op(0,f(1)))"),
        ("have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(3,5,f,op,0)=reduce(3,5,f,op,0)\nreduce(0,2,fn(k Z)R {f(3+k)},op,0)=reduce(0,2,fn(k Z)R {f(3+k)},op,0)", "reduce(3,5,f,op,0)=reduce(0,2,fn(k Z)R {f(3+k)},op,0)"),
        ("", REMOVE),
        ("", POINTWISE),
    ] {
        let mut rt = Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language: OutputLanguage::English });
        let run = rt.run_litex_code(setup).unwrap();
        assert!(run.success, "{setup}\n{}", emit_run_detailed(&run, &rt, "eval", None));
        let tokens = Tokenizer::new().tokenize(goal, rt.current_file.clone()).unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(fact) = &statements[0] else { panic!("fact expected"); };
        let before = rt.execution_environments_stack.iter().map(|e| (e.facts.facts_by_id.len(), e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
        assert!(rt.verify_fact(fact, VerifyState::new(VerifyStateLevel::KnownSpecialProperty)).unwrap().is_failed(), "disabled builtin: {goal}");
        assert!(!rt.verify_fact(fact, VerifyState::new(VerifyStateLevel::BuiltinRule)).unwrap().is_failed(), "builtin only: {goal}");
        let after = rt.execution_environments_stack.iter().map(|e| (e.facts.facts_by_id.len(), e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
        assert_eq!(before, after, "scoped search must not publish: {goal}");
    }
}
