use crate::prelude::*;

const MAX_BOUND: &str = "forall a,b,x,y R, epsilon R+:\n    abs(a-x)<=epsilon\n    abs(b-y)<=epsilon\n    =>:\n        abs(max(a,b)-max(x,y))<=epsilon\n";
const MIN_BOUND: &str = "forall a,b,x,y R, epsilon R+:\n    abs(a-x)<=epsilon\n    abs(b-y)<=epsilon\n    =>:\n        abs(min(a,b)-min(x,y))<=epsilon\n";
const SYMMETRY: &str = "forall x,y R:\n    abs(x-y)=abs(y-x)\n";
const TRIANGLE: &str = "forall x,y,z R:\n    abs(x-z)<=abs(x-y)+abs(y-z)\n";
const POSITIVE_MIN: &str = "forall a,b R+:\n    min(a,b) $in R+\n";

fn runtime(language: crate::launch_command::OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language })
}

fn check(rt: &mut Runtime, source: &str, expected: bool) -> RunLitexCodeResult {
    let run = rt.run_litex_code(source).expect("public statement execution");
    assert!(run.session_error.is_none(), "{source}: {:?}", run.session_error);
    assert_eq!(run.success, expected, "{source}");
    run
}

fn named_rule(value: &crate::knowledge_base::JsonValue, name: &str) -> Option<crate::knowledge_base::JsonValue> {
    use crate::knowledge_base::JsonValue;
    match value {
        JsonValue::Object(fields) => {
            if fields.get("rule").and_then(|value| value.as_str().ok()) == Some(name) {
                return Some(value.clone());
            }
            fields.keys_in_order().into_iter().find_map(|key| named_rule(fields.get(&key).unwrap(), name))
        }
        JsonValue::Array(items) => items.iter().find_map(|value| named_rule(value, name)),
        _ => None,
    }
}

#[test]
fn exact_rules_keep_both_checked_premises() {
    for (source, name, fields) in [
        (MAX_BOUND, "MaxLipschitzFromCoordinateBounds", &["left_error_bound", "right_error_bound"][..]),
        (MIN_BOUND, "MinLipschitzFromCoordinateBounds", &["left_error_bound", "right_error_bound"][..]),
        (SYMMETRY, "AbsDifferenceSymmetry", &[][..]),
        (TRIANGLE, "AbsDifferenceTriangle", &[][..]),
        (POSITIVE_MIN, "MinPreservesPositiveCarrier", &["left_positive", "right_positive"][..]),
    ] {
        let mut rt = runtime(crate::launch_command::OutputLanguage::English);
        let run = check(&mut rt, source, true);
        let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        let rule = named_rule(&detail, name).expect(name);
        for field in fields {
            let premise = rule.as_object().unwrap().get(field).expect(field).stringify_pretty();
            assert!(premise.contains("cite_fact_id"), "{name}.{field}: {premise}");
            assert!(premise.contains("\"success\": true"), "{name}.{field}: {premise}");
        }
    }
}

#[test]
fn strict_reverse_and_finite_pair_forms_keep_the_same_rule() {
    for extremum in ["min", "max"] {
        for (first, second) in [
            ("abs(a-x)<epsilon", "abs(b-y)<epsilon"),
            ("epsilon>=abs(a-x)", "epsilon>abs(b-y)"),
        ] {
            let source = format!("forall a,b,x,y R, epsilon R+:\n    {first}\n    {second}\n    =>:\n        abs({extremum}(a,b)-{extremum}(x,y))<=epsilon\n");
            check(&mut runtime(crate::launch_command::OutputLanguage::English), &source, true);
        }
        let source = format!("forall a,b,x,y R, epsilon R+:\n    abs(a-x)<epsilon\n    abs(b-y)<epsilon\n    $is_finite_set(union({{a}},{{b}}))\n    $is_nonempty_set(union({{a}},{{b}}))\n    union({{a}},{{b}}) $subset R\n    $is_finite_set(union({{x}},{{y}}))\n    $is_nonempty_set(union({{x}},{{y}}))\n    union({{x}},{{y}}) $subset R\n    =>:\n        abs(finite_set_{extremum}(union({{a}},{{b}}))-finite_set_{extremum}(union({{x}},{{y}})))<=epsilon\n");
        let mut rt = runtime(crate::launch_command::OutputLanguage::English);
        let run = check(&mut rt, &source, true);
        let detail = crate::json_output::project_run_detailed(&run, &rt, "eval", None);
        let name = if extremum == "max" { "MaxLipschitzFromCoordinateBounds" } else { "MinLipschitzFromCoordinateBounds" };
        let rule = named_rule(&detail, name).expect("finite pair uses the same mathematical rule");
        for field in ["left_error_bound", "right_error_bound"] {
            let text = rule.as_object().unwrap().get(field).unwrap().stringify_pretty();
            assert!(text.contains(" < epsilon"), "strict source citation: {text}");
        }
    }
}

#[test]
fn triangle_orientations_and_typed_minimum_composition() {
    for source in [
        "forall x,y,z R:\n    abs(x-z)<=abs(z-y)+abs(y-x)\n",
        "forall x,y R:\n    abs(x-y)<=abs(x)+abs(y)\n",
        "forall x,y R:\n    abs(x-y)<=abs(y)+abs(x)\n",
        "have a,b,c R+\nhave first R+ = min(a,b)\nhave delta R+ = min(first,c)\n",
        "forall a,b R+:\n    $is_finite_set(union({a},{b}))\n    $is_nonempty_set(union({a},{b}))\n    union({a},{b}) $subset R\n    =>:\n        finite_set_min(union({a},{b})) $in R+\n",
    ] {
        check(&mut runtime(crate::launch_command::OutputLanguage::English), source, true);
    }
}

#[test]
fn missing_bounds_false_formulas_and_undefined_domains_reject() {
    for source in [
        "forall a,b,x,y R, epsilon R+:\n    abs(a-x)<=epsilon\n    =>:\n        abs(max(a,b)-max(x,y))<=epsilon\n",
        "forall a,b,x,y R, epsilon R+:\n    abs(a-x)<=epsilon\n    abs(b-y)<=epsilon\n    =>:\n        abs(max(a,b)-min(x,y))<=epsilon\n",
        "forall a,b,x,y R, epsilon R+:\n    abs(a-x)<=epsilon\n    abs(b-y)<=epsilon\n    =>:\n        abs(min(a,b)-min(x,y))<epsilon\n",
        "forall x,y,z,w R:\n    abs(x-z)<=abs(x-y)+abs(y-w)\n",
        "forall x,y R:\n    abs(x-y)=abs(x+y)\n",
        "have a R+\nhave b R\nhave delta R+ = min(a,b)\n",
        "have delta R+ = min(1,0)\n",
        "have delta R+ = min(1,-1)\n",
        "have x C\nabs(x-1)=abs(1-x)\n",
        "abs(1/0-1)=abs(1-1/0)\n",
        "forall a,b,x,y C, epsilon R+:\n    C_abs(a-x)<=epsilon\n    C_abs(b-y)<=epsilon\n    =>:\n        C_abs(max(a,b)-max(x,y))<=epsilon\n",
    ] {
        check(&mut runtime(crate::launch_command::OutputLanguage::English), source, false);
    }
}

#[test]
fn leaf_permissions_and_failed_publication_remain_bounded() {
    for source in [SYMMETRY, TRIANGLE, MAX_BOUND, MIN_BOUND, POSITIVE_MIN] {
        let mut rt = runtime(crate::launch_command::OutputLanguage::English);
        let tokens = crate::tokenize::Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
        let crate::ast::stmt::Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else { panic!("forall fact"); };
        for level in [VerifyStateLevel::Direct, VerifyStateLevel::KnownSpecialProperty] {
            assert!(rt.verify_fact(&fact, VerifyState::new(level)).unwrap().is_failed(), "{level:?}: {source}");
        }
        assert!(!rt.verify_fact(&fact, VerifyState::top_level()).unwrap().is_failed(), "{source}");
    }
    let mut rt = runtime(crate::launch_command::OutputLanguage::English);
    let before = rt.top_exec_env().facts.facts_by_id.len();
    check(&mut rt, "claim:\n    ? forall a,b,x,y R, epsilon R+:\n        abs(a-x)<=epsilon\n        abs(b-y)<=epsilon\n        =>:\n            abs(max(a,b)-max(x,y))<=epsilon\n    abs(max(a,b)-max(x,y))<=epsilon\n    0=1\n", false);
    assert_eq!(rt.top_exec_env().facts.facts_by_id.len(), before);
    check(&mut rt, MAX_BOUND, true);
}


#[test]
fn all_output_languages_and_unsupported_lean_routes_remain_explicit() {
    for language in crate::launch_command::OutputLanguage::ALL {
        for source in [MAX_BOUND, MIN_BOUND, SYMMETRY, TRIANGLE, POSITIVE_MIN] {
            let mut rt = runtime(language);
            let run = check(&mut rt, source, true);
            let normal = crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
            assert!(!normal.contains("unsupported"), "{language:?}: {normal}");
        }
    }
    for source in [SYMMETRY, TRIANGLE, MAX_BOUND, POSITIVE_MIN] {
        let mut rt = runtime(crate::launch_command::OutputLanguage::English);
        let run = check(&mut rt, source, true);
        assert!(crate::compile_to_lean::compile_run(&run, &rt, "metric_bound").is_err(), "No Lean theorem adapter was added");
    }
}
