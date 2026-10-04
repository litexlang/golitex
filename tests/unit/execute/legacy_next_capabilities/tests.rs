use crate::json_output::{emit_run_detailed, emit_run_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn check(source: &str, expected: bool) -> String {
    let source = source.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut runtime = Runtime::new(LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            });
            let result = runtime
                .run_litex_code(&source)
                .expect("run through exec_stmt");
            let json = emit_run_detailed(&result, &runtime, "eval", None);
            assert_eq!(result.success, expected, "{source}\n{json}");
            json
        })
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn finite_cartesian_cardinality() {
    let json = check("forall A,B finite_set:\n    finite_set_size(cart(A,B)) = finite_set_size(A)*finite_set_size(B)", true);
    assert!(json.contains("CartesianSize") && json.contains("factor_finiteness"));
    check("forall A,B,D finite_set:\n    finite_set_size(cart(A,B,D)) = finite_set_size(D)*(finite_set_size(B)*finite_set_size(A))", true);
    check("forall A,B finite_set:\n    finite_set_size(B)*finite_set_size(A) = finite_set_size(cart(A,B))", true);
    check("forall A,B finite_set:\n    finite_set_size(cart(A,B)) = finite_set_size(A)+finite_set_size(B)", false);
    check(
        "forall A,B set:\n    finite_set_size(cart(A,B)) = finite_set_size(A)*finite_set_size(B)",
        false,
    );
    check("forall A,B,D finite_set:\n    finite_set_size(cart(A,B,D)) = finite_set_size(A)*finite_set_size(B)", false);
}

#[test]
fn complex_modulus_product() {
    assert!(
        check("forall z,w C:\n    C_abs(z*w) = C_abs(z)*C_abs(w)", true)
            .contains("ComplexModulusProduct")
    );
    check("forall z,w C:\n    C_abs(w)*C_abs(z) = C_abs(z*w)", true);
    check("forall z,w C:\n    C_abs(z*w) = C_abs(z)+C_abs(w)", false);
    check("forall z,w C:\n    C_abs(z*w) = C_abs(z)*C_abs(z)", false);
    check("forall S,T set:\n    C_abs(S*T) = C_abs(S)*C_abs(T)", false);
}

#[test]
fn trig_difference_formulas() {
    assert!(check(
        "forall x,y R:\n    sin(x-y) = sin(x)*cos(y)-cos(x)*sin(y)",
        true
    )
    .contains("SinDifference"));
    assert!(check(
        "forall x,y R:\n    cos(x-y) = cos(x)*cos(y)+sin(x)*sin(y)",
        true
    )
    .contains("CosDifference"));
    check(
        "forall x,y R:\n    cos(y)*sin(x)-sin(y)*cos(x) = sin(x-y)",
        true,
    );
    check(
        "forall x,y R:\n    sin(y)*sin(x)+cos(y)*cos(x) = cos(x-y)",
        true,
    );
    check(
        "forall x,y R:\n    sin(x-y) = sin(x)*cos(y)+cos(x)*sin(y)",
        false,
    );
    check(
        "forall x,y R:\n    cos(x-y) = cos(x)*cos(y)-sin(x)*sin(y)",
        false,
    );
    check(
        "forall x,y C:\n    sin(x-y) = sin(x)*cos(y)-cos(x)*sin(y)",
        false,
    );
}

#[test]
fn ordered_reduce_partition() {
    let declarations = "have op fn(a,b R)R\nhave f fn(k Z)R\n";
    let json = check(
        &format!("{declarations}reduce(1,4,f,op,0) = reduce(3,4,f,op,reduce(1,2,f,op,0))"),
        true,
    );
    for key in ["ReducePartition", "bounds", "matches"] {
        assert!(json.contains(key));
    }
    check("claim:\n    ? forall a,b,c Z, s R, f fn(k Z)R, op fn(x,y R)R:\n        a <= b\n        b < c\n        =>:\n            reduce(a,c,f,op,s) = reduce(b+1,c,f,op,reduce(a,b,f,op,s))\n    b <= c\n    b+1 $in Z\n    reduce(a,b,f,op,s) $in R", true);
    check(
        &format!("{declarations}reduce(1,4,f,op,0) = reduce(5,4,f,op,reduce(1,4,f,op,0))"),
        true,
    );
    check("reduce(1,4,fn(k Z)Z {k},fn(a,b Z)Z {a-b},0) = reduce(3,4,fn(k Z)Z {k},fn(a,b Z)Z {a-b},reduce(1,2,fn(k Z)Z {k},fn(a,b Z)Z {a-b},0))", true);
    for goal in [
        "reduce(1,4,f,op,0) = reduce(2,4,f,op,reduce(1,2,f,op,0))",
        "reduce(1,4,f,op,0) = reduce(4,4,f,op,reduce(1,2,f,op,0))",
        "reduce(1,4,f,op,0) = reduce(3,4,f,op,reduce(1,2,f,op,1))",
        "reduce(1,4,f,op,0) = reduce(3,5,f,op,reduce(1,2,f,op,0))",
        "reduce(1,4,f,op,0) = reduce(0,4,f,op,reduce(1,-1,f,op,0))",
    ] {
        check(&format!("{declarations}{goal}"), false);
    }
    check("have op fn(a,b R)R\nhave other fn(a,b R)R\nhave f fn(k Z)R\nreduce(1,4,f,op,0) = reduce(3,4,f,other,reduce(1,2,f,op,0))", false);
    check("have op fn(a,b R)R\nhave f fn(k Z)R\nhave g fn(k Z)R\nreduce(1,4,f,op,0) = reduce(3,4,g,op,reduce(1,2,f,op,0))", false);
}

#[test]
fn finite_product_fresh_insertion() {
    let json = check("claim:\n    ? forall S finite_set,a R,f fn(x union(S,{a}))R:\n        not a $in S\n        =>:\n            finite_set_product(union(S,{a}),f) = finite_set_product(S,fn(x S)R {f(x)})*f(a)\n    a $in union(S,{a})\n    forall x S:\n        x $in union(S,{a})\n    release thm fn_set_member(f,fn(x S)R)", true);
    for key in [
        "FiniteSetProductFreshInsertion",
        "premises",
        "pointwise",
        "function_expansions",
        "factor_equal",
        "cite",
    ] {
        assert!(json.contains(key), "missing {key}");
    }
    check("claim:\n    ? forall S finite_set,a R,f fn(x union({a},S))R:\n        not a $in S\n        =>:\n            f(a)*finite_set_product(S,fn(y S)R {f(y)}) = finite_set_product(union({a},S),f)\n    a $in union({a},S)\n    forall x S:\n        x $in union({a},S)\n    release thm fn_set_member(f,fn(x S)R)", true);
    check("forall S finite_set,a R,f fn(x union(S,{a}))R:\n    finite_set_product(union(S,{a}),f) = finite_set_product(S,fn(x S)R {f(x)})*f(a)", false);
    check("forall S finite_set,a R,f fn(x union(S,{a}))R:\n    not a $in S\n    =>:\n        finite_set_product(union(S,{a}),f) = finite_set_product(S,fn(x S)R {f(x)+1})*f(a)", false);
    check("forall S finite_set,a R,f fn(x union(S,{a}))R:\n    not a $in S\n    =>:\n        finite_set_product(union(S,{a}),f) = finite_set_product(S,fn(x S)R {f(x)})*(f(a)+1)", false);
    check("forall S set,a R,f fn(x union(S,{a}))R:\n    not a $in S\n    =>:\n        finite_set_product(union(S,{a}),f) = finite_set_product(S,fn(x S)R {f(x)})*f(a)", false);
}

#[test]
fn normal_bilingual_contract() {
    for (source, en, zh) in [
        ("have A,B finite_set\nfinite_set_size(cart(A,B)) = finite_set_size(A)*finite_set_size(B)", "Finite Cartesian cardinality", "有限笛卡尔积的基数"),
        ("have z,w C\nC_abs(z*w) = C_abs(z)*C_abs(w)", "Multiplicativity of complex modulus", "复数模的乘法公式"),
        ("have x,y R\nsin(x-y) = sin(x)*cos(y)-cos(x)*sin(y)", "Sine difference formula", "正弦差角公式"),
        ("have x,y R\ncos(x-y) = cos(x)*cos(y)+sin(x)*sin(y)", "Cosine difference formula", "余弦差角公式"),
        ("have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(1,4,f,op,0) = reduce(3,4,f,op,reduce(1,2,f,op,0))", "Adjacent left-fold partition", "左折叠的相邻分段"),
        ("have f fn(x union({1,2},{3}))R\nnot 3 $in {1,2}\n3 $in union({1,2},{3})\nforall x {1,2}:\n    x $in union({1,2},{3})\nrelease thm fn_set_member(f,fn(x {1,2})R)\nfinite_set_product(union({1,2},{3}),f) = finite_set_product({1,2},fn(x {1,2})R {f(x)})*f(3)", "Fresh insertion into a finite product", "有限乘积插入新元素"),
    ] {
      for (language, expected_text) in [(OutputLanguage::English, en), (OutputLanguage::Chinese, zh)] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        });
        let result = rt.run_litex_code(source).unwrap();
        assert!(result.success);
        assert!(emit_run_normal(&result, &rt, "eval", None).contains(expected_text));
      }
    }
}

#[test]
fn builtin_permission_and_depth_are_inherited() {
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::VerifyState;
    use crate::tokenize::Tokenizer;
    for (setup, goal) in [
        ("have A,B finite_set\nfinite_set_size(cart(A,B)) = finite_set_size(cart(A,B))\nfinite_set_size(A)*finite_set_size(B) = finite_set_size(A)*finite_set_size(B)", "finite_set_size(cart(A,B)) = finite_set_size(A)*finite_set_size(B)"),
        ("have z,w C\nC_abs(z*w) = C_abs(z*w)\nC_abs(z)*C_abs(w) = C_abs(z)*C_abs(w)", "C_abs(z*w) = C_abs(z)*C_abs(w)"),
        ("have x,y R\nsin(x-y) = sin(x-y)\nsin(x)*cos(y)-cos(x)*sin(y) = sin(x)*cos(y)-cos(x)*sin(y)", "sin(x-y) = sin(x)*cos(y)-cos(x)*sin(y)"),
        ("have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(1,4,f,op,0) = reduce(1,4,f,op,0)\nreduce(3,4,f,op,reduce(1,2,f,op,0)) = reduce(3,4,f,op,reduce(1,2,f,op,0))", "reduce(1,4,f,op,0) = reduce(3,4,f,op,reduce(1,2,f,op,0))"),
        ("have f fn(x union({1,2},{3}))R\nnot 3 $in {1,2}\n3 $in union({1,2},{3})\nforall x {1,2}:\n    x $in union({1,2},{3})\nrelease thm fn_set_member(f,fn(x {1,2})R)\nfinite_set_product(union({1,2},{3}),f) = finite_set_product(union({1,2},{3}),f)\nfinite_set_product({1,2},fn(x {1,2})R {f(x)})*f(3) = finite_set_product({1,2},fn(x {1,2})R {f(x)})*f(3)", "finite_set_product(union({1,2},{3}),f) = finite_set_product({1,2},fn(x {1,2})R {f(x)})*f(3)"),
    ] {
        let mut rt = Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language: OutputLanguage::English });
        assert!(rt.run_litex_code(setup).unwrap().success, "{setup}");
        let tokens = Tokenizer::new().tokenize(goal, rt.current_file.clone()).unwrap();
        let statements = rt.parse(&tokens).unwrap();
        let Stmt::Fact(fact) = &statements[0] else { panic!("fact expected"); };
        let before = rt.execution_environments_stack.iter().map(|e| (e.facts.facts_by_id.len(), e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
        let mut state = VerifyState::top_level();
        state = VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty);
        assert!(rt.verify_fact(fact, state.clone()).unwrap().is_failed(), "disabled entry: {goal}");
        state = VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule);
        assert!(!rt.verify_fact(fact, state).unwrap().is_failed(), "zero deep depth: {goal}");
        let after = rt.execution_environments_stack.iter().map(|e| (e.facts.facts_by_id.len(), e.well_defined_objects.object_to_wd_id.len())).collect::<Vec<_>>();
        assert_eq!(before, after, "search must not publish evidence: {goal}");
    }
}
