use crate::prelude::*;

fn run(source: &str) -> RunLitexCodeResult {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: source.into(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    runtime.run_litex_code(source).unwrap()
}

#[test]
fn fold_rejects_unsound_operation_seed_and_iterand_paths() {
    for source in [
        r#"have fn op(x, y C) R = re(y)
have fn f(x Z) R = x
by extension:
    ? {0, 1} = {1, 0}
    claim:
        ? forall t {0, 1} => t $in {1, 0}
        t = 0 or t = 1
        by cases:
            ? t $in {1, 0}
            case t = 0:
                t $in {1, 0}
            case t = 1:
                t $in {1, 0}
    claim:
        ? forall t {1, 0} => t $in {0, 1}
        t = 1 or t = 0
        by cases:
            ? t $in {0, 1}
            case t = 1:
                t $in {0, 1}
            case t = 0:
                t $in {0, 1}
    {0, 1} $subset {1, 0}
    {1, 0} $subset {0, 1}

eval finite_set_reduce({0, 1}, f, op, 0)
eval finite_set_reduce({1, 0}, f, op, 0)
finite_set_reduce({0, 1}, f, op, 0) = finite_set_reduce({1, 0}, f, op, 0)
1 = 0
"#,
        r#"have fn op(x, y C) N+ = 1
reduce(1, 0, 0, op, 0) = 0
reduce(1, 0, 0, op, 0) $in N+
0 $in N+
1 <= 0
0 <= 1
1 = 0
"#,
        r#"have fn op(x, y N+) N+ = x + y
have fn f(x N+) R = -10
reduce(1, 0, f, op, 0) = 0
reduce(1, 0, f, op, 0) $in N+
0 $in N+
1 <= 0
0 <= 1
1 = 0
"#,
        r#"have fn f(x Z) Z = 1
f(1) = 1
reduce(1, 1, f, fn(a, b Z) Z {0 + 0}, 0) = 0
reduce(1, 1, f, fn(a, b Z) Z {0 + 0}, 0) = 1
1 = 0
"#,
    ] {
        let result = run(source);
        assert!(result.session_error.is_none(), "{source}");
        assert!(!result.success, "{source}");
        assert!(
            result.statement_results.last().unwrap().is_failed(),
            "{source}"
        );
    }
}

#[test]
fn fold_checks_seed_and_closure_even_for_empty_inputs() {
    for source in [
        "reduce(1,0,fn(k Z) Z {k},fn(a,b N+) N+ {a+b},0) = 0",
        "reduce(1,0,0,fn(a,b Z) Z {a+b},0) = 0",
        "reduce(1,0,fn(k Z) R {k/2},fn(a,b Z) Z {a+b},0) = 0",
        "finite_set_reduce({},fn(k Z) Z {k},fn(a,b Z: a=a) Z {a-b},0) = 0",
    ] {
        assert!(!run(source).success, "{source}");
    }
}

#[test]
fn fold_preserves_checked_homogeneous_examples() {
    for source in [
        "reduce(2,1,fn(k Z) Z {k},fn(a,b Z) Z {a+b},7) = 7",
        "reduce(1,2,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 3",
        "finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {a+b},0) = finite_set_sum({1,2},fn(k R) R {k}) = 3",
        "reduce(1,2,fn(k Z) Z {k},fn(a,b Z) Z {a-b},0) = -3",
    ] {
        let result = run(source);
        assert!(result.success, "{source}\n{:?}", result.session_error);
    }
}

#[test]
fn aggregate_expansion_retains_composite_terms() {
    for source in [
        "forall x,y R,f fn(t R) R:\n    x != y\n    f(x)=x+1\n    f(y)=y+1\n    =>:\n        finite_set_sum({x,y},f) = (x+1)+(y+1)",
        "forall x,y R,f fn(t R) R:\n    x != y\n    f(x)=x*2\n    f(y)=y*2\n    =>:\n        finite_set_product({x,y},f) = (x*2)*(y*2)",
    ] {
        let result = run(source);
        assert!(result.success, "{source}\n{:?}", result.session_error);
    }
}
