use crate::json_output::emit_run_detailed;
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
            let result = runtime.run_litex_code(&source).expect("run code");
            let json = emit_run_detailed(&result, &runtime, "eval", None);
            assert_eq!(result.success, expected, "{}\n{}", source, json);
            json
        })
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn legacy_small_elementary_arithmetic() {
    for (code, rule) in [
        (
            "forall a Z, m N+:\n    (-a) % m = (m - a % m) % m",
            "ModNegation",
        ),
        (
            "forall a Z, m N+, n N:\n    (a^n) % m = ((a % m)^n) % m",
            "ModNaturalPower",
        ),
        ("forall x R:\n    abs(x)^4 = x^4", "AbsEvenPower"),
        (
            "forall x R, n N+:\n    x^n = 0\n    =>:\n        x = 0",
            "PositivePowerZero",
        ),
        (
            "forall a, b R+:\n    a^3 = b^3\n    =>:\n        a = b",
            "PositivePowerCancellation",
        ),
        (
            "forall x, y R:\n    x >= 0\n    y >= 0\n    x = y^2\n    =>:\n        sqrt(x) = y",
            "SqrtKnownSquare",
        ),
    ] {
        assert!(check(code, true).contains(rule), "missing {rule} evidence");
    }
    for code in [
        "forall a Z:\n    (-a) % 0 = 0",
        "forall x R:\n    abs(x)^3 = x^3",
        "forall a, b R:\n    a^2 = b^2\n    =>:\n        a = b",
        "forall x, y R:\n    x >= 0\n    x = y^2\n    =>:\n        sqrt(x) = y",
    ] {
        check(code, false);
    }
}

#[test]
fn legacy_small_trig_complex() {
    for code in [
        "forall x R:\n    sin(-x) = -sin(x)\n    cos(-x) = cos(x)\n    sin(x + pi) = -sin(x)\n    cos(x + pi) = -cos(x)\n    sin(2*x) = 2*sin(x)*cos(x)",
        "forall z C:\n    z = re(z) + img(z)*i",
        "forall z C:\n    C_abs(z) = 0\n    =>:\n        z = 0",
        "forall z, w C:\n    re(z) = re(w)\n    img(z) = img(w)\n    =>:\n        z = w",
        "forall z, w C:\n    re(z+w) = re(z)+re(w)\n    img(z+w) = img(z)+img(w)\n    re(z-w) = re(z)-re(w)\n    img(z-w) = img(z)-img(w)",
    ] {check(code,true);}
    let evidence = check(
        "forall z, w C:\n    re(z) = re(w)\n    img(z) = img(w)\n    =>:\n        z = w",
        true,
    );
    for key in [
        "ComplexCoordinatesEqual",
        "\"real\"",
        "\"imaginary\"",
        "\"domains\"",
    ] {
        assert!(evidence.contains(key), "missing {key}");
    }
    for code in [
        "forall x R:\n    sin(-x) = sin(x)",
        "forall z C:\n    z = re(z)",
        "forall z C:\n    C_abs(z) = 1\n    =>:\n        z = 0",
        "forall z, w C:\n    re(z) = re(w)\n    =>:\n        z = w",
        "forall z, w C:\n    re(z+w) = re(z)+img(w)",
    ] {
        check(code, false);
    }
}

#[test]
fn legacy_small_quantified_contradiction() {
    check(
        "by contra:\n    ? not forall x R:\n        x^2 >= x\n    impossible 0.5^2 >= 0.5",
        true,
    );
    check("by contra:\n    ? exist x R st {x = 0}\n    witness exist x R st {x = 0} from 0\n    impossible 0 = 0",true);
    check(
        "by contra:\n    ? exist x R st {x != x}\n    impossible 0 = 0",
        false,
    );
    check(
        "by contra:\n    ? not forall x R:\n        x = x\n    impossible 0 = 0",
        false,
    );
}

#[test]
fn legacy_small_ordered_reduce() {
    let evidence = check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 6", true);
    for key in [
        "AggregateCalculation",
        "\"reduce\"",
        "\"term\"",
        "\"operation\"",
        "\"accumulated_value\"",
    ] {
        assert!(evidence.contains(key), "missing {key}");
    }
    check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a-b},0) = -6", true);
    check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a-b},0) = 2", false);
    check("reduce(1,3,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 7", false);
    check(
        "reduce(1,3,fn(k Z) R {k},fn(a,b R) R {a*b},1) = product(1,3,fn(k Z) R {k})",
        true,
    );
    check(
        "reduce(1,3,fn(k Z) R {k},fn(a,b R) R {a*b},2) = product(1,3,fn(k Z) R {k})",
        false,
    );
    check("reduce(3,1,fn(k Z) Z {k},fn(a,b Z) Z {a+b},5) = 5", true);
    check(
        "reduce(1,1025,fn(k Z) Z {k},fn(a,b Z) Z {a+b},0) = 525825",
        false,
    );
}

#[test]
fn legacy_small_finite_map_size() {
    let proof=check("forall A, B finite_set, f fn(x A)B:\n    $bijective(A,B,f)\n    =>:\n        finite_set_size(A) = finite_set_size(B)",true);
    assert!(proof.contains("FiniteBijectiveSize") && proof.contains("certificate"));
    check("forall A finite_set, B set, f fn(x A)B:\n    $injective(A,B,f)\n    =>:\n        finite_set_size(fn_range(f)) = finite_set_size(A)",true);
    check(
        "forall A, B finite_set, f fn(x A)B:\n    finite_set_size(A) = finite_set_size(B)",
        false,
    );
    check("forall A finite_set, B set, f fn(x A)B:\n    finite_set_size(fn_range(f)) = finite_set_size(A)",false);
    check("forall z C, n N:\n    re(z^(n+1)) = re(z^n)*re(z)-img(z^n)*img(z)\n    img(z^(n+1)) = re(z^n)*img(z)+img(z^n)*re(z)",true);
    check(
        "forall z C, n N:\n    re(z^(n+1)) = re(z^n)*re(z)+img(z^n)*img(z)",
        false,
    );
}

#[test]
fn legacy_small_unordered_fold_laws() {
    check(
        "finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {a+b},0) $in R",
        true,
    );
    check(
        "finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {a-b},0) $in R",
        false,
    );
    // Commutativity alone is insufficient: this symmetric operation is not
    // associative, and enumeration order would change the resulting value.
    check(
        "finite_set_reduce({1,2},fn(k R) R {k},fn(a,b R) R {(a+b)/2},0) $in R",
        false,
    );
    check("forall a Z,n N:\n    a^n $in Z", true);
    check("2^(-1) $in Z", false);
    check("forall a Z,m N+:\n    (a%m) $in Z", true);
    check(
        "forall A finite_set,B set,f fn(x A)B:\n    $is_finite_set(fn_range(f))",
        true,
    );
    check("forall f fn(x R)R:\n    $is_finite_set(fn_range(f))", false);
    let evidence = check(
        "finite_set_reduce({3,1,2},fn(k R) R {k},fn(a,b R) R {a+b},0) = 6",
        true,
    );
    assert!(evidence.contains("finite_set_reduce") && evidence.contains("operation"));
    check(
        "finite_set_reduce({1,1},fn(k R) R {k},fn(a,b R) R {a+b},0) = 1",
        false,
    );
    check(
        "finite_set_reduce({1,2,3},fn(k R) R {k},fn(a,b R) R {a+b},0) = 7",
        false,
    );
}

#[test]
fn legacy_small_fold_carrier_composition() {
    let source =
        "have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(1,3,f,op,0) = op(reduce(1,2,f,op,0),f(3))";
    let evidence = check(source, true);
    assert!(evidence.contains("ReduceLastStep") && evidence.contains("FoldInCarrier"));
    check(
        "have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(1,3,f,op,0) = op(reduce(1,2,f,op,0),f(2))",
        false,
    );
    check(
        "have op fn(a,b R)R\nhave f fn(k Z)R\nreduce(3,1,f,op,0) = op(reduce(3,0,f,op,0),f(1))",
        false,
    );
    let proof = check(
        "forall x,y R:\n    fn(a,b R) R {a+b}(fn(a,b R) R {a+b}(x,y),x) $in R",
        true,
    );
    assert!(proof.contains("AnonymousFnApplicationInCodomain"));
    check("forall x C,y R:\n    fn(a,b R) R {a+b}(x,y) $in R", false);
    check("forall x,y R:\n    fn(a,b R) Z {a+b}(x,y) $in Z", false);
}

#[test]
fn legacy_small_choice_definition_projection() {
    let source="forall I,S set,g fn(alpha I)S,f fn(alpha I)family_union(S),t I:\n    $is_choice_function_for(I,S,g,f)\n    =>:\n        f(t) $in g(t)";
    let evidence = check(source, true);
    assert!(evidence.contains("infers"));
    check(
        "forall I,S set,g fn(alpha I)S,f fn(alpha I)family_union(S),t I:\n    f(t) $in g(t)",
        false,
    );
}

#[test]
fn legacy_small_bijective_unique_preimage() {
    let evidence = check("forall A,B set,f fn(x A)B,y B:\n    $bijective(A,B,f)\n    =>:\n        exist! x A st {f(x)=y}",true);
    for key in [
        "BijectivePreimage",
        "certificate",
        "target_membership",
        "fact_id",
    ] {
        assert!(evidence.contains(key), "missing {key}");
    }
    check("forall A,B set,f fn(x A)B,y B:\n    $bijective(A,B,f)\n    =>:\n        exist! x A st {y=f(x)}",true);
    for code in [
        "forall A,B set,f fn(x A)B,y B:\n    $surjective(A,B,f)\n    =>:\n        exist! x A st {f(x)=y}",
        "forall f fn(x R)R:\n    $bijective(R,R,f)\n    =>:\n        exist! x R st {f(x)=i}",
        "forall A,B set,f fn(x A)B:\n    $bijective(A,B,f)\n    =>:\n        exist! x A st {f(x)=f(x)}",
        "forall A,B set,f fn(x A)B,y B:\n    exist! x A st {f(x)=y}",
    ] { check(code,false); }
}

#[test]
fn legacy_small_prime_definition_projection() {
    check("forall p N:\n    $prime(p)\n    =>:\n        2 <= p", true);
    check("forall p N:\n    $prime(p)\n    =>:\n        3 <= p", false);
}

#[test]
fn legacy_small_coprime_definition_projection() {
    check(
        "forall a, b N:\n    $coprime(a, b)\n    =>:\n        gcd(a, b) = 1",
        true,
    );
    check(
        "forall a, b N:\n    $coprime(a, b)\n    =>:\n        gcd(a, b) = 2",
        false,
    );
}

#[test]
fn legacy_small_rounding_identities() {
    check("forall x R:\n    floor(-x) = -ceil(x)", true);
    check("forall x R, n Z:\n    floor(x + n) = floor(x) + n", true);
    check("forall x R:\n    floor(x + 0.5) = floor(x) + 0.5", false);
}

#[test]
fn legacy_small_extrema_absorption() {
    check("forall a, b R:\n    min(a, max(a, b)) = a", true);
    check("forall a, b R:\n    max(a, min(a, b)) = a", true);
}
