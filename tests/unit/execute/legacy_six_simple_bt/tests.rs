use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
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
    let result = rt.run_litex_code(code).expect("public execution");
    assert!(result.session_error.is_none(), "{code}");
    assert_eq!(result.success, accepted, "{code}");
    crate::json_output::project_run_detailed(&result, rt, "eval", None)
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

#[test]
fn originals_keep_exact_rules_and_detailed_premises() {
    for (code, rule, fields) in ORIGINALS {
        let json = check(&mut runtime(OutputLanguage::English), code, true);
        let JsonValue::Object(evidence) = find_rule(&json, rule).expect(rule) else {
            panic!("rule object")
        };
        for field in *fields {
            let child = evidence.get(field).expect(field).stringify_pretty();
            assert!(child.contains("cite_fact_id"), "{rule}.{field}: {child}");
        }
    }
}

#[test]
fn false_formulas_missing_guards_and_invalid_domains_reject() {
    for code in NEGATIVES {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
}

#[test]
fn builtin_permissions_are_inherited() {
    for (code, _, _) in ORIGINALS {
        let mut rt = runtime(OutputLanguage::English);
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact")
        };
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::KnownSpecialProperty,
        ] {
            assert!(
                rt.verify_fact(&fact, VerifyState::new(level))
                    .unwrap()
                    .is_failed(),
                "{level:?}: {code}"
            );
        }
        // Some complex formula WD itself needs the enclosing top-level
        // allowance for nonnegative sums / nonzero squared denominators.
        assert!(
            !rt.verify_fact(&fact, VerifyState::top_level())
                .unwrap()
                .is_failed(),
            "{code}"
        );
    }
}

#[test]
fn rejected_statement_does_not_publish_or_poison_reuse() {
    let mut rt = runtime(OutputLanguage::English);
    for code in NEGATIVES {
        let before = rt.top_exec_env().facts.facts_by_id.len();
        check(&mut rt, code, false);
        assert_eq!(
            rt.top_exec_env().facts.facts_by_id.len(),
            before,
            "failed publication: {code}"
        );
    }
    for (code, _, _) in ORIGINALS {
        check(&mut rt, code, true);
        check(&mut rt, code, true);
    }
    for code in NEGATIVES {
        check(&mut rt, code, false);
    }
}

#[test]
fn actual_rules_are_available_in_all_output_locales() {
    for language in OutputLanguage::ALL {
        for (code, rule, _) in ORIGINALS {
            let mut rt = runtime(language);
            let json = check(&mut rt, code, true);
            assert!(find_rule(&json, rule).is_some(), "{language:?}: {rule}");
        }
    }
}

#[test]
fn fixed_argument_monotonicity_and_reverse_spellings() {
    for code in [
        "forall a,b,c R:\n    a<=b\n    =>:\n        min(a,c)<=min(b,c)\n",
        "forall a,b,c R:\n    a<=b\n    =>:\n        max(c,a)<=max(c,b)\n",
        "forall a C*,n Z:\n    a^(-n)=1/(a^n)\n",
        "forall a,b R:\n    a>=min(a,b)\n    max(a,b)>=b\n",
        "forall x R:\n    1>=sign(x)\n    sign(x)>=-1\n",
        "forall x R:\n    0=sign(x)\n    =>:\n        0=x\n",
        "forall x R:\n    0!=x\n    =>:\n        0!=sign(x)\n",
        "forall x R:\n    0!=sign(x)\n    =>:\n        0!=x\n",
    ] {
        check(&mut runtime(OutputLanguage::English), code, true);
    }
    for (code, rule, structural) in [
        (
            "forall a,b,c R:\n    a<=b\n    =>:\n        min(a,c)<=min(b,c)\n",
            "MinWeakMonotone",
            "right_order",
        ),
        (
            "forall a,b,c R:\n    a<=b\n    =>:\n        max(c,a)<=max(c,b)\n",
            "MaxWeakMonotone",
            "left_order",
        ),
    ] {
        let json = check(&mut runtime(OutputLanguage::English), code, true);
        let JsonValue::Object(fields) = find_rule(&json, rule).unwrap() else {
            panic!("rule")
        };
        assert!(fields
            .get(structural)
            .unwrap()
            .stringify()
            .contains("same_argument"));
    }
}

#[test]
fn guarded_forall_reuse_rechecks_in_source_order_when_needed() {
    let source = "forall z C,w C*:\n    C_abs(w)!=0\n    C_abs(w)^2!=0\n    re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2\n";
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, source, true);
    let reused = check(&mut rt, source, true);
    assert!(
        find_rule(&reused, "RealPartQuotient").is_some(),
        "local proof fallback must retain actual evidence"
    );
    check(
        &mut rt,
        &source
            .replace("z C,w C*", "u C,v C*")
            .replace("z/", "u/")
            .replace("(z)", "(u)")
            .replace("(w)", "(v)")
            .replace("/w", "/v"),
        true,
    );
    check(
        &mut rt,
        &source.replace("re(z)*re(w)+img(z)*img(w)", "re(z)*re(w)-img(z)*img(w)"),
        false,
    );
    check(
        &mut rt,
        &source
            .replace("w C*", "w C")
            .replace("    C_abs(w)!=0\n    C_abs(w)^2!=0\n", ""),
        false,
    );
    check(&mut rt, source, true);
}

// Exact formerly accepted sources are generated from the saved audit input,
// with dedicated expected rule IDs rather than success-only smoke checks.
const ORIGINALS: &[(&str, &str, &[&str])] = &[
    (
        r#"forall z C:
    sqrt(re(z)^2+img(z)^2)=C_abs(z)
"#,
        "ComplexModulusCoordinates",
        &[],
    ),
    (
        r#"forall z C,w C*:
    C_abs(w)!=0
    C_abs(w)^2!=0
    (re(z)*re(w)+img(z)*img(w))/C_abs(w)^2=re(z/w)
"#,
        "RealPartQuotient",
        &[],
    ),
    (
        r#"forall u C,v C*:
    C_abs(v)!=0
    C_abs(v)^2!=0
    img(u/v)=(img(u)*re(v)-re(u)*img(v))/C_abs(v)^2
"#,
        "ImaginaryPartQuotient",
        &[],
    ),
    (
        r#"forall z C:
    C_abs(z)=sqrt(re(z)^2+img(z)^2)
"#,
        "ComplexModulusCoordinates",
        &[],
    ),
    (
        r#"forall z C:
    0<=re(z)^2+img(z)^2
    C_abs(z)=sqrt(re(z)^2+img(z)^2)
"#,
        "ComplexModulusCoordinates",
        &[],
    ),
    (
        r#"forall z C,w C*:
    C_abs(w)!=0
    C_abs(w)^2!=0
    re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2
"#,
        "RealPartQuotient",
        &[],
    ),
    (
        r#"forall z C,w C*:
    C_abs(w)!=0
    C_abs(w)^2!=0
    img(z/w)=(img(z)*re(w)-re(z)*img(w))/C_abs(w)^2
"#,
        "ImaginaryPartQuotient",
        &[],
    ),
    (
        r#"forall a C,n N+:
    a!=0
    =>:
        a^(-n)=1/(a^n)
"#,
        "NegativeIntegerPowerReciprocal",
        &["base_nonzero"],
    ),
    (
        r#"forall a C:
    a!=0
    =>:
        a^(-2)=1/(a^2)
"#,
        "NegativeIntegerPowerReciprocal",
        &["base_nonzero"],
    ),
    (
        r#"forall a C:
    a!=0
    =>:
        1/(a^2)=a^(-2)
"#,
        "NegativeIntegerPowerReciprocal",
        &["base_nonzero"],
    ),
    (
        r#"forall a C,n N+:
    a!=0
    =>:
        a^(0-n)=1/(a^n)
"#,
        "NegativeIntegerPowerReciprocal",
        &["base_nonzero"],
    ),
    (
        r#"forall a,b,c,d R:
    a<=c
    b<=d
    =>:
        min(a,b)<=min(c,d)
"#,
        "MinWeakMonotone",
        &["left_order", "right_order"],
    ),
    (
        r#"forall a,b,c,d R:
    a<=c
    b<=d
    =>:
        max(a,b)<=max(c,d)
"#,
        "MaxWeakMonotone",
        &["left_order", "right_order"],
    ),
    (
        r#"forall a,b R:
    min(a,b)<=a
"#,
        "MinLowerBound",
        &[],
    ),
    (
        r#"forall a,b R:
    min(a,b)<=b
"#,
        "MinLowerBound",
        &[],
    ),
    (
        r#"forall a,b R:
    a<=max(a,b)
"#,
        "MaxUpperBound",
        &[],
    ),
    (
        r#"forall a,b R:
    b<=max(a,b)
"#,
        "MaxUpperBound",
        &[],
    ),
    (
        r#"forall n N:
    factorial(n)!=0
"#,
        "FactorialNonzero",
        &[],
    ),
    (
        r#"forall x R:
    exp(x)!=0
"#,
        "ExpNonzero",
        &[],
    ),
    (
        r#"forall x R:
    -1<=sign(x)
"#,
        "SignLowerBound",
        &[],
    ),
    (
        r#"forall x R:
    sign(x)<=1
"#,
        "SignUpperBound",
        &[],
    ),
    (
        r#"forall x R:
    sign(x)=0
    =>:
        x=0
"#,
        "SignZeroReflection",
        &["premise_proof"],
    ),
    (
        r#"forall x R:
    x!=0
    =>:
        sign(x)!=0
"#,
        "SignNonzeroFromArgument",
        &["argument_nonzero"],
    ),
    (
        r#"forall x R:
    sign(x)!=0
    =>:
        x!=0
"#,
        "SignNonzeroReflection",
        &["sign_nonzero"],
    ),
    (
        r#"forall a,b R:
    a<=b
    =>:
        sign(a)<=sign(b)
"#,
        "SignWeakMonotone",
        &["argument_order"],
    ),
    (
        r#"forall a,b R:
    b>=a
    =>:
        sign(b)>=sign(a)
"#,
        "SignWeakMonotone",
        &["argument_order"],
    ),
];

const NEGATIVES: &[&str] = &[
    "forall a C,n N+:\n    a^(-n)=1/(a^n)\n",
    "forall a C*,n R:\n    a^(-n)=1/(a^n)\n",
    "forall a C*,n N+:\n    a^n=1/(a^n)\n",
    "forall a,b C*,n N+:\n    a^(-n)=1/(b^n)\n",
    "forall a C*,n N+:\n    a^(-n)=2/(a^n)\n",
    "forall a C*,n N+:\n    a^(-n)=1/(a^(n+1))\n",
    "0^(-2)=1/(0^2)\n",
    "forall z C:\n    C_abs(z)=sqrt(re(z)^2-img(z)^2)\n",
    "forall z C:\n    C_abs(z)=sqrt(re(z)^2+img(z)^3)\n",
    "forall z,w C:\n    C_abs(z)=sqrt(re(w)^2+img(w)^2)\n",
    "forall z C:\n    C_abs(z)=-sqrt(re(z)^2+img(z)^2)\n",
    "forall z C:\n    C_abs(z)=re(z)+img(z)\n",
    "forall z set:\n    C_abs(z)=sqrt(re(z)^2+img(z)^2)\n",
    "forall z,w C:\n    re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2\n",
    "forall z C,w C*:\n    C_abs(w)!=0\n    C_abs(w)^2!=0\n    re(z/w)=(re(z)*re(w)-img(z)*img(w))/C_abs(w)^2\n",
    "forall z C,w C*:\n    C_abs(w)!=0\n    C_abs(w)^2!=0\n    img(z/w)=(img(z)*re(w)+re(z)*img(w))/C_abs(w)^2\n",
    "forall z C,w C*:\n    C_abs(w)!=0\n    C_abs(w)^2!=0\n    re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(z)^2\n",
    "forall z C,w C*:\n    C_abs(w)!=0\n    C_abs(w)^2!=0\n    img(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2\n",
    "forall x C:\n    exp(x)!=0\n",
    "forall n Z:\n    factorial(n)!=0\n",
    "forall n R:\n    factorial(n)!=0\n",
    "factorial(-1)!=0\n",
    "forall x R:\n    exp(x)!=1\n",
    "forall n N:\n    factorial(n)!=1\n",
    "forall x R:\n    0<=sign(x)\n",
    "forall x R:\n    sign(x)<=0\n",
    "forall x R:\n    -1<sign(x)\n",
    "forall x R:\n    sign(x)<1\n",
    "forall x C:\n    -1<=sign(x)\n",
    "forall x R:\n    sign(x)=0\n    =>:\n        x=1\n",
    "forall x R:\n    sign(x)=1\n    =>:\n        x=0\n",
    "forall x R:\n    x=0\n",
    "forall x R:\n    sign(x)!=0\n",
    "forall x R:\n    x!=0\n",
    "forall x R:\n    x=0\n    =>:\n        sign(x)!=0\n",
    "forall x R:\n    sign(x)!=0\n    =>:\n        x!=1\n",
    "forall a,b R:\n    a<=b\n    =>:\n        sign(a)<sign(b)\n",
    "forall a,b R:\n    sign(a)<=sign(b)\n    =>:\n        a<=b\n",
    "forall a,b R:\n    sign(a)<=sign(b)\n",
    "forall a,b R:\n    b<=a\n    =>:\n        sign(a)<=sign(b)\n",
    "forall a,b R:\n    a<=min(a,b)\n",
    "forall a,b R:\n    max(a,b)<=a\n",
    "forall a,b R:\n    min(a,b)<a\n",
    "forall a,b R:\n    a<max(a,b)\n",
    "forall a,b,c R:\n    min(a,b)<=c\n",
    "forall a,b C:\n    min(a,b)<=a\n",
    "forall a,b,c,d R:\n    a<=c\n    =>:\n        min(a,b)<=min(c,d)\n",
    "forall a,b,c,d R:\n    b<=d\n    =>:\n        max(a,b)<=max(c,d)\n",
    "forall a,b,c,d R:\n    a<=c\n    b<=d\n    =>:\n        min(a,b)<min(c,d)\n",
    "forall a,b,c,d R:\n    a<=c\n    b<=d\n    =>:\n        max(a,b)<max(c,d)\n",
    "forall a,b,c,d R:\n    a<=c\n    b<=d\n    =>:\n        min(c,d)<=min(a,b)\n",
];

#[test]
fn run_examples_legacy_six_simple_bt_tracers() {
    for relative in [
        "examples/proof_nodes/equal/by_builtin_rule/power_negative_integer_reciprocal.lit",
        "examples/proof_nodes/equal/by_builtin_rule/complex_modulus_coordinates_symbolic.lit",
        "examples/proof_nodes/equal/by_builtin_rule/complex_quotient_real_coordinates.lit",
        "examples/proof_nodes/equal/by_builtin_rule/complex_quotient_imaginary_coordinates.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/exp_nonzero_intrinsic.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/factorial_nonzero_intrinsic.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/sign_lower_bound.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/sign_upper_bound.lit",
        "examples/proof_nodes/equal/by_builtin_rule/sign_zero_reflection.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/sign_nonzero_from_argument.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/sign_nonzero_reflection.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/sign_weak_monotone.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/binary_min_lower_bound.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/binary_max_upper_bound.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/binary_min_weak_monotone.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/binary_max_weak_monotone.lit",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
        let code = std::fs::read_to_string(&path).unwrap();
        check(&mut runtime(OutputLanguage::English), &code, true);
    }
}
