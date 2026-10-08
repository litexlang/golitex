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

mod fixtures;
use fixtures::{NEGATIVES, ORIGINALS};

#[test]
fn exact_originals_and_variants_pass_in_fresh_runtime() {
    for code in ORIGINALS {
        check(&mut runtime(OutputLanguage::English), code, true);
    }
}
#[test]
fn false_formulas_missing_guards_and_domains_reject() {
    for code in NEGATIVES {
        check(&mut runtime(OutputLanguage::English), code, false);
    }
}
#[test]
fn failed_statements_discard_and_one_live_runtime_reuses_context() {
    let mut rt = runtime(OutputLanguage::English);
    for code in NEGATIVES {
        let before = rt.top_exec_env().facts.facts_by_id.len();
        check(&mut rt, code, false);
        assert_eq!(before, rt.top_exec_env().facts.facts_by_id.len(), "{code}");
    }
    for code in ORIGINALS {
        check(&mut rt, code, true);
        check(&mut rt, code, true);
    }
    for code in NEGATIVES {
        check(&mut rt, code, false);
    }
}
#[test]
fn inherited_search_permissions_do_not_reopen_builtin_entry() {
    for code in [
        "forall n N+:\n    factorial(n)=n*factorial(n-1)\n",
        "forall x,y R:\n    exp(x)=exp(y)\n    =>:\n        x=y\n",
        "forall a,b,c R:\n    b!=0\n    a/b=c\n    =>:\n        a=c*b\n",
        "forall x,n Z:\n    n<=x\n    x<n+1\n    =>:\n        x=n\n",
        "forall a,b R:\n    0<a\n    b<0\n    =>:\n        a*b<0\n",
    ] {
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
        assert!(
            !rt.verify_fact(&fact, VerifyState::top_level())
                .unwrap()
                .is_failed(),
            "{code}"
        );
    }
}
#[test]
fn rules_keep_their_actual_source_evidence_and_all_locales() {
    for lang in OutputLanguage::ALL {
        for (code, rule, fields) in EVIDENCE_CASES {
            let mut rt = runtime(lang);
            let json = check(&mut rt, code, true);
            let JsonValue::Object(proof) = find_rule(&json, rule).expect(rule) else {
                panic!("rule")
            };
            for field in *fields {
                assert!(proof.get(field).is_some(), "{lang:?}: {rule}.{field}");
            }
        }
    }
}
const EVIDENCE_CASES: &[(&str,&str,&[&str])] = &[
    ("forall n N+:\n    factorial(n)=n*factorial(n-1)\n","FactorialPredecessor",&["positive_natural"]),
    ("forall x,y R:\n    exp(x)=exp(y)\n    =>:\n        x=y\n","ExpInjective",&["left_real","right_real","image_equality"]),
    ("forall x,y R+:\n    ln(x)=ln(y)\n    =>:\n        x=y\n","LnInjective",&["left_positive","right_positive","image_equality"]),
    ("forall a,x R+,n Z:\n    a!=1\n    a^n=x\n    =>:\n        log(a,x)=n\n","LogFromKnownPower",&["base_proof","exponent_integer","power_equality"]),
    ("forall a,b,c R:\n    b!=0\n    a/b=c\n    =>:\n        a=c*b\n","ProductFromDivision",&["division_equation"]),
    ("forall x R:\n    (-4)<x\n    =>:\n        (-6)<=x\n","LiteralWeakBound",&["source_order"]),
    ("forall x Z:\n    4>x\n    =>:\n        x<=3\n","IntegerSuccessorGap",&["left_integer","right_integer","strict_order"]),
    ("forall a,b,c,d R:\n    b>a\n    d>c\n    =>:\n        a+c<b+d\n","SumStrictOperands",&["first_order","second_order"]),
    ("forall x,b R:\n    -b<=x\n    x<=b\n    =>:\n        abs(x)<=b\n","AbsFromIntervalBounds",&["lower_bound","upper_bound"]),
    ("forall x,y R:\n    0<=x\n    x<=y\n    =>:\n        sqrt(x)<=sqrt(y)\n","SqrtMonotoneFromDefinedRoots",&["arguments_order"]),
    ("forall x R:\n    x<=0\n    =>:\n        sqrt(x^2)=-x\n","SqrtSquareNonpositive",&["nonpositive_argument"]),
    ("forall x,n Z:\n    n<=x\n    x<n+1\n    =>:\n        n=x\n","IntegerSingletonAtLower",&["variable_integer","boundary_integer","lower_weak","upper_strict"]),
    ("forall x,n N:\n    n<x\n    x<=n+1\n    =>:\n        x=n+1\n","IntegerSingletonAtUpper",&["variable_integer","boundary_integer","lower_strict","upper_weak"]),
    ("forall a,b,z R:\n    z=0\n    a*b!=z\n    =>:\n        a!=0\n","ProductFactorNonzeroWithZeroAlias",&["product_nonzero","zero_equality"]),
    ("forall a,b R+:\n    a/b $in R+\n","PositiveRealQuotient",&["numerator_positive","denominator_positive"]),
    ("forall a,b Q*:\n    a*b $in Q*\n","NonzeroRationalProduct",&["left_nonzero_rational","right_nonzero_rational"]),
    ("forall a,b R:\n    0<=a\n    b<0\n    =>:\n        a*b<=0\n","ProductNonnegativeNegativeWeak",&["nonnegative_factor","negative_factor"]),
    ("forall a,b R:\n    0<a\n    b<0\n    =>:\n        a*b<0\n","ProductPositiveNegativeStrict",&["positive_factor","negative_factor"]),
    ("forall x R+:\n    1<x\n    =>:\n        0<ln(x)\n","LnPositiveAboveOne",&["above_one"]),
    ("forall x,y R:\n    -1<=x\n    x<=1\n    -pi/2<=y\n    y<=pi/2\n    sin(y)=x\n    =>:\n        arcsin(x)=y\n","ArcsinFromKnownSine",&["principal_bounds","sine_equality"]),
];

#[test]
fn run_examples_legacy_remaining_local_migration() {
    let root=std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for path in EXAMPLES {
        let source=std::fs::read_to_string(root.join(path)).unwrap();
        check(&mut runtime(OutputLanguage::English),&source,true);
    }
    assert_eq!(EXAMPLES.len(),50);
    println!("checked {} maintained examples",EXAMPLES.len());
}
const EXAMPLES:&[&str]=&[
    "examples/proof_nodes/equal/by_builtin_rule/factorial_predecessor.lit",
    "examples/proof_nodes/equal/by_builtin_rule/exp_injective.lit",
    "examples/proof_nodes/equal/by_builtin_rule/ln_injective.lit",
    "examples/proof_nodes/equal/by_builtin_rule/log_below_unit_self.lit",
    "examples/proof_nodes/equal/by_builtin_rule/log_below_unit_one.lit",
    "examples/proof_nodes/equal/by_builtin_rule/log_below_unit_integer_power.lit",
    "examples/proof_nodes/equal/by_builtin_rule/log_from_known_integer_power.lit",
    "examples/proof_nodes/equal/by_builtin_rule/power_from_known_integer_log.lit",
    "examples/proof_nodes/equal/by_builtin_rule/exp_difference.lit",
    "examples/proof_nodes/equal/by_builtin_rule/ln_product.lit",
    "examples/proof_nodes/equal/by_builtin_rule/ln_quotient.lit",
    "examples/proof_nodes/equal/by_builtin_rule/scalar_product_from_known_division.lit",
    "examples/proof_nodes/equal/by_builtin_rule/scalar_division_from_known_product.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/sin_nonzero_negation.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/cos_nonzero_negation.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/sin_nonzero_integer_pi_shift.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/cos_nonzero_integer_pi_shift.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/tan_nonzero_from_sine.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/cot_nonzero_from_cosine.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/euler_nonunit.lit",
    "examples/proof_nodes/equal/by_builtin_rule/sin_three_angle_sum.lit",
    "examples/proof_nodes/equal/by_builtin_rule/tan_addition.lit",
    "examples/proof_nodes/less_equal/by_builtin_rule/literal_weak_bound.lit",
    "examples/proof_nodes/less_equal/by_builtin_rule/integer_successor_gap.lit",
    "examples/proof_nodes/less/by_builtin_rule/reverse_written_order_transitivity.lit",
    "examples/proof_nodes/less/by_builtin_rule/negation_strict_order.lit",
    "examples/proof_nodes/less_equal/by_builtin_rule/negation_weak_order.lit",
    "examples/proof_nodes/less/by_builtin_rule/negation_negative_from_literal_bound.lit",
    "examples/proof_nodes/less/by_builtin_rule/sum_strict_operands.lit",
    "examples/proof_nodes/less_equal/by_builtin_rule/abs_from_interval_bounds.lit",
    "examples/proof_nodes/less_equal/by_builtin_rule/sqrt_monotone_defined_roots.lit",
    "examples/proof_nodes/equal/by_builtin_rule/sqrt_known_square_nonnegative.lit",
    "examples/proof_nodes/equal/by_builtin_rule/sqrt_square_nonpositive.lit",
    "examples/proof_nodes/equal/by_builtin_rule/integer_singleton_lower.lit",
    "examples/proof_nodes/equal/by_builtin_rule/integer_singleton_upper.lit",
    "examples/proof_nodes/not_equal/by_builtin_rule/product_factor_nonzero_zero_alias.lit",
    "examples/proof_nodes/in/by_builtin_rule/positive_real_quotient.lit",
    "examples/proof_nodes/in/by_builtin_rule/nonzero_rational_product.lit",
    "examples/proof_nodes/less_equal/by_builtin_rule/product_nonnegative_negative.lit",
    "examples/proof_nodes/less/by_builtin_rule/product_positive_negative.lit",
    "examples/proof_nodes/less/by_builtin_rule/ln_positive_above_one.lit",
    "examples/proof_nodes/less/by_builtin_rule/ln_negative_below_one.lit",
    "examples/proof_nodes/equal/by_builtin_rule/positive_power_reciprocal_root.lit",
    "examples/proof_nodes/equal/by_builtin_rule/real_log_from_known_power.lit",
    "examples/proof_nodes/equal/by_builtin_rule/positive_power_log_inverse.lit",
    "examples/proof_nodes/equal/by_builtin_rule/sqrt_product_from_known_argument.lit",
    "examples/proof_nodes/equal/by_builtin_rule/sqrt_quotient_from_known_argument.lit",
    "examples/proof_nodes/equal/by_builtin_rule/positive_integer_power_injective.lit",
    "examples/proof_nodes/equal/by_builtin_rule/arcsin_from_known_sine.lit",
    "examples/proof_nodes/equal/by_builtin_rule/nested_remainder_unit.lit",
];
