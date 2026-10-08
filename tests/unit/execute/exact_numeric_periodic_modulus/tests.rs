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
                .expect("public statement pipeline");
            let json = emit_run_detailed(&result, &runtime, "eval", None);
            assert_eq!(result.success, expected, "{source}\n{json}");
            if !expected {
                assert!(
                    !json.contains("ParseError"),
                    "negative must reach mathematical verification: {json}"
                );
            }
            json
        })
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn exact_signed_integer_powers_and_eval() {
    for source in [
        "2^(-3)=1/8",
        "(-2)^(-3)=-1/8",
        "(-2)^(-2)=1/4",
        "3^(-2)=1/9",
        "(2/3)^(-2)=9/4",
        "2^(-3)*2^3=1",
        "eval 3^(-1)",
        "100000000000000000000^1=100000000000000000000",
    ] {
        check(source, true);
    }
    for source in ["0^(-1)=0", "2^(-3)=8", "(-2)^(-3)=1/8", "eval 2^(-100000)"] {
        check(source, false);
    }
    let json = check("3^(-2)=1/9", true);
    assert!(
        json.contains("by_closed_calculation")
            && json.contains("rational")
            && json.contains("left_normal")
    );
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime
        .run_litex_code("eval 3^(-1)\neval C_abs(3-4*i)")
        .unwrap();
    assert!(result.success);
    let normal = emit_run_normal(&result, &runtime, "eval", None);
    assert!(
        normal.contains("3 ^ -1 = 1 / 3") && normal.contains("C_abs(3 - 4 * i) = 5"),
        "{normal}"
    );
}

#[test]
fn exact_fraction_order_and_extrema() {
    for source in [
        "1/3 < 1/2",
        "1/2 > 1/3",
        "1/3 <= 2/6",
        "2/6 >= 1/3",
        "-1/2 < 1/(-3)",
        "1/(-3) > -1/2",
        "(1+1)/7 < 1/3",
        "not 1/3 > 1/2",
        "not 1/3 >= 1/2",
        "not 1/2 < 1/3",
        "not 1/2 <= 1/3",
        "min(1/3,1/2)=1/3",
        "max(1/3,1/2)=1/2",
        "eval min(1/3,1/2)",
        "3^(-1) < 1/2",
    ] {
        check(source, true);
    }
    for source in ["1/3 > 1/2", "1/3 < 2/6", "1/0 < 1/2", "min(1/3,1/2)=1/2"] {
        check(source, false);
    }
    let json = check("1/3 < 1/2", true);
    assert!(
        json.contains("by_closed_calculation")
            && json.contains("comparison")
            && json.contains("1 / 3")
    );
}

#[test]
fn integral_periods_and_reordered_angles() {
    for goal in [
        "tan(pi+2*k*pi)=0",
        "tan(k*pi)=0",
        "tan((k+j+1)*pi)=0",
        "tan(pi*(2*k+1))=0",
        "tan(pi-2*pi*k)=0",
        "tan(-pi+pi*k*2)=0",
        "tan(pi/4+k*pi)=1",
        "tan(-pi/4+k*pi)=-1",
        "cot(pi/4-k*pi)=1",
        "sin((k-j)*pi)=0",
        "cos(pi/2+k*pi)=0",
        "cos(pi+2*k*pi)=-1",
        "sin(pi/2+2*k*pi)=1",
        "sin(pi/6+2*k*pi)=1/2",
        "cos(pi/3+2*k*pi)=1/2",
        "tan(pi+(2*k-2*k)*pi)=0",
        "tan(pi/3+2*k*pi)=sqrt(3)",
        "cot(pi/6-3*j*pi)=sqrt(3)",
        "sin(pi/4+2*k*pi)=sqrt(2)/2",
        "cos(5*pi/6-2*j*pi)=-sqrt(3)/2",
        "tan(pi+2*(k+j)*pi)=0",
        "cos((1+k+k)*pi)=-1",
        "sin(pi/2+(k/2+k/2)*2*pi)=1",
    ] {
        check(&format!("have k,j Z\n{goal}"), true);
    }
    for source in [
        "tan(pi)=0",
        "tan(5*pi/4)=1",
        "cot(-pi/4)=-1",
        "sin(-pi/6)=-1/2",
        "cos(-pi/3)=1/2",
        "sin(7*pi/6)=-1/2",
        "cos(5*pi/3)=1/2",
    ] {
        check(source, true);
    }
    let json = check("have k Z\ntan(pi+2*k*pi)=0", true);
    assert!(
        json.contains("PeriodicTrig")
            && json.contains("integer_requirements")
            && json.contains("PeriodicTrigNonzero")
    );
}

#[test]
fn trig_poles_and_missing_period_evidence_reject() {
    for source in [
        "tan(pi/2)=0",
        "cot(pi)=0",
        "have k Z\ntan(pi/2+k*pi)=0",
        "have k R\ntan(pi+2*k*pi)=0",
        "have k Q\ntan(pi+k*pi)=0",
        "have k Z\nsin(pi+2*k*pi)=1",
        "have k Z\ncos(k*pi)=1",
        "have k Z\nsin(pi/2+k*pi)=1",
        "tan(pi+1)=0",
        "tan(pi*pi)=0",
        "have k Z\ntan(pi+2*k*pi/0)=0",
        "have k Z\ntan(pi+(1/k-1/k)*pi)=0",
    ] {
        check(source, false);
    }
}

#[test]
fn exact_complex_coordinates_all_requested_layouts() {
    for source in [
        "C_abs(3+4*i)=5",
        "C_abs(4*i+3)=5",
        "C_abs(3-4*i)=5",
        "C_abs(-4*i+3)=5",
        "C_abs(i*4+3)=5",
        "C_abs(-(3+4*i))=5",
        "C_abs(-3)=3",
        "C_abs(-i)=1",
        "C_abs(0)=0",
        "C_abs(0.3+0.4*i)=0.5",
        "C_abs(1/3+4/9*i)=5/9",
        "C_abs((1+i)*(1-i))=2",
        "C_abs(1+i)=sqrt(2)",
        "eval C_abs(3-4*i)",
        "eval C_abs(1+i)",
        "C_abs(1+i)=sqrt(2)\neval C_abs(1+i)",
        "5=C_abs(3-4*i)",
    ] {
        check(source, true);
    }
    for source in [
        "C_abs(3+4*i)=-5",
        "C_abs(3-4*i)=7",
        "C_abs(-i)=-1",
        "C_abs(0)=1",
        "C_abs(1+i)=1",
        "C_abs((3+4*i)/0)=5",
    ] {
        check(source, false);
    }
    let json = check("C_abs(-4*i+3)=5", true);
    assert!(json.contains("by_closed_calculation") && json.contains("left_normal"));
    // A non-rational principal root still uses the dedicated modulus rule and
    // retains its square/coordinate evidence; Direct has no radical algebra.
    let json = check("C_abs(1+i)=sqrt(2)", true);
    assert!(
        json.contains("NumericComplexModulus")
            && json.contains("squared_modulus")
            && json.contains("imaginary")
    );
}

#[test]
fn complex_modulus_nonnegative_and_unknown_coordinates() {
    check("have z C\nC_abs(z)>=0\n0<=C_abs(z)", true);
    check("have z C\nC_abs(z)>0", false);
    check("have a,b R\nC_abs(a+b*i)=5", false);
    check("C_abs({1})=1", false);
}

#[test]
fn new_rule_normal_output_is_bilingual() {
    for (source, en, zh) in [
        (
            "have k Z\ntan(pi+2*k*pi)=0",
            "Exact periodic trigonometric value",
            "精确周期三角值",
        ),
        ("C_abs(3+4*i)=5", "Closed calculation", "封闭计算"),
        ("3^(-2)=1/9", "Closed calculation", "封闭计算"),
        (
            "finite_set_max({1/3,1/2})=1/2",
            "Exact finite-set maximum",
            "有限集合最大值精确选取",
        ),
        ("pi/4<pi/2", "Exact pi coefficient order", "pi 系数精确比较"),
        ("e>1", "Euler constant exceeds one", "自然常数 e 大于一"),
    ] {
        for (language, expected) in [(OutputLanguage::English, en), (OutputLanguage::Chinese, zh)] {
            let mut runtime = Runtime::new(LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language,
            });
            let result = runtime.run_litex_code(source).unwrap();
            assert!(result.success);
            assert!(emit_run_normal(&result, &runtime, "eval", None).contains(expected));
        }
    }
}

#[test]
fn new_leaves_inherit_search_ceiling_and_do_not_store_search_facts() {
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};
    use crate::tokenize::Tokenizer;
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    assert!(
        runtime
            .run_litex_code("have k Z\nlet rational_max = finite_set_max({1/3,1/2})")
            .unwrap()
            .success
    );
    for source in [
        "tan(pi+2*k*pi)=0",
        "C_abs(3-4*i)=5",
        "3^(-2)=1/9",
        "1/3<1/2",
        "finite_set_max({1/3,1/2})=1/2",
        "pi/4<pi/2",
        "e>1",
    ] {
        let tokens = Tokenizer::new()
            .tokenize(source, runtime.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = runtime.parse(&tokens).unwrap().remove(0) else {
            panic!("fact");
        };
        let memory = |rt: &Runtime| {
            rt.execution_environments_stack
                .iter()
                .map(|env| {
                    (
                        env.facts.facts_by_id.len(),
                        env.well_defined_objects.object_to_wd_id.len(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let before = memory(&runtime);
        let state = VerifyState::new(VerifyStateLevel::BuiltinRule);
        assert!(
            !runtime
                .verify_fact(&fact, state.clone())
                .unwrap()
                .is_failed(),
            "{source}"
        );
        assert_eq!(
            before,
            memory(&runtime),
            "successful search is read-only: {source}"
        );
        let state = state.capped_at(VerifyStateLevel::KnownSpecialProperty);
        let calculated = matches!(source, "C_abs(3-4*i)=5" | "3^(-2)=1/9" | "1/3<1/2");
        assert_eq!(
            runtime.verify_fact(&fact, state).unwrap().is_failed(),
            !calculated,
            "closed calculation remains Direct; symbolic builtin is capped: {source}"
        );
        assert_eq!(
            before,
            memory(&runtime),
            "failed search is read-only: {source}"
        );
    }
}

#[test]
fn finite_rational_extrema_selection_certificate() {
    for source in [
        "finite_set_max({1/3,1/2})=1/2",
        "finite_set_min({1/3,1/2})=1/3",
        "finite_set_max({1/3})=1/3",
        "finite_set_min({-1/3,-1/2})=-1/2",
        "finite_set_max({1/2,1/3})=1/2",
        "1/3=finite_set_max({1/4,2/6})",
        "finite_set_min({3^(-1),1/2,2/3})=1/3",
        "finite_set_max({1/100000000000000000000,1/100000000000000000001})=1/100000000000000000000",
    ] {
        check(source, true);
    }
    for source in [
        "finite_set_max({1/3,1/2})=1/3",
        "finite_set_min({1/3,1/2})=1/2",
        "finite_set_max({})=0",
        "finite_set_min({1/3,2/6})=1/3",
        "finite_set_max({i,1/2})=1/2",
        "finite_set_min({1/0,1/2})=1/2",
    ] {
        check(source, false);
    }
    let json = check("finite_set_max({1/4,2/6})=1/3", true);
    assert!(
        json.contains("FiniteSetMaxSelection")
            && json.contains("selected_member")
            && json.contains("2 / 6")
            && json.contains("comparisons")
            && json.contains("\"ordering\": \"less\"")
            && json.contains("\"ordering\": \"equal\""),
        "{json}"
    );
    let json = check("finite_set_min({1/3,1/2})=1/3", true);
    assert!(
        json.contains("FiniteSetMinSelection") && json.contains("\"ordering\": \"greater\""),
        "{json}"
    );
}

#[test]
fn rational_pi_order_and_inverse_principal_values() {
    for source in [
        "(-pi)/2<pi/4",
        "pi/4<pi/2",
        "0<3*pi/4",
        "3*pi/4<pi",
        "(-3)*pi/4<(-pi)/2",
        "pi/4+pi/4<pi",
        "(-pi)/2 $in R\npi/2 $in R\npi/4 $in R\ncos(pi/4)!=0\ntan(pi/4)=1\n(-pi)/2<pi/4\npi/4<pi/2\narctan(1)=arctan(tan(pi/4))=pi/4",
        "(-pi)/2 $in R\npi/2 $in R\n(-pi)/4 $in R\ncos(-pi/4)!=0\ntan(-pi/4)=-1\n(-pi)/2<(-pi)/4\n(-pi)/4<pi/2\narctan(-1)=arctan(tan(-pi/4))=(-pi)/4",
        "0 $in R\npi $in R\npi/4 $in R\nsin(pi/4)!=0\ncot(pi/4)=1\n0<pi/4\npi/4<pi\narccot(1)=arccot(cot(pi/4))=pi/4",
        "0 $in R\npi $in R\n3*pi/4 $in R\nsin(3*pi/4)!=0\ncot(3*pi/4)=-1\n0<3*pi/4\n3*pi/4<pi\narccot(-1)=arccot(cot(3*pi/4))=3*pi/4",
    ] { check(source, true); }
    for source in [
        "pi/2<pi/4",
        "pi/4<pi/4",
        "pi/4<0",
        "arctan(tan(3*pi/4))=3*pi/4",
        "(-pi)/2 $in R\npi/2 $in R\n3*pi/4 $in R\ntan(3*pi/4)=-1\narctan(tan(3*pi/4))=3*pi/4",
        "arccot(cot(-pi/4))=-pi/4",
        "0 $in R\npi $in R\n(-pi)/4 $in R\ncot(-pi/4)=-1\narccot(cot(-pi/4))=-pi/4",
        "arccot(-1)=-pi/4",
        "arctan(1)=-pi/4",
        "arctan(tan(pi/2))=pi/2",
        "cot(0)=0",
        "cot(pi)=0",
        "have x R\nx*pi<pi",
        "pi/0<pi",
        "pi*pi<pi",
    ] {
        check(source, false);
    }
    let json = check("pi/4<pi/2", true);
    assert!(json.contains("PiMultipleComparison") && json.contains("left_coefficient"));
    let json = check("0 $in R\npi $in R\n3*pi/4 $in R\ncot(3*pi/4)=-1\n0<3*pi/4\n3*pi/4<pi\narccot(-1)=arccot(cot(3*pi/4))=3*pi/4", true);
    assert!(
        json.contains("ArccotCotRightInverse") && json.contains("proof_of_requirement_facts"),
        "{json}"
    );
}

#[test]
fn logarithm_algebra_for_positive_nonunit_bases() {
    for source in [
        "1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,1/2)=1",
        "1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,1)=0",
        "1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,(1/2)^(-3))=-3",
        "1/2 $in R\n1/2>0\n1/2!=1\n(1/2)^(-3)=8\nlog(1/2,8)=log(1/2,(1/2)^(-3))=-3",
        "e $in R\ne>1\ne!=1\ne>0\nlog(e,e)=1",
        "1 $in R\nforall b R:\n    b>0\n    b!=1\n    =>:\n        log(b,b)=1\n        log(b,1)=0",
        "1 $in R\nforall b R:\n    0<b\n    b!=1\n    =>:\n        log(b,b^(-3))=-3",
    ] {
        check(&format!("0 $in R\n{source}"), true);
    }
    for source in [
        "log(1,1)=1",
        "log(0,1)=0",
        "log(-2,-2)=1",
        "log(1/2,8)=3",
        "log(1/2,2)<log(1/2,4)",
        "e<1",
        "forall b R:\n    b>0\n    =>:\n        log(b,b)=1",
    ] {
        check(source, false);
    }
    let json = check(
        "0 $in R\n1/2 $in R\n1/2>0\n1/2!=1\nlog(1/2,(1/2)^(-3))=-3",
        true,
    );
    assert!(
        json.contains("by_closed_calculation") && json.contains("\"left_normal\": \"-3\""),
        "{json}"
    );
    let symbolic = check("0 $in R\n1 $in R\nforall b R:\n    0 < b\n    b != 1\n    =>:\n        log(b, b^(-3)) = -3", true);
    assert!(
        symbolic.contains("LogOfPowerSameBase") && symbolic.contains("proof_of_requirement_facts"),
        "{symbolic}"
    );
    let json = check("0 $in R\ne $in R\ne>1\ne!=1\ne>0\nlog(e,e)=1", true);
    assert!(
        json.contains("NativeEulerGreaterOne") && json.contains("LogBaseSelf"),
        "{json}"
    );
}

#[test]
fn arccos_principal_lower_bound_precedes_generic_zero_dispatch() {
    for lower in ["0", "0 + 0", "0 - 0"] {
        let source =
            format!("forall x R:\n    -1 <= x\n    x <= 1\n    =>:\n        {lower} <= arccos(x)");
        let json = check(&source, true);
        assert!(json.contains("ArccosPrincipalLowerBound"), "{json}");
    }
    for source in [
        "forall x R:\n    0 <= arccos(x)",
        "0 <= arccos(2)",
        "0 <= arccos(i)",
        "forall x R:\n    -1 <= x\n    x <= 1\n    =>:\n        1 <= arccos(x)",
    ] {
        check(source, false);
    }
}

#[test]
fn exact_rational_comparison_overflow_is_a_miss() {
    use crate::rational_expression::exact_rational::EvalRational;
    let left = EvalRational::new(100000000000000000001, 100000000000000000000).unwrap();
    let right = EvalRational::new(100000000000000000003, 100000000000000000002).unwrap();
    assert_eq!(left.compare(&right), None);
}
