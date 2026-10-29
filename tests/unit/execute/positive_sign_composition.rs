use crate::prelude::*;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

fn check(rt: &mut Runtime, source: &str, expected: bool) -> RunLitexCodeResult {
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.session_error.is_none(),
        "{source}: {:?}",
        run.session_error
    );
    assert_eq!(run.success, expected, "{source}");
    run
}

const EXAMPLE: &str = include_str!(
    "../../../examples/proof_nodes/atomic/by_builtin_rule/positive_sign_composition.lit"
);

#[test]
fn run_examples_positive_sign_composition() {
    check(&mut runtime(OutputLanguage::English), EXAMPLE, true);
}

#[test]
fn positive_sign_composition_direct_carriers_and_orientation() {
    for source in [
        "have fn f(x R:x>0) R+=x+1",
        "have fn f(x R:0<x) R+=x+1",
        "forall x,y,z R+:\n    (x+y)+z $in R+",
        "forall x,y,z R+:\n    (x+y)+z>=0\n    =>:\n        (x+y)+z $in R+",
        "forall x R:\n    x^2!=0\n    =>:\n        x^2 $in R+",
        "forall x,y,z Q+:\n    x*(y*z) $in Q+",
        "forall x,y,z R-:\n    (x+y)+z $in R-",
        "forall x R:\n    x^2+1 $in R+",
        "forall x R*:\n    x^4 $in R+",
        "forall x R*:\n    abs(x)+1 $in R+",
        "forall x R+:\n    sqrt(x)+1 $in R+",
        "forall x R+:\n    0!=x+1",
        "forall x R+:\n    1/(x+1)=1/(x+1)",
        "forall x R:\n    x>=0\n    x!=0\n    =>:\n        x+1 $in R+",
        "forall x,y R:\n    0<=x\n    0<y\n    =>:\n        x+y $in R+",
        "forall x,y R:\n    x<=0\n    y<0\n    =>:\n        x+y $in R-",
        "forall x,y R:\n    x>=0\n    y>=0\n    =>:\n        0<=x+y",
        "forall x,y R:\n    x<=0\n    y<=0\n    =>:\n        x+y<=0",
        "forall x,y R:\n    x<=0\n    y<=0\n    =>:\n        x*y>=0",
        "forall x,y R:\n    x>=0\n    y<=0\n    =>:\n        x*y<=0",
        "forall x,y R:\n    x>=0\n    y>0\n    =>:\n        max(x,y) $in R+",
        "forall x,y R:\n    x<=0\n    y<0\n    =>:\n        min(x,y) $in R-",
        "forall x,y R:\n    x>0\n    y>=0\n    =>:\n        max(y,x) $in R+",
        "forall x,y R:\n    x<0\n    y<=0\n    =>:\n        min(y,x) $in R-",
    ] {
        check(&mut runtime(OutputLanguage::English), source, true);
    }
}

#[test]
fn positive_sign_composition_rejects_missing_premises_and_invalid_domains() {
    for source in [
        "have fn f(x R:x>=0) R+=x",
        "have fn f(x R) R+=x+1",
        "forall x,y R:\n    x>=0\n    y>=0\n    =>:\n        x+y $in R+",
        "forall x R:\n    x^2 $in R+",
        "forall x R:\n    abs(x) $in R+",
        "forall x R:\n    x>=0\n    =>:\n        sqrt(x) $in R+",
        "forall x,y R+:\n    x-y $in R+",
        "forall x R+,y R-:\n    x*y $in R+",
        "forall x R+,y R-:\n    x/y $in R+",
        "forall x R:\n    x>=0\n    =>:\n        1/x=1/x",
        "1/(1-1)=1/(1-1)",
        "sqrt(-1)+1 $in R+",
        "forall x C:\n    x^2+1 $in R+",
        "forall x C*:\n    abs(x)+1 $in R+",
        "forall x R+,y R:\n    min(x,y) $in R+",
        "forall x,y R:\n    x>=0\n    y>=0\n    =>:\n        min(x,y)!=0",
        "forall x R-,y R:\n    max(x,y)<0",
        "forall x,y R:\n    x<=0\n    y<=0\n    =>:\n        max(x,y)<0",
        "forall x R:\n    x>=0\n    =>:\n        x!=0",
        "forall x R:\n    x!=0\n    =>:\n        x>0",
    ] {
        check(&mut runtime(OutputLanguage::English), source, false);
    }
}

#[test]
fn positive_sign_composition_ordered_field_sign_matrix() {
    // Independent arithmetic oracle: strict signs determine product/quotient
    // signs, while opposite-sign sums have no uniform strict sign.
    for (a, av) in [("R+", 2), ("R-", -3)] {
        for (b, bv) in [("R+", 5), ("R-", -7)] {
            for op in ["*", "/"] {
                for (carrier, positive) in [("R+", true), ("R-", false)] {
                    let expected = (av * bv > 0) == positive;
                    let source = format!("forall x {a},y {b}:\n    x{op}y $in {carrier}");
                    check(&mut runtime(OutputLanguage::English), &source, expected);
                }
            }
            for (carrier, positive) in [("R+", true), ("R-", false)] {
                let expected = (av > 0) == (bv > 0) && (av > 0) == positive;
                let source = format!("forall x {a},y {b}:\n    x+y $in {carrier}");
                check(&mut runtime(OutputLanguage::English), &source, expected);
            }
        }
    }
}

#[test]
fn positive_sign_composition_certificates_locales_and_reading() {
    let source = "forall x,y R:\n    x>0\n    y>=0\n    =>:\n        (x+y)+1 $in R+\n";
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        let run = check(&mut rt, source, true);
        let detail =
            crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
        for field in ["base_membership", "sign", "source", "cite_fact_id"] {
            assert!(
                detail.contains(&crate::json_output::json_keys::localize_key(
                    field, language
                )),
                "missing {field}: {detail}"
            );
        }
        for value in [
            "SignedNumericMembership",
            "by_structural_real_sign",
            "Positive",
            "Nonnegative",
            "add",
        ] {
            assert!(detail.contains(value), "missing {value}: {detail}");
        }
        let normal =
            crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
        assert!(!normal.contains("unsupported") && !normal.contains("unreachable"));
    }
    let result = crate::reading::build_reading(
        &crate::reading::ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let reading = result.document.stringify_pretty();
    for value in [
        "SignedNumericMembership",
        "StructuralRealSignReason",
        "source",
        "base_membership",
    ] {
        assert!(reading.contains(value), "missing {value}: {reading}");
    }
    assert!(result
        .document
        .as_object()
        .unwrap()
        .get("diagnostics")
        .unwrap()
        .as_array()
        .unwrap()
        .is_empty());
}

#[test]
fn positive_sign_composition_failure_is_read_only_and_scoped() {
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, "have x,y R", true);
    check(&mut rt, "sketch:\n    x>0", false);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("x+1 $in R+", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    let count = rt.top_exec_env().facts.facts_by_id.len();
    assert!(rt
        .verify_fact(&fact, VerifyState::top_level())
        .unwrap()
        .is_failed());
    assert_eq!(count, rt.top_exec_env().facts.facts_by_id.len());
    check(&mut rt, "x=x", true);
    check(
        &mut rt,
        "forall z R:\n    z>0\n    =>:\n        z+1 $in R+",
        true,
    );
    check(&mut rt, "x+1 $in R+", false);
    check(&mut rt, "x=x", true);
}

#[test]
fn positive_sign_composition_function_return_respects_inherited_permission() {
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, "have fn f(x R) R+=x^2+1", true);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("f(2)+1 $in R+", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::InFact(fact))) =
        rt.parse(&tokens).unwrap().remove(0)
    else {
        panic!("membership")
    };
    assert!(rt
        .search_structural_real_sign(&fact.element, VerifyState::new(VerifyStateLevel::Direct))
        .is_none());
    let proof = rt
        .search_structural_real_sign(
            &fact.element,
            VerifyState::new(VerifyStateLevel::KnownSpecialProperty).without_inference(),
        )
        .expect("declared positive return is a permitted leaf");
    assert_eq!(proof.sign, RealSign::Positive);
    check(&mut rt, "forall x R:\n    1/(f(x)+1)=1/(f(x)+1)", true);
}

#[test]
fn positive_sign_composition_deep_nesting_and_lean_replay() {
    let expression = (0..20).fold("x".to_owned(), |e, _| format!("({e}+x)"));
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, "have x R+", true);
    let source = format!("{expression} $in R+");
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(&source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::InFact(fact))) =
        rt.parse(&tokens).unwrap().remove(0)
    else {
        panic!("membership")
    };
    // Exercise this traversal separately from the existing enclosing WD walk.
    let proof = rt
        .search_structural_real_sign(&fact.element, VerifyState::new(VerifyStateLevel::Direct))
        .expect("strict descent at inherited Direct permission");
    assert_eq!(proof.sign, RealSign::Positive);
    let expression = (0..12).fold("x".to_owned(), |e, _| format!("({e}+x)"));
    check(
        &mut runtime(OutputLanguage::English),
        &format!("forall x R+:\n    {expression} $in R+"),
        true,
    );
    for source in [
        "have fn f(x R:x>0) R+=x+1",
        "forall x,y,z R+:\n    (x+y)+z $in R+",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let run = check(&mut rt, source, true);
        let output = crate::compile_to_lean::compile_run(&run, rt, "positive_sign_composition")
            .expect("the selected sign tree has a checked Lean adapter");
        assert!(output.contains("Litex.addPositive"));
        assert!(output.contains("Litex.inRPos_intro"));
        assert!(!output.contains("sorry"));
    }
}
