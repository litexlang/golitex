use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof as Rule;
use crate::prelude::*;
const CASES: [(&str, &str, &str); 4] = [
    (
        r#"forall x R:
    x<=0
    =>:
        sqrt(x^2)=0-x
"#,
        "SqrtSquareNonpositive",
        "sqrtOfNonpositiveSquareValue",
    ),
    (
        r#"forall a Z, m N+:
    (-a)%m=(m-a%m)%m
"#,
        "ModNegation",
        "remainderNegationValue",
    ),
    (
        r#"forall a Z, m N+, n N:
    (a^n)%m=((a%m)^n)%m
"#,
        "ModNaturalPower",
        "remainderNaturalPowerValue",
    ),
    (
        r#"forall a R, p,q C:
    0<=a
    q!=0
    sqrt(a)=p/q
    =>:
        p^2=a*q^2
"#,
        "SqrtQuotientSquare",
        "sqrtQuotientSquareValue",
    ),
];
fn target(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn selected(p: &mut VerifyEqualitySuccess) -> &mut Rule {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ElementaryArithmetic(p),
    ) = &mut p.searched_proof
    else {
        panic!("exact selected elementary arithmetic rule");
    };
    p
}
#[test]
fn elementary_arithmetic_replays_original_selected_rules_in_both_equation_orientations() {
    for (source, rule, law) in CASES {
        let (prefix, last) = source.trim_end().rsplit_once('\n').unwrap();
        let indent = &last[..last.len() - last.trim_start().len()];
        let (left, right) = last.trim().split_once('=').unwrap();
        let reversed = format!("{prefix}\n{indent}{right}={left}\n");
        for source in [source, &reversed] {
            let (mut run, compiler) = super::execute(source);
            assert_eq!(selected(target(&mut run)).rule_id(), rule);
            let output = compiler
                .compile_run(&run, "elementary_arithmetic")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
            assert!(output.contains(&format!("Litex.{law}")));
            assert_eq!(
                output,
                compiler.compile_run(&run, "elementary_arithmetic").unwrap()
            );
        }
    }
}
#[test]
fn elementary_arithmetic_keeps_original_endpoint_wd_and_zero_subtraction_profiles() {
    for (source, _, _) in CASES {
        let (mut run, compiler) = super::execute(source);
        let wd = target(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        compiler
            .compile_run(&run, "changed_wd")
            .expect_err("original constructors must match their endpoints");
    }
    for source in [
        CASES[0].0.replace("0-x", "-x"),
        CASES[1].0.replace("(-a)", "(0-a)"),
    ] {
        let (mut run, compiler) = super::execute(&source);
        selected(target(&mut run));
        compiler
            .compile_run(&run, "negation_profile")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}
#[test]
fn remainder_rules_cannot_omit_exchange_weaken_or_cite_future_original_requirements() {
    for index in [1, 2] {
        for mutation in ["missing", "swapped", "carrier", "future"] {
            let (mut run, compiler) = super::execute(CASES[index].0);
            let p = target(&mut run);
            let future = p.fact.fact_id;
            let children = match selected(p) {
                Rule::ModNegation { requirements } | Rule::ModNaturalPower { requirements } => {
                    requirements
                }
                _ => panic!(),
            };
            match mutation {
                "missing" => {
                    children.pop();
                }
                "swapped" => children.swap(0, 1),
                "carrier" => {
                    let AtomicFact::InFact(f) =
                        &mut super::atomic_proof_mut(&mut children[index]).fact
                    else {
                        panic!();
                    };
                    f.set = Obj::StandardSet(StandardSet::R);
                }
                _ => {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut super::atomic_proof_mut(&mut children[0]).searched_proof
                    else {
                        panic!("integer citation");
                    };
                    cite.cite_fact_id = future;
                }
            }
            compiler.compile_run(&run, mutation).expect_err(
                "original ordered integer/positive-modulus/natural-exponent evidence is required",
            );
        }
    }
}
#[test]
fn nonpositive_square_keeps_original_bound_subject_direction_and_citation() {
    for mutation in ["direction", "future", "missing"] {
        let (mut run, compiler) = super::execute(CASES[0].0);
        let p = target(&mut run);
        let future = p.fact.fact_id;
        let Rule::SqrtSquareNonpositive(p) = selected(p) else {
            panic!();
        };
        let p = super::atomic_proof_mut(&mut p.nonpositive_argument);
        if mutation == "direction" {
            let AtomicFact::LessEqualFact(f) = &mut p.fact else {
                panic!();
            };
            std::mem::swap(&mut f.left, &mut f.right);
        } else {
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut p.searched_proof
            else {
                panic!("original nonpositive citation");
            };
            cite.cite_fact_id = if mutation == "future" {
                future
            } else {
                FactId::new(u64::MAX)
            };
        }
        compiler
            .compile_run(&run, mutation)
            .expect_err("the original visible nonpositive comparison must be replayed");
    }
}

#[test]
fn quotient_square_replays_the_original_root_ratio_wd_and_visible_equation() {
    for mutation in ["future", "missing", "wd", "radicand", "denominator"] {
        let (mut run, compiler) = super::execute(CASES[3].0);
        let p = target(&mut run);
        let future = p.fact.fact_id;
        let Rule::SqrtQuotientSquare(p) = selected(p) else {
            panic!();
        };
        let p = super::equality_proof_mut(&mut p.quotient_equation);
        if mutation == "wd" {
            let wd = p.well_defined_proof.as_detailed_mut().unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
        } else if mutation == "radicand" {
            let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) = &mut p.fact.left else {
                panic!();
            };
            root.arg = Box::new(Obj::Literal(Literal::Number(Number::new("1".into()))));
        } else if mutation == "denominator" {
            let Obj::ArithmeticOperator(ArithmeticOperator::Div(ratio)) = &mut p.fact.right else {
                panic!();
            };
            ratio.right = Box::new(Obj::Literal(Literal::Number(Number::new("0".into()))));
        } else {
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &mut p.searched_proof
            else {
                panic!("original visible root-ratio equation");
            };
            assert!(!path.path.is_empty());
            if mutation == "future" {
                path.path[0].2 = future;
            } else {
                path.path.clear();
            }
        }
        compiler
            .compile_run(&run, mutation)
            .expect_err("the original defined root, nonzero ratio and cited equation are required");
    }
    let source = CASES[3].0.replace("p^2=a*q^2", "q^2*a=p^2");
    let (mut run, compiler) = super::execute(&source);
    assert!(matches!(
        selected(target(&mut run)),
        Rule::SqrtQuotientSquare(_)
    ));
    let output = compiler.compile_run(&run, "reordered_square").unwrap();
    assert!(output.contains("Litex.sqrtQuotientSquareValue"));
}
