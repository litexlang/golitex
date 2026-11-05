use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{less::LessFactSearchProofByBuiltinRule as Lt,less_equal::LessEqualFactSearchProofByBuiltinRule as Le};
use crate::prelude::*;
const CASES: [(&str, &str); 4] = [
    (
        r#"forall x R:
    1<x
    =>:
        0<ln(x)
"#,
        "naturalLogPositiveAboveOneValue",
    ),
    (
        r#"forall x R+:
    x<1
    =>:
        ln(x)<0
"#,
        "naturalLogNegativeBelowOneValue",
    ),
    (
        r#"forall a,b R:
    0<a
    b<0
    =>:
        a*b<0
"#,
        "positiveNegativeProductValue",
    ),
    (
        r#"forall a,b R:
    0<=a
    b<0
    =>:
        a*b<=0
"#,
        "nonnegativeNegativeProductValue",
    ),
];
fn target(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result)
}
fn selected(proof: &VerifyAtomicExceptEqualityFactSuccess, index: usize) {
    use AtomicExceptEqualityFactSearchProofByBuiltinRule as Rule;
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &proof.searched_proof else {
        panic!("selected sign builtin")
    };
    assert!(matches!(
        (rule, index),
        (Rule::LessFact(Lt::LnPositiveAboveOne(_)), 0)
            | (Rule::LessFact(Lt::LnNegativeBelowOne(_)), 1)
            | (Rule::LessFact(Lt::ProductPositiveNegativeStrict(_)), 2)
            | (
                Rule::LessEqualFact(Le::ProductNonnegativeNegativeWeak(_)),
                3
            )
    ));
}
fn log_guard(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> &mut AtomicExceptEqualityFactKnownProof {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(rule),
    ) = &mut proof.searched_proof
    else {
        panic!()
    };
    match rule {
        Lt::LnPositiveAboveOne(p) => &mut p.above_one,
        Lt::LnNegativeBelowOne(p) => &mut p.below_one,
        _ => panic!(),
    }
}
fn product_children(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> (&mut VerifyFactResult, &mut VerifyFactResult) {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &mut proof.searched_proof
    else {
        panic!()
    };
    match rule {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
            Lt::ProductPositiveNegativeStrict(p),
        ) => (&mut p.positive_factor, &mut p.negative_factor),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
            Le::ProductNonnegativeNegativeWeak(p),
        ) => (&mut p.nonnegative_factor, &mut p.negative_factor),
        _ => panic!(),
    }
}
#[test]
fn log_product_signs_replay_four_selected_rules_and_both_product_factor_orders() {
    for (index, (source, law)) in CASES.into_iter().enumerate() {
        for source in [
            source,
            if index >= 2 {
                if index == 2 {
                    r#"forall a,b R:
    0<a
    b<0
    =>:
        b*a<0
"#
                } else {
                    r#"forall a,b R:
    0<=a
    b<0
    =>:
        b*a<=0
"#
                }
            } else {
                source
            },
        ] {
            let (mut run, compiler) = super::execute(source);
            selected(target(&mut run), index);
            let output = compiler
                .compile_run(&run, "log_product_sign")
                .unwrap_or_else(|e| panic!("{source}: {e}"));
            assert!(output.contains(&format!("Litex.{law}")));
            assert_eq!(
                output,
                compiler.compile_run(&run, "log_product_sign").unwrap()
            );
        }
    }
}
#[test]
fn log_signs_preserve_exact_one_endpoint_direction_strictness_and_prior_citation() {
    for (source, _) in &CASES[..2] {
        for change in ["future", "endpoint", "strictness"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            let future = p.fact.fact_id();
            let guard = log_guard(p);
            if change == "future" {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    guard.searched_proof.as_mut()
                else {
                    panic!()
                };
                cite.cite_fact_id = future;
            } else {
                let AtomicFact::LessFact(f) = &guard.fact else {
                    panic!()
                };
                guard.fact = if change == "strictness" {
                    AtomicFact::LessEqualFact(LessEqualFact {
                        fact_id: f.fact_id,
                        left: f.left.clone(),
                        right: f.right.clone(),
                        line_file: f.line_file.clone(),
                    })
                } else {
                    let mut f = f.clone();
                    if source.contains("1<x") {
                        f.left = Obj::Literal(Literal::Number(Number::new("2".into())))
                    } else {
                        f.right = Obj::Literal(Literal::Number(Number::new("2".into())))
                    }
                    AtomicFact::LessFact(f)
                };
            }
            compiler
                .compile_run(&run, change)
                .expect_err("the original strict comparison with one must be retained");
        }
    }
}
#[test]
fn product_signs_preserve_both_original_factor_results_order_and_scope() {
    for (source, _) in &CASES[2..] {
        for change in ["swapped", "future", "strictness"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            let future = p.fact.fact_id();
            let (positive, negative) = product_children(p);
            if change == "swapped" {
                std::mem::swap(positive, negative)
            } else {
                let child = super::atomic_proof_mut(negative);
                if change == "future" {
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut child.searched_proof
                    else {
                        panic!()
                    };
                    cite.cite_fact_id = future;
                } else {
                    let AtomicFact::LessFact(f) = &child.fact else {
                        panic!()
                    };
                    child.fact = AtomicFact::LessEqualFact(LessEqualFact {
                        fact_id: f.fact_id,
                        left: f.left.clone(),
                        right: f.right.clone(),
                        line_file: f.line_file.clone(),
                    });
                }
            }
            compiler.compile_run(&run, change).expect_err(
                "use the exact original positive/nonnegative and strictly negative factor proofs",
            );
        }
    }
}
#[test]
fn log_and_product_signs_require_original_target_wd_and_zero_endpoint() {
    for (source, _) in CASES {
        for change in ["wd", "zero"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            if change == "wd" {
                p.well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter
                    .swap(0, 1)
            } else {
                let (left, right) = match &mut p.fact {
                    AtomicFact::LessFact(f) => (&mut f.left, &mut f.right),
                    AtomicFact::LessEqualFact(f) => (&mut f.left, &mut f.right),
                    _ => panic!(),
                };
                let endpoint = if source.contains("0<ln") { left } else { right };
                *endpoint = Obj::Literal(Literal::Number(Number::new("1".into())));
            }
            compiler
                .compile_run(&run, change)
                .expect_err("retain exact source constructors and the zero comparison endpoint");
        }
    }
}
