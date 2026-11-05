use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;
const SAME: &str = r#"thm checked_finite_sum_pointwise_equality:
    ? forall A finite_set, f,g fn(x A) C:
        forall x A:
            f(x)=g(x)
        =>:
            finite_set_sum(A,f)=finite_set_sum(A,g)
    release thm finite_set_sum_substitution(finite_set_sum(A,f),finite_set_sum(A,g))
"#;
const EQUAL: &str = r#"thm checked_finite_sum_pointwise_equal_sets:
    ? forall A,B finite_set, f fn(x A) C, g fn(x B) C:
        A=B
        forall x A:
            f(x)=g(x)
        =>:
            finite_set_sum(A,f)=finite_set_sum(B,g)
    release thm finite_set_sum_substitution(finite_set_sum(A,f),finite_set_sum(B,g))
"#;
const ORDER: &str = r#"thm checked_finite_sum_pointwise_order:
    ? forall A finite_set, f,g fn(x A) R:
        forall x A:
            f(x)<=g(x)
        =>:
            finite_set_sum(A,f)<=finite_set_sum(A,g)
    release thm finite_set_sum_le_from_pointwise(finite_set_sum(A,f),finite_set_sum(A,g))
"#;
const EQUAL_ORDER: &str = r#"thm checked_finite_sum_equal_sets_order:
    ? forall A,B finite_set, f fn(x A) R, g fn(x B) R:
        A=B
        forall x A:
            f(x)<=g(x)
        =>:
            finite_set_sum(A,f)<=finite_set_sum(B,g)
    release thm finite_set_sum_le_from_pointwise(finite_set_sum(A,f),finite_set_sum(B,g))
"#;
#[test]
fn finite_sum_substitution_replays_original_named_callback_pointwise_contracts() {
    for (source, ordered) in [
        (SAME, false),
        (EQUAL, false),
        (ORDER, true),
        (EQUAL_ORDER, true),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(
            invocation(&mut run).builtin.as_ref().unwrap().theorem,
            if ordered {
                BuiltinTheoremId::FiniteSetSumLessEqualFromPointwise
            } else {
                BuiltinTheoremId::FiniteSetSumSubstitution
            }
        );
        let output = compiler
            .compile_run(&run, "finite_sum_pointwise")
            .unwrap_or_else(|e| panic!("{e}"));
        assert!(output.contains(if ordered {
            "Litex.finiteSumPointwiseLeValue"
        } else {
            "Litex.finiteAggregatePointwiseValue false"
        }));
        assert_eq!(
            output,
            compiler.compile_run(&run, "finite_sum_pointwise").unwrap()
        );
    }
}
#[test]
fn finite_sum_substitution_preserves_original_requirement_order_stores_wd_and_arguments() {
    for source in [SAME, EQUAL, ORDER, EQUAL_ORDER] {
        for mutation in [
            "proof",
            "store",
            "wd",
            "swapped",
            "arguments",
            "publication",
        ] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match mutation {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                "swapped" => p.dom_proofs.swap(0, 1),
                "arguments" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                _ => {
                    p.dom_stores.swap(0, 1);
                }
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("exact original premise, store, conclusion WD and argument stages");
        }
    }
}
#[test]
fn finite_sum_substitution_cannot_change_pointwise_domain_binder_body_or_callbacks() {
    for mutation in ["domain", "capture", "empty", "guards", "body"] {
        let (mut run, compiler) = super::execute(SAME);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let extra = p.requirements[0].clone();
        let Fact::ForallFact(point) = &mut p.requirements[1] else {
            panic!();
        };
        match mutation {
            "domain" => {
                point.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            "capture" => {
                let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = &p.arguments[0]
                else {
                    panic!();
                };
                let Obj::Identifier(IdentifierObj::Plain { id, .. }) = sum.func.as_ref() else {
                    panic!();
                };
                point.typed_parameters.groups[0].params[0].id = *id;
            }
            "empty" => point.then_facts.clear(),
            "guards" => point.dom_facts.push(extra),
            _ => {
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                    &mut point.then_facts[0]
                else {
                    panic!();
                };
                eq.right = Obj::Literal(Literal::Number(Number::new("0".into())));
            }
        }
        compiler.compile_run(&run, mutation).expect_err(
            "retain the exact uncaptured universal member binder and callback equality",
        );
    }
}
#[test]
fn finite_sum_substitution_cannot_use_a_future_set_equality() {
    let (mut run, compiler) = super::execute(EQUAL);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let p = super::equality_proof_mut(&mut p.dom_proofs[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut p.searched_proof
    else {
        panic!("original set-equality path");
    };
    assert!(!path.path.is_empty());
    path.path[0].2 = future;
    compiler
        .compile_run(&run, "future")
        .expect_err("the original set-equality citation must precede the builtin conclusion");
}

#[test]
fn finite_sum_order_keeps_the_original_weak_pointwise_direction_and_relation() {
    for source in [ORDER, EQUAL_ORDER] {
        for mutation in ["direction", "strict", "conclusion"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run).builtin.as_mut().unwrap();
            if mutation == "conclusion" {
                let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut p.conclusions[0] else {
                    panic!();
                };
                std::mem::swap(&mut f.left, &mut f.right);
            } else {
                let Fact::ForallFact(point) = &mut p.requirements[1] else {
                    panic!();
                };
                let ExistOrAndChainAtomicFact::AtomicFact(body) = &mut point.then_facts[0] else {
                    panic!();
                };
                let AtomicFact::LessEqualFact(f) = body else {
                    panic!();
                };
                if mutation == "direction" {
                    std::mem::swap(&mut f.left, &mut f.right);
                } else {
                    *body = AtomicFact::LessFact(LessFact {
                        fact_id: f.fact_id,
                        left: f.left.clone(),
                        right: f.right.clone(),
                        line_file: f.line_file.clone(),
                    });
                }
            }
            compiler.compile_run(&run, mutation).expect_err(
                "replay the original weak pointwise implication and ordered sum endpoints",
            );
        }
    }
}
