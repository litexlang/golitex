use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;

const DIRECT: &str =
    include_str!("../../../lean/examples/finite_summand_nonnegative/statement.lit");
const EQUAL: &str = include_str!("../../../lean/examples/finite_summand_equal_value/statement.lit");

#[test]
fn finite_summand_replays_membership_nonnegativity_and_original_value_equality() {
    for source in [DIRECT, EQUAL] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(
            invocation(&mut run).builtin.as_ref().unwrap().theorem,
            BuiltinTheoremId::FiniteSetSummandLessEqualSum
        );
        let output = compiler.compile_run(&run, "finite_summand").unwrap();
        assert!(output.contains("Litex.finiteSummandLeSumValue"));
        assert!(output.contains("Eq.mp (congrArg"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "finite_summand").unwrap()
        );
    }
}

#[test]
fn finite_summand_requires_exact_ordered_premises_stores_arguments_and_conclusion_wd() {
    for source in [DIRECT, EQUAL] {
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
                _ => p.dom_stores.swap(0, 1),
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("all original stages are required");
        }
    }
}

#[test]
fn finite_summand_preserves_the_exact_universal_nonnegative_callback_contract() {
    for mutation in [
        "domain",
        "capture",
        "empty",
        "guards",
        "zero",
        "direction",
        "callback",
        "member",
        "conclusion",
    ] {
        let (mut run, compiler) = super::execute(DIRECT);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        let extra = p.requirements[0].clone();
        if mutation == "member" {
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[1] else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::R);
        } else if mutation == "conclusion" {
            let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut p.conclusions[0] else {
                panic!()
            };
            std::mem::swap(&mut f.left, &mut f.right);
        } else {
            let Fact::ForallFact(point) = &mut p.requirements[2] else {
                panic!()
            };
            match mutation {
                "domain" => {
                    point.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C))
                }
                "capture" => {
                    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) =
                        &p.arguments[1]
                    else {
                        panic!()
                    };
                    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = sum.func.as_ref() else {
                        panic!()
                    };
                    point.typed_parameters.groups[0].params[0].id = *id;
                }
                "empty" => point.then_facts.clear(),
                "guards" => point.dom_facts.push(extra),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(f)) =
                        &mut point.then_facts[0]
                    else {
                        panic!()
                    };
                    match mutation {
                        "zero" => f.left = Obj::Literal(Literal::Number(Number::new("1".into()))),
                        "direction" => std::mem::swap(&mut f.left, &mut f.right),
                        _ => f.right = Obj::Literal(Literal::Number(Number::new("0".into()))),
                    }
                }
            }
        }
        compiler
            .compile_run(&run, mutation)
            .expect_err("the source nonnegative family and original member must remain unchanged");
    }
}

#[test]
fn finite_summand_cannot_reuse_its_future_conclusion_as_an_original_equality() {
    let (mut run, compiler) = super::execute(EQUAL);
    let p = invocation(&mut run);
    let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let p = super::equality_proof_mut(&mut p.dom_proofs[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut p.searched_proof
    else {
        panic!("original summand equality path")
    };
    assert!(!path.path.is_empty());
    path.path[0].2 = future;
    compiler
        .compile_run(&run, "future")
        .expect_err("the cited equality must precede the builtin conclusion");
}
