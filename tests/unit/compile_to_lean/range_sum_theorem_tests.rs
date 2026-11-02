use super::dense_order_theorem_tests::invocation;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::prelude::*;

const SAME: &str = include_str!("../../../lean/examples/range_sum_pointwise_order/statement.lit");
const EQUAL: &str =
    include_str!("../../../lean/examples/range_sum_equal_endpoints_order/statement.lit");

#[test]
fn range_sum_replays_original_endpoint_equalities_and_guarded_integer_pointwise_bound() {
    for source in [SAME, EQUAL] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(
            invocation(&mut run).builtin.as_ref().unwrap().theorem,
            BuiltinTheoremId::SumLessEqualFromPointwise
        );
        let output = compiler.compile_run(&run, "range_sum").unwrap();
        assert!(output.contains("Litex.rangeSumPointwiseLeValue"));
        assert!(output.contains("Litex.integerRangeBoundsValue"));
        assert_eq!(output, compiler.compile_run(&run, "range_sum").unwrap());
    }
}

#[test]
fn range_sum_preserves_original_stage_order_stores_arguments_and_wd() {
    for source in [SAME, EQUAL] {
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
                "swapped" => p.dom_proofs.swap(0, 2),
                "arguments" => p.builtin.as_mut().unwrap().arguments.swap(0, 1),
                _ => p.dom_stores.swap(0, 2),
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("retain original endpoint, universal, store and conclusion WD stages");
        }
    }
}

#[test]
fn range_sum_preserves_integer_binder_bounds_and_pointwise_direction() {
    for mutation in [
        "domain",
        "capture",
        "guards",
        "swapped",
        "bounds",
        "body",
        "direction",
        "endpoint",
    ] {
        let (mut run, compiler) = super::execute(SAME);
        let p = invocation(&mut run).builtin.as_mut().unwrap();
        if mutation == "endpoint" {
            let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut p.requirements[0] else {
                panic!()
            };
            f.left = Obj::Literal(Literal::Number(Number::new("0".into())));
        } else {
            let Fact::ForallFact(point) = &mut p.requirements[2] else {
                panic!()
            };
            match mutation {
                "domain" => {
                    point.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                "capture" => {
                    let Obj::IteratedOperator(IteratedOperator::Sum(sum)) = &p.arguments[0] else {
                        panic!()
                    };
                    let Obj::Identifier(IdentifierObj::Plain { id, .. }) = sum.func.as_ref() else {
                        panic!()
                    };
                    point.typed_parameters.groups[0].params[0].id = *id;
                }
                "guards" => point.dom_facts.clear(),
                "swapped" => point.dom_facts.swap(0, 1),
                "bounds" => {
                    let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut point.dom_facts[0]
                    else {
                        panic!()
                    };
                    std::mem::swap(&mut f.left, &mut f.right);
                }
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(f)) =
                        &mut point.then_facts[0]
                    else {
                        panic!()
                    };
                    if mutation == "body" {
                        f.right = Obj::Literal(Literal::Number(Number::new("0".into())));
                    } else {
                        std::mem::swap(&mut f.left, &mut f.right);
                    }
                }
            }
        }
        compiler
            .compile_run(&run, mutation)
            .expect_err("do not alter the source integer interval or selected weak comparison");
    }
}

#[test]
fn range_sum_endpoint_equalities_cannot_cite_the_future_conclusion() {
    for index in [0, 1] {
        let (mut run, compiler) = super::execute(EQUAL);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let p = super::equality_proof_mut(&mut p.dom_proofs[index]);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut p.searched_proof
        else {
            panic!("original endpoint equality path")
        };
        assert!(!path.path.is_empty());
        path.path[0].2 = future;
        compiler
            .compile_run(&run, "future")
            .expect_err("each original endpoint equality must already be visible");
    }
}
