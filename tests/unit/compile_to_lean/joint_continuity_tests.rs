use crate::execute::execute_fact_stmt::multivariable::continuity::ContinuousExpressionConstructorProof as C;
use crate::execute::execute_fact_stmt::multivariable::strategy::{
    ContinuousMultivariableProof, MultivariableStrategyProof,
};
use crate::prelude::*;

const NORM: &str = "have fn norm(p finite_seq(R,2)) R = sqrt(p(1)^2+p(2)^2)\n$is_multi_continuous_at(norm,(0,0),2)\n$has_multi_limit_at(norm,(0,0),2,0)";
fn number(n: i64) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.to_string())))
}
fn proof(result: &mut ExecStmtResult) -> &mut ContinuousMultivariableProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(f)) = result else {
        panic!("fact");
    };
    let p = super::atomic_proof_mut(&mut f.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MultivariableAnalysis(
            MultivariableStrategyProof::ContinuousExpression(p),
        ),
    ) = &mut p.searched_proof
    else {
        panic!("selected continuity tree");
    };
    p
}
#[test]
fn joint_continuity_compiles_the_selected_nonderivative_tree() {
    let (run, compiler) = super::execute(NORM);
    let output = compiler.compile_run(&run, "joint_norm").unwrap();
    assert!(output.contains("semanticEuclideanContinuousSqrt"));
    assert!(output.contains("semanticEuclideanContinuousCoordinate"));
    assert!(output.contains("scalarContinuityToMultivariableLimit"));
    assert!(!output.contains("semanticDerivative"));
    assert_eq!(output, compiler.compile_run(&run, "joint_norm").unwrap());
}
#[test]
fn joint_continuity_rejects_changed_tree_domains_and_values() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(NORM);
        let p = proof(&mut run.statement_results[1]);
        match mutation {
            0 => p.coordinates[0].expression.constructor = C::Constant,
            1 => p.coordinates[0].expression.value = number(7),
            2 => p.coordinates[0].expression.value_reduction.source = number(7),
            3 => p.body.equal_to = Box::new(number(7)),
            4 => p.coordinates[0].row = 2,
            5 => {
                let C::Elementary { domain, .. } = &mut p.coordinates[0].expression.constructor
                else {
                    panic!()
                };
                let AtomicFact::LessEqualFact(f) = &mut super::atomic_proof_mut(domain).fact else {
                    panic!()
                };
                f.left = number(1);
            }
            6 | 7 => {
                let C::Elementary { argument, .. } = &mut p.coordinates[0].expression.constructor
                else {
                    panic!()
                };
                let C::Add { left, .. } = &mut argument.constructor else {
                    panic!()
                };
                let C::NaturalPower {
                    base,
                    exponent_natural,
                } = &mut left.constructor
                else {
                    panic!()
                };
                if mutation == 6 {
                    let C::Coordinate { index, .. } = &mut base.constructor else {
                        panic!()
                    };
                    *index = number(3);
                } else {
                    let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(exponent_natural).fact
                    else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::R);
                }
            }
            _ => unreachable!(),
        }
        compiler.compile_run(&run, "changed_joint_norm").expect_err(
            "the exact tree, source body, point values, dimensions and domains are required",
        );
    }
}
#[test]
fn joint_limit_rejects_changed_target_and_conclusion() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(NORM);
        let p = proof(&mut run.statement_results[2]);
        match mutation {
            0 => p.conclusion_equalities.clear(),
            1 => p.conclusion_equalities[0].target_reduction.source = number(1),
            _ => {
                let eq = super::equality_proof_mut(&mut p.conclusion_equalities[0].equality);
                eq.fact.right = number(1);
            }
        }
        compiler
            .compile_run(&run, "changed_joint_limit")
            .expect_err("the limit must consume the recorded target reduction and equality");
    }
}
