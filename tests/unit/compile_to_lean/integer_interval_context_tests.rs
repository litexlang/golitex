use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule;

fn requirements(result: &mut VerifyFactResult) -> &mut Vec<VerifyFactResult> {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(
            SubsetFactSearchProofByBuiltinRule::IntegerRangeSubsetNumericCarrier(p),
        ),
    ) = &mut super::atomic_proof_mut(result).searched_proof
    else {
        panic!("recorded integer interval subset rule")
    };
    &mut p.proof_of_requirement_facts
}

#[test]
fn integer_interval_contexts_replay_numeric_subsets_and_captured_endpoints() {
    for source in [
        include_str!("../../../lean/examples/integer_interval_subsets/statement.lit"),
        include_str!("../../../lean/examples/captured_integer_interval/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "integer_intervals")
            .expect(source);
        assert_eq!(
            lean,
            compiler.compile_run(&run, "integer_intervals").unwrap()
        );
    }
}

#[test]
fn integer_interval_subset_requires_the_original_start_membership() {
    for carrier in ["N", "N+"] {
        for interval in ["range", "closed_range"] {
            for change in 0..4 {
                let source =
                    format!("forall a {carrier}, b Z:\n    {interval}(a,b) $subset {carrier}\n");
                let (mut run, compiler) = super::execute(&source);
                let all = super::forall_proof_mut(&mut run.statement_results[0]);
                let proof = &mut all.proved_then_facts[0].verify_result;
                let req = requirements(proof);
                assert_eq!(req.len(), 1);
                match change {
                    0 => req.clear(),
                    1 => {
                        let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(&mut req[0]).fact
                        else {
                            panic!()
                        };
                        f.element = super::number_object("0");
                    }
                    2 => {
                        let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(&mut req[0]).fact
                        else {
                            panic!()
                        };
                        f.set = Obj::StandardSet(StandardSet::Z);
                    }
                    _ => {
                        let AtomicFact::SubsetFact(f) = &mut super::atomic_proof_mut(proof).fact
                        else {
                            panic!()
                        };
                        f.right = Obj::StandardSet(StandardSet::Z);
                    }
                }
                compiler
                    .compile_run(&run, "invalid_integer_interval")
                    .expect_err("missing, foreign, retyped or extra evidence");
            }
        }
    }
}
