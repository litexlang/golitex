use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::AtomicExceptEqualityFactSearchProofByBuiltinStrategy as Strategy;

const SOURCE: &str = r#"# Build closed and half-open integer interval membership from ordered bounds.
forall lower, upper, k Z:
    lower <= k
    k <= upper
    =>:
        k $in closed_range(lower, upper)

forall lower, upper, k Z:
    lower <= k
    k < upper
    =>:
        k $in range(lower, upper)
"#;

#[test]
fn integer_range_strategies_require_all_original_proofs_in_role_order() {
    for statement in 0..2 {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(SOURCE);
            let forall = super::forall_proof_mut(&mut run.statement_results[statement]);
            let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy) =
                &mut atomic.searched_proof
            else {
                panic!("the recorded range strategy");
            };
            let (requirements, proofs) = match strategy {
                Strategy::ClosedRangeMembership(p) => {
                    (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
                }
                Strategy::RangeMembership(p) => {
                    (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
                }
                _ => panic!("the recorded integer-range branch"),
            };
            match mutation {
                0 => {
                    proofs.pop();
                }
                1 => proofs.swap(1, 2),
                _ => {
                    requirements.swap(0, 1);
                    proofs.swap(0, 1);
                }
            }
            assert!(compiler.compile_run(&run, "InvalidIntegerBounds").is_err());
        }
    }
}
