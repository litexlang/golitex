use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;

#[test]
fn aggregate_output_replays_refinements_positivity_empty_values_and_nested_wd() {
    for source in [
        include_str!("../../../lean/examples/positive_range_output/statement.lit"),
        include_str!("../../../lean/examples/positive_finite_output/statement.lit"),
        include_str!("../../../lean/examples/refined_aggregate_output/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "aggregate_output")
            .expect(source);
    }
}

#[test]
fn aggregate_output_rejects_retyped_return_and_closure_certificates() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute("forall f fn(k Z) R+:\n    sum(1,3,f) $in R+\n");
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::AggregateScalarCodomain(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!("selected aggregate closure")
        };
        match change {
            0 => p.codomain = StandardSet::R,
            1 => p.iterand_return_set = Obj::StandardSet(StandardSet::NPos),
            _ => {
                p.iterand_return_set = Obj::StandardSet(StandardSet::R);
                p.codomain = StandardSet::R;
            }
        }
        compiler
            .compile_run(&run, "changed_aggregate_output")
            .expect_err("the exact selected signature and closure must agree");
    }
}

#[test]
fn aggregate_output_does_not_treat_a_potentially_empty_finite_sum_as_positive() {
    let (mut run, compiler) = super::execute(
        "forall S finite_set, f fn(k Z) R+:\n    S $subset Z\n    =>:\n        finite_set_sum(S,f) $in R\n",
    );
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
            InFactSearchProofByBuiltinRule::AggregateScalarCodomain(p),
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("selected finite sum closure")
    };
    p.codomain = StandardSet::RPos;
    compiler
        .compile_run(&run, "false_positive_empty_sum")
        .expect_err("zero must remain allowed for finite sums");
}
