use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::VerifyAtomicExceptEqualityFactSuccess;
use crate::prelude::*;
const CASES: [&str; 2] = [
    include_str!("../../../lean/examples/finite_set_equality_transport/statement.lit"),
    include_str!("../../../lean/examples/finite_set_equality_chain_transport/statement.lit"),
];
fn target(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    super::atomic_proof_mut(&mut p.proved_then_facts[0].verify_result)
}
#[test]
fn known_finiteness_replays_original_set_equality_and_chained_transport() {
    for source in CASES {
        let (mut run, compiler) = super::execute(source);
        let p = target(&mut run);
        assert!(matches!(p.fact, AtomicFact::IsFiniteSetFact(_)));
        assert!(matches!(
            &p.searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
        ));
        let output = compiler
            .compile_run(&run, "known_finiteness_transport")
            .unwrap();
        assert!(output.contains("Eq.mp"));
        assert!(output.contains("Litex.memberSet"));
        assert_eq!(
            output,
            compiler
                .compile_run(&run, "known_finiteness_transport")
                .unwrap()
        );
    }
}
#[test]
fn known_finiteness_requires_original_visible_citation_and_ordered_equality_winner() {
    for source in CASES {
        for mutation in ["arity", "citation", "equality", "endpoint"] {
            let (mut run, compiler) = super::execute(source);
            let p = target(&mut run);
            let future = p.fact.fact_id();
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                &mut p.searched_proof
            else {
                panic!();
            };
            if mutation == "arity" {
                known
                    .why_parameters_of_known_fact_are_equal_to_givens
                    .clear();
            } else if mutation == "citation" {
                known.cite_fact_id = future;
            } else {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = &mut known.why_parameters_of_known_fact_are_equal_to_givens[0]
                else {
                    panic!("original set-equality path");
                };
                assert!(!path.path.is_empty());
                if mutation == "equality" {
                    path.path[0].2 = future;
                } else {
                    path.path[0].0 = Obj::Literal(Literal::Number(Number::new("0".into())));
                }
            }
            compiler
                .compile_run(&run, mutation)
                .expect_err("exact prior finite-set citation and original set-equality path");
        }
    }
}
