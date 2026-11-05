use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_finite_set::{IsFiniteSetFactSearchProofByBuiltinRule,FunctionRangeOfFiniteDomainProof};
const SOURCES: [&str; 3] = [
    r#"# A function on a finite carrier has finite range.
thm function_range_finite:
    ? forall A,B set,f fn(x A) B:
        $is_finite_set(A)
        =>:
            $is_finite_set(fn_range(f))
"#,
    r#"# A guarded unary function on a finite carrier still has finite range.
thm function_range_finite_guarded:
    ? forall A,B set,c A,f fn(x A:x!=c) B:
        $is_finite_set(A)
        =>:
            $is_finite_set(fn_range(f))
"#,
    r#"# The image of a finite positive-indexed prefix is finite.
thm function_range_finite_prefix_explicit:
    ? forall n N+,f fn(k closed_range(1,n)) R:
        $is_finite_set(fn_range(f))
    $is_finite_set(closed_range(1,n))
"#,
];
fn body(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_def_thm_stmt::ExecDefThmForallProof {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!()
    };
    p
}
fn selected(
    proof: &mut VerifyAtomicExceptEqualityFactSuccess,
) -> &mut FunctionRangeOfFiniteDomainProof {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(
            IsFiniteSetFactSearchProofByBuiltinRule::FunctionRangeOfFiniteDomain(p),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("original finite-domain selection")
    };
    p
}
#[test]
fn finite_function_range_replays_generic_guarded_and_prefix_domains() {
    for source in SOURCES {
        let (mut run, compiler) = super::execute(source);
        selected(super::atomic_proof_mut(
            &mut body(&mut run).conclusion_proofs[0],
        ));
        let lean = compiler.compile_run(&run, "finite_range").unwrap();
        assert!(lean.contains("Litex.fnRangeFiniteOfFiniteCover "));
        assert_eq!(lean, compiler.compile_run(&run, "finite_range").unwrap());
    }
}
#[test]
fn finite_function_range_rejects_swapped_children_or_changed_subjects() {
    for source in SOURCES {
        for change in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let p = selected(super::atomic_proof_mut(
                &mut body(&mut run).conclusion_proofs[0],
            ));
            match change {
                0 => std::mem::swap(&mut p.domain_finite, &mut p.function_membership),
                1 => {
                    let AtomicFact::InFact(f) =
                        &mut super::atomic_proof_mut(&mut p.function_membership).fact
                    else {
                        panic!()
                    };
                    f.element = super::number_object("17");
                }
                2 => {
                    let AtomicFact::IsFiniteSetFact(f) =
                        &mut super::atomic_proof_mut(&mut p.domain_finite).fact
                    else {
                        panic!()
                    };
                    f.set = super::number_object("17");
                }
                _ => unreachable!(),
            }
            assert!(compiler.compile_run(&run, "invalid_finite_range").is_err());
        }
    }
}
