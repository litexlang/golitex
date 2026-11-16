use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::matrix_entry_normalization_proof::*;
use crate::prelude::*;

const SOURCE: &str = include_str!(
    "../../../examples/proof_nodes/equal/by_builtin_strategy/matrix_structural_equality.lit"
);
const TRACER: &str = "forall m,n N,A matrix(C,m,n):\n    transpose(transpose(A,m,n),n,m)=A";

fn structural(statement: &mut ExecStmtResult) -> &mut MatrixStructuralEqualityProof {
    let all = super::forall_proof_mut(statement);
    let proof = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::MatrixStructuralEquality(proof),
    ) = &mut proof.searched_proof
    else {
        panic!("structural strategy")
    };
    proof
}

#[test]
fn native_matrix_structural_compiler_thirteen_independent_goals() {
    let mut count = 0;
    for source in SOURCE.split("\n\n").filter(|s| s.starts_with("forall")) {
        let (run, compiler) = super::execute(source);
        let generated = compiler.compile_run(&run, "matrix_structural").unwrap();
        assert!(generated.contains("Litex.functionExtOnDomain"));
        assert!(!generated.contains("sorry"));
        count += 1;
    }
    assert_eq!(count, 13);
}

#[test]
fn native_matrix_structural_compiler_rejects_corrupted_evidence() {
    for change in [
        "domain",
        "binder",
        "pointwise",
        "normal_value",
        "native_body",
        "scalar",
    ] {
        let (mut run, compiler) = super::execute(TRACER);
        let p = structural(&mut run.statement_results[0]);
        if change == "domain" {
            p.domain_match.target.ret_set = Box::new(Obj::StandardSet(StandardSet::Z));
        } else {
            let VerifyFactResult::ForallFact(all) = &mut p.pointwise else {
                panic!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(all)) =
                all.as_mut()
            else {
                panic!()
            };
            if change == "binder" {
                all.fact.typed_parameters.groups.swap(0, 1);
            } else {
                let entry = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
                if change == "pointwise" {
                    entry.fact.right = entry.fact.left.clone()
                }
                let EqualFactSearchedProof::ByBuiltinStrategy(
                    EqualitySearchProofByBuiltinStrategy::MatrixEntryReduction(p),
                ) = &mut entry.searched_proof
                else {
                    panic!()
                };
                match change {
                    "normal_value" => p.left.value = p.left.source_wd.obj().clone(),
                    "native_body" => {
                        let MatrixEntryNormalizationStep::NativeCall(call) = &mut p.left.step
                        else {
                            panic!()
                        };
                        call.body = p.right.value.clone();
                    }
                    "scalar" => {
                        let scalar = super::equality_proof_mut(&mut p.scalar_equality);
                        scalar.fact.left = p.left.source_wd.obj().clone();
                    }
                    _ => {}
                }
            }
        }
        assert!(compiler.compile_run(&run, change).is_err(), "{change}");
    }
}
