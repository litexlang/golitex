use crate::prelude::*;

const SOURCE: &str =
    "forall a, b, c, d R:\n    a = b\n    c = d\n    =>:\n        (a, c) = (b, d)\n";

fn selected(result: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let forall = super::forall_proof_mut(&mut result.statement_results[0]);
    let equality = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByMatchingOneArgByOne(proof) = &mut equality.searched_proof else {
        panic!("original component congruence");
    };
    &mut proof.corresponding_arg_equal_proofs
}

#[test]
fn tuple_congruence_replays_original_component_equalities() {
    let (mut result, compiler) = super::execute(SOURCE);
    assert_eq!(selected(&mut result).len(), 2);
    let generated = compiler.compile_run(&result, "tuple_congruence").unwrap();
    assert!(generated.contains("congrArg (Litex.FiniteFunction.tupleValue"));
}

#[test]
fn tuple_congruence_rejects_missing_or_reordered_component_proofs() {
    for reorder in [false, true] {
        let (mut result, compiler) = super::execute(SOURCE);
        let children = selected(&mut result);
        if reorder {
            children.swap(0, 1);
        } else {
            children.pop();
        }
        let error = compiler
            .compile_run(&result, "corrupted_components")
            .unwrap_err();
        assert_eq!(
            error.route,
            if reorder {
                "TupleCongruence/ChildSubject"
            } else {
                "TupleCongruence/Children"
            }
        );
    }
}

#[test]
fn tuple_congruence_rejects_unknown_component_citation() {
    let (mut result, compiler) = super::execute(SOURCE);
    let child = super::equality_proof_mut(&mut selected(&mut result)[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(proof),
    ) = &mut child.searched_proof
    else {
        panic!("known equality citation");
    };
    proof.path[0].2 = FactId::new(u64::MAX);
    assert!(compiler.compile_run(&result, "bad_citation").is_err());
}
