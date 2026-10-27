use crate::prelude::*;

#[test]
fn finite_intersection_replays_both_original_finiteness_proofs() {
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/finite_intersection/statement.lit"
    ));
    compiler.compile_run(&run, "finite_intersection").unwrap();
}

#[test]
fn finite_intersection_one_bound_replays_each_actual_operand() {
    for (source, bridge) in [
        (
            "forall A finite_set,B set:\n    $is_finite_set(intersect(A,B))",
            "finiteSetIntersectFromLeft",
        ),
        (
            "forall A set,B finite_set:\n    $is_finite_set(intersect(A,B))",
            "finiteSetIntersectFromRight",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "one_bound").unwrap();
        assert!(lean.contains(bridge), "{lean}");
    }
    let (run, compiler) =
        super::execute("forall E set,point R:\n    finite_set_size(intersect(E,{point})) $in N");
    compiler.compile_run(&run, "one_bound_size").unwrap();
}

#[test]
fn finite_intersection_one_bound_rejects_missing_or_wrong_side_evidence() {
    for source in [
        "forall A finite_set,B set:\n    $is_finite_set(intersect(A,B))",
        "forall A set,B finite_set:\n    $is_finite_set(intersect(A,B))",
    ] {
        for corruption in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let all = super::forall_proof_mut(&mut run.statement_results[0]);
            let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
            let AtomicFact::IsFiniteSetFact(fact) = &atom.fact else {
                panic!("finite intersection")
            };
            let Obj::SetOperator(SetOperator::Intersect(pair)) = &fact.set else {
                panic!("intersection")
            };
            let (requirements, proofs, wrong) = match &mut atom.searched_proof {
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromLeft(
                        p,
                    ),
                ) => (
                    &mut p.requirement_facts,
                    &mut p.proof_of_requirement_facts,
                    pair.right.as_ref().clone(),
                ),
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromRight(
                        p,
                    ),
                ) => (
                    &mut p.requirement_facts,
                    &mut p.proof_of_requirement_facts,
                    pair.left.as_ref().clone(),
                ),
                _ => panic!("actual one-bound evidence"),
            };
            match corruption {
                0 => requirements.clear(),
                1 => proofs.clear(),
                _ => {
                    let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) = &mut requirements[0]
                    else {
                        panic!("finite operand")
                    };
                    f.set = wrong;
                }
            }
            assert!(compiler.compile_run(&run, "bad_bound").is_err());
        }
    }
}

#[test]
fn finite_intersection_rejects_missing_or_reordered_requirements() {
    for missing in [false, true] {
        let (mut run, compiler) =
            super::execute("forall A, B finite_set:\n    $is_finite_set(intersect(A,B))\n");
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromBoth(p),
        ) = &mut atom.searched_proof
        else {
            panic!("finite intersection strategy")
        };
        if missing {
            p.proof_of_requirement_facts.pop();
        } else {
            p.requirement_facts.swap(0, 1);
            p.proof_of_requirement_facts.swap(0, 1);
        }
        assert!(compiler
            .compile_run(&run, "invalid_finite_intersection")
            .is_err());
    }
}
