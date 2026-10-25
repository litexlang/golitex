use crate::prelude::*;

const CASES: &[(&str, &str)] = &[
    ("intersect(A, B) = intersect(B, A)", "intersectComm"),
    ("union(A, B) = union(B, A)", "unionComm"),
    ("intersect(A, A) = A", "intersectIdem"),
    ("union(A, A) = A", "unionIdem"),
    ("intersect(A, {}) = {}", "intersectEmptyRight"),
    ("intersect({}, A) = {}", "intersectEmptyLeft"),
    ("union(A, {}) = A", "unionEmptyRight"),
    ("union({}, A) = A", "unionEmptyLeft"),
    (
        "intersect(intersect(A, B), D) = intersect(A, intersect(B, D))",
        "intersectAssoc",
    ),
    (
        "union(union(A, B), D) = union(A, union(B, D))",
        "unionAssoc",
    ),
    (
        "intersect(A, union(B, D)) = union(intersect(A, B), intersect(A, D))",
        "intersectUnionDistrib",
    ),
];

#[test]
fn set_identities_replay_selected_rules_in_both_directions() {
    for &(statement, law) in CASES {
        let (left, right) = statement.split_once(" = ").unwrap();
        for (a, b) in [(left, right), (right, left)] {
            let source = format!("forall A, B, D set:\n    {a} = {b}\n");
            let (run, compiler) = super::execute(&source);
            let lean = compiler.compile_run(&run, "set_identity").unwrap();
            assert!(lean.contains(&format!("Litex.{law} ")), "{source}");
            assert_eq!(lean, compiler.compile_run(&run, "set_identity").unwrap());
        }
    }
}

#[test]
fn set_identities_reject_changed_endpoints_for_each_rule() {
    for &(statement, _) in CASES {
        let source = format!("forall A, B, D set:\n    {statement}\n");
        let (mut run, compiler) = super::execute(&source);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
        p.fact.right = super::number_object("17");
        assert!(compiler.compile_run(&run, "changed_set_endpoint").is_err());
    }
}

#[test]
fn set_identities_do_not_substitute_another_rule() {
    let (mut run, compiler) =
        super::execute("forall A, B set:\n    intersect(A, B) = intersect(B, A)\n");
    let (mut other, _) = super::execute("forall A set:\n    intersect(A, A) = A\n");
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
    let q = super::forall_proof_mut(&mut other.statement_results[0]);
    let q = super::equality_proof_mut(&mut q.proved_then_facts[0].verify_result);
    std::mem::swap(&mut p.searched_proof, &mut q.searched_proof);
    assert!(compiler
        .compile_run(&run, "wrong_selected_set_rule")
        .is_err());
}

#[test]
fn intersection_absorption_replays_both_operands_and_orientations() {
    for expression in ["intersect(A, B)", "intersect(B, A)"] {
        for (left, right) in [(expression, "A"), ("A", expression)] {
            let source =
                format!("forall A, B set:\n    A $subset B\n    =>:\n        {left} = {right}\n");
            let (run, compiler) = super::execute(&source);
            let lean = compiler.compile_run(&run, "subset_absorption").unwrap();
            let side = if expression == "intersect(A, B)" {
                "Left"
            } else {
                "Right"
            };
            assert!(lean.contains(&format!("Litex.intersectOfSubset{side} ")));
        }
    }
}

#[test]
fn intersection_absorption_rejects_missing_extra_or_changed_premise() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(
            "forall A, B set:\n    A $subset B\n    =>:\n        intersect(A, B) = A\n",
        );
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::IntersectFromSubset(p),
        ) = &mut p.searched_proof
        else {
            panic!("selected absorption")
        };
        match mutation {
            0 => p.proof_of_requirement_facts.clear(),
            1 => {
                let (mut extra, _) = super::execute(
                    "forall X, Y set:\n    X $subset Y\n    =>:\n        intersect(X, Y) = X\n",
                );
                let q = super::forall_proof_mut(&mut extra.statement_results[0]);
                let q = super::equality_proof_mut(&mut q.proved_then_facts[0].verify_result);
                let EqualFactSearchedProof::ByBuiltinRule(
                    EqualitySearchProofByBuiltinRule::IntersectFromSubset(q),
                ) = &mut q.searched_proof
                else {
                    panic!()
                };
                p.proof_of_requirement_facts
                    .push(q.proof_of_requirement_facts.pop().unwrap());
            }
            2 | 3 => {
                let p = super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]);
                let AtomicFact::SubsetFact(f) = &mut p.fact else {
                    panic!()
                };
                if mutation == 2 {
                    std::mem::swap(&mut f.left, &mut f.right);
                } else {
                    f.right = super::number_object("17");
                }
            }
            _ => unreachable!(),
        }
        assert!(compiler.compile_run(&run, "bad_subset_child").is_err());
    }
}

#[test]
fn intersection_absorption_rejects_future_citation() {
    let (mut run, compiler) =
        super::execute("forall A, B set:\n    A $subset B\n    =>:\n        intersect(A, B) = A\n");
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let future = p.proved_then_facts[0].store_and_infer.primary_fact_id();
    let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::IntersectFromSubset(p),
    ) = &mut p.searched_proof
    else {
        panic!()
    };
    let p = super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &mut p.searched_proof else {
        panic!()
    };
    p.cite_fact_id = future;
    assert!(compiler
        .compile_run(&run, "future_subset_citation")
        .is_err());
}
