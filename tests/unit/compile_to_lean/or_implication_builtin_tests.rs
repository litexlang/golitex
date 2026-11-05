use super::or_order_builtin_tests::target;
use crate::execute::execute_fact_stmt::verify_or_fact::OrBuiltinClassicalImplication;
use crate::prelude::*;
const LEFT: &str = r#"# Unequal real values or equality after a common shift form a classical implication disjunction.
thm checked_classical_implication_shift:
    ? forall a,b R:
        a!=b or a+1=b+1
    a!=b or a+1=b+1
"#;
const RIGHT: &str = r#"# A shifted equality or commuted disequality retains its original local implication proof.
thm checked_classical_implication_shift_swapped:
    ? forall a,b R:
        a+1=b+1 or b!=a
    a+1=b+1 or b!=a
"#;
const SCOPE:&str="thm checked_classical_implication_scope_candidate:\n    ? forall a,b R:\n        a=b\n        =>:\n            a=b\n    a!=b or a+1=b+1\n    a=b\n";
fn selected(run: &mut RunLitexCodeResult) -> &mut OrBuiltinClassicalImplication {
    let OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::ClassicalImplication(p)) =
        &mut target(run).searched_proof
    else {
        panic!("original local implication route")
    };
    p
}
#[test]
fn classical_implication_replays_original_private_assumption_and_conclusion() {
    for source in [LEFT, RIGHT, SCOPE] {
        let (mut run, compiler) = super::execute(source);
        let id = selected(&mut run).assumed_premise.fact_id();
        let output = compiler.compile_run(&run, "implication").unwrap();
        assert!(output.contains("Litex.classicalImplicationDisjunction"));
        assert!(output.contains(&format!("h_{}", id.value())));
        assert_eq!(output, compiler.compile_run(&run, "implication").unwrap());
    }
}
#[test]
fn classical_implication_preserves_branch_indices_assumption_store_and_goal() {
    for source in [LEFT, RIGHT] {
        for mutation in [
            "index",
            "same_branch",
            "assumption",
            "store",
            "conclusion",
            "formation",
        ] {
            let (mut run, compiler) = super::execute(source);
            let future = target(&mut run).fact.fact_id;
            let p = selected(&mut run);
            match mutation {
                "index" => p.assumed_from_branch_index = 2,
                "same_branch" => p.conclusion_branch_index = p.assumed_from_branch_index,
                "assumption" => {
                    let Fact::AtomicFact(AtomicFact::EqualFact(f)) = &mut p.assumed_premise else {
                        panic!()
                    };
                    f.left = Obj::Literal(Literal::Number(Number::new("0".into())));
                }
                "store" => {
                    let StoreFactResult::AtomicFact(p) = &mut p.assumed_store_and_infer.store
                    else {
                        panic!()
                    };
                    p.fact_id = future;
                }
                "conclusion" => {
                    super::equality_proof_mut(&mut p.conclusion_proof).fact.left =
                        Obj::Literal(Literal::Number(Number::new("0".into())))
                }
                _ => {
                    let FactWellDefinedProof::Equality(p) = &mut p.assumed_well_defined else {
                        panic!()
                    };
                    let p = p.as_detailed_mut().unwrap();
                    std::mem::swap(&mut p.left, &mut p.right);
                }
            }
            compiler.compile_run(&run, mutation).expect_err(
                "preserve original implication assumptions, WD, publication and selected branch",
            );
        }
    }
}
#[test]
fn classical_implication_requires_all_original_or_branch_formation() {
    for source in [LEFT, RIGHT] {
        let (mut run, compiler) = super::execute(source);
        target(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .branches
            .clear();
        compiler
            .compile_run(&run, "branches")
            .expect_err("forming the implication never bypasses outer Or branch WD");
    }
}
#[test]
fn classical_implication_cannot_cite_its_future_disjunction_in_the_conclusion() {
    for source in [LEFT, RIGHT] {
        let (mut run, compiler) = super::execute(source);
        let future = target(&mut run).fact.fact_id;
        let p = super::equality_proof_mut(&mut selected(&mut run).conclusion_proof);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut p.searched_proof else {
            panic!("original additive congruence")
        };
        let path = super::equality_path_mut(&mut p.corresponding_arg_equal_proofs[0]);
        assert!(!path.path.is_empty());
        path.path[0].2 = future;
        compiler
            .compile_run(&run, "future")
            .expect_err("the original local conclusion cannot use the future Or producer");
    }
}
#[test]
fn classical_implication_assumption_cannot_escape_to_a_later_matching_equality() {
    let (mut run, compiler) = super::execute(SCOPE);
    let private_id = selected(&mut run).assumed_premise.fact_id();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!()
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut p.proof_steps[1] else {
        panic!()
    };
    let path = super::equality_path_mut(&mut p.verify_result);
    assert!(!path.path.is_empty());
    assert_ne!(path.path[0].2, private_id);
    path.path[0].2 = private_id;
    compiler.compile_run(&run,"leak").expect_err("an implication's local assumption stays private even when its subject matches a later true fact");
}
