use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::VerifyForallFactWithIffSuccess;
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../../lean/examples/equivalence_directions/statement.lit");

fn fact(statement: &mut ExecStmtResult) -> &mut ExecFactStmtSuccessResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) = statement else {
        panic!("fact")
    };
    proof
}

fn iff(statement: &mut ExecStmtResult) -> &mut VerifyForallFactWithIffSuccess {
    let VerifyFactResult::ForallFactWithIff(result) = &mut fact(statement).verify_result else {
        panic!("iff")
    };
    let VerifyForallFactWithIffResult::Success(proof) = result.as_mut() else {
        panic!("success")
    };
    proof
}

fn direction(result: &mut VerifyFactResult) -> &mut ForallFact {
    let VerifyFactResult::ForallFact(result) = result else {
        panic!("forall")
    };
    match result.as_mut() {
        VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) => {
            &mut p.fact
        }
        VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) => &mut p.fact,
        VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(p)) => {
            &mut p.fact
        }
        _ => panic!("success"),
    }
}

#[test]
fn forall_iff_exports_both_original_stored_directions() {
    let (mut run, compiler) = super::execute(SOURCE);
    let StoreFactResult::ForallFactWithIff(store) = &fact(&mut run.statement_results[0])
        .store_and_infer_result
        .store
    else {
        panic!("store")
    };
    let ids = [store.forward.fact_id, store.reverse.fact_id];
    let surface = store.fact_id;
    for (index, id) in ids.iter().enumerate() {
        let VerifyFactResult::ForallFact(result) =
            &fact(&mut run.statement_results[index + 1]).verify_result
        else {
            panic!("forall")
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
            result.as_ref()
        else {
            panic!("the whole direction must cite the stored forall")
        };
        assert_eq!(proof.cite_fact_id, *id);
    }
    let output = compiler.compile_run(&run, "iff").unwrap();
    assert_eq!(
        compiler.compile_run(&run, "iff").unwrap(),
        output,
        "Replaying the same typed result must preserve the artifact exactly"
    );
    for (index, id) in ids.iter().enumerate() {
        assert!(output.contains(&format!("theorem h_{}", id.value())));
        assert!(
            output.contains(&format!("((h_{} (M := M))).{}", surface.value(), index + 1)),
            "{output}"
        );
    }
}

#[test]
fn forall_iff_premise_requires_both_original_wd_sides() {
    let (mut run, compiler) = super::execute(SOURCE);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(proof),
    )) = run.statement_results.last_mut().unwrap()
    else {
        panic!("theorem")
    };
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(wd)) =
        &mut proof.goal_wd
    else {
        panic!("forall wd")
    };
    let FactWellDefinedProof::ForallFactWithIff(wd) =
        &mut wd.as_detailed_mut().unwrap().assumed_dom_facts[0].well_defined
    else {
        panic!("iff wd")
    };
    wd.as_detailed_mut().unwrap().iff.clear();
    let error = compiler.compile_run(&run, "iff").unwrap_err();
    assert_eq!(error.route, "ForallIff/FormationArity", "{error:?}");
}

#[test]
fn forall_iff_rejects_changed_direction_or_missing_shared_premise() {
    for edit in 0..3 {
        let (mut run, compiler) = super::execute(SOURCE);
        let proof = iff(&mut run.statement_results[3]);
        match edit {
            0 => {
                direction(&mut proof.then_implies_iff).dom_facts.remove(0);
            }
            1 => {
                std::mem::swap(&mut proof.then_implies_iff, &mut proof.iff_implies_then);
            }
            _ => {
                direction(&mut proof.iff_implies_then)
                    .typed_parameters
                    .groups
                    .clear();
            }
        }
        let error = compiler.compile_run(&run, "iff").unwrap_err();
        assert_eq!(error.route, "ForallIff/Direction", "{error:?}");
    }
}

#[test]
fn forall_iff_rejects_corrupt_direction_stores() {
    for identity in [false, true] {
        let (mut run, compiler) = super::execute(SOURCE);
        let StoreFactResult::ForallFactWithIff(store) = &mut fact(&mut run.statement_results[0])
            .store_and_infer_result
            .store
        else {
            panic!("store")
        };
        if identity {
            store.reverse.fact_id = store.forward.fact_id;
        } else {
            store.reverse.fact.dom_facts.clear();
        }
        let error = compiler.compile_run(&run, "iff").unwrap_err();
        assert!(error.route.starts_with("ForallIff/"), "{error:?}");
    }
}

#[test]
fn forall_iff_directions_cannot_cite_a_future_iff() {
    let (mut run, compiler) = super::execute(SOURCE);
    let StoreFactResult::ForallFactWithIff(store) = &fact(&mut run.statement_results[3])
        .store_and_infer_result
        .store
    else {
        panic!("store")
    };
    let future = store.forward.fact_id;
    let VerifyFactResult::ForallFact(result) =
        &mut fact(&mut run.statement_results[1]).verify_result
    else {
        panic!("forall")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
        result.as_mut()
    else {
        panic!("known")
    };
    proof.cite_fact_id = future;
    assert!(compiler.compile_run(&run, "iff").is_err());
}

#[test]
fn forall_iff_opposite_side_does_not_supply_division_wd() {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime
        .run_litex_code("forall x R:\n    =>:\n        x != 0\n    <=>:\n        1 / x != 0\n")
        .unwrap();
    assert!(!run.success);
    assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "unguarded_iff")
        .is_err());
}
