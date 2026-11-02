use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/finite_subset_theorem/statement.lit");

fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &mut run.statement_results[0]
    else {
        panic!("named theorem");
    };
    let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
        panic!("forall body");
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(call),
    )) = &mut body.proof_steps[0]
    else {
        panic!("original builtin invocation");
    };
    call
}

#[test]
fn finite_subset_explicit_theorem_replays_generic_and_concrete_calls() {
    for source in [
        SOURCE,
        "release thm subset_of_finite_set_is_finite({1},{1,2})\n",
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "finite_subset")
            .unwrap_or_else(|error| {
                panic!(
                    "{error}\n{}",
                    crate::json_output::project_stmt_detailed(
                        &run.statement_results[0],
                        &compiler.runtime
                    )
                    .stringify()
                )
            });
        assert!(output.contains("Litex.finiteSubsetOfFinite"));
        assert_eq!(output, compiler.compile_run(&run, "finite_subset").unwrap());
    }
}

#[test]
fn finite_subset_theorem_requires_original_ordered_proofs_and_stores() {
    for change in [
        "missing_proof",
        "wrong_order",
        "missing_store",
        "wrong_conclusion",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        match change {
            "missing_proof" => {
                call.dom_proofs.pop();
            }
            "wrong_order" => call.dom_proofs.swap(1, 2),
            "missing_store" => {
                call.dom_stores.pop();
            }
            "wrong_conclusion" => {
                let application = call.builtin.as_mut().unwrap();
                let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) =
                    &mut application.conclusions[0]
                else {
                    panic!("finite conclusion");
                };
                f.set = application.arguments[1].clone();
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, change)
            .expect_err("the exact source theorem stages and finite subject are mandatory");
    }
}

#[test]
fn subset_finiteness_inference_requires_its_seed_upper_proof_and_exact_conclusion() {
    use crate::store_fact_and_infer::{InferAtomicFactResult, InferResult, InferSubsetFactResult};
    for change in ["seed", "upper_proof", "conclusion", "missing"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) =
            &mut named.goal_wd
        else {
            panic!()
        };
        let Some(InferResult::AtomicFact(InferAtomicFactResult::SubsetFact(rules))) =
            &mut goal.as_detailed_mut().unwrap().assumed_dom_facts[1]
                .store_and_infer
                .infer
        else {
            panic!("original subset inference");
        };
        if change == "missing" {
            rules.remove(0);
        } else {
            let InferSubsetFactResult::FiniteUpperBound(p) = &mut rules[0] else {
                panic!("finite bound before elementwise publication");
            };
            match change {
                "seed" => p.source_fact_id = FactId::new(u64::MAX),
                "upper_proof" => {
                    let child = super::atomic_proof_mut(&mut p.upper_finite_proof);
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut child.searched_proof
                    else {
                        panic!("stored upper finiteness");
                    };
                    cite.cite_fact_id = p.derived.primary_fact_id();
                }
                "conclusion" => {
                    let StoreFactResult::AtomicFact(stored) = &mut p.derived.store else {
                        panic!()
                    };
                    let AtomicFact::IsFiniteSetFact(f) = &mut stored.fact else {
                        panic!()
                    };
                    f.set = Obj::Literal(Literal::Number(Number::new("7".into())));
                }
                _ => unreachable!(),
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "the later finite-domain citation must be backed by the original preceding inference",
        );
    }
}
