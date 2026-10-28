use super::{
    source_position::{SourceOwner, SourcePosition},
    LitexToLeanCompiler,
};
use crate::execute::execute_by_stmt::{
    ByInducBodySuccess, ExecByInducStmtResult, ExecByInducStmtSuccess, ExecByStmtResult,
};
use crate::prelude::*;

const SOURCE: &str = "by induc k from 0:\n    ? k = k\n    ? from k = 0:\n        0 = 0\n    ? induc:\n        k + 1 = k + 1\n";

const LOCAL_RECURSIVE_SOURCE: &str = r#"claim:
    ? forall n N:
        n = 0 or n > 0
    n >= 0

claim:
    ? forall n N:
        n > 0
        =>:
            n - 1 >= 0
    n - 1 $in N
    n - 1 >= 0

have fn repeated_one(n N) R by induc n from 0:
    case n = 0: 1
    case n > 0: repeated_one(n - 1)

repeated_one(0) = 1

forall n N:
    n > 0
    =>:
        repeated_one(n) = repeated_one(n - 1)

thm repeated_one_is_one:
    ? forall n N:
        repeated_one(n) = 1
    by induc k from 0:
        ? repeated_one(k) = 1
        ? from k = 0:
            repeated_one(0) = 1
        ? induc:
            k + 1 > 0
            (k + 1) - 1 = k
            repeated_one(k + 1) = repeated_one((k + 1) - 1)
            repeated_one((k + 1) - 1) = repeated_one(k)
"#;

fn checked() -> (RunLitexCodeResult, LitexToLeanCompiler) {
    checked_source(SOURCE)
}

fn checked_source(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime
        .run_litex_code(source)
        .expect("typed induction source");
    assert!(result.success && result.session_error.is_none());
    (result, LitexToLeanCompiler::new(runtime))
}

#[test]
fn local_recursive_induction_cites_its_original_forall_at_the_callers_universe() {
    let (result, compiler) = checked_source(LOCAL_RECURSIVE_SOURCE);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(theorem),
    )) = &result.statement_results[5]
    else {
        panic!("original enclosing natural theorem");
    };
    let ExecDefThmBodyProof::Forall(body) = &theorem.body else {
        panic!("original forall body");
    };
    let ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(induction))) =
        &body.proof_steps[0]
    else {
        panic!("original local induction");
    };
    let VerifyFactResult::Equality(conclusion) = &body.conclusion_proofs[0] else {
        panic!("original enclosing equality conclusion");
    };
    let VerifyEqualityResult::Success(conclusion) = conclusion.as_ref() else {
        panic!("checked enclosing conclusion");
    };
    let EqualFactSearchedProof::ByKnownForallFact(citation) = &conclusion.searched_proof else {
        panic!("the original conclusion must consume the local induction forall");
    };
    let id = induction.stored.primary_fact_id();
    assert_eq!(citation.detailed_ref().cite.fact_id, id);
    let lean = compiler
        .compile_run(&result, "local_recursive_induction")
        .expect("original local induction and generic outer observation compile");
    let declaration = lean
        .lines()
        .find(|line| line.contains(&format!("have h_{} :", id.value())))
        .expect("the actual local induction FactId is emitted");
    assert!(declaration.contains("M.Value"));
    assert!(!declaration.contains(&format!("Type v{}", induction.parameter.id.value())));
    assert!(lean.contains(&format!("=> h_{} (Litex.denote _value)", id.value())));
    assert!(lean.contains("Litex.integerInductionFromZero"));
}

fn induction(result: &mut RunLitexCodeResult) -> &mut ExecByInducStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof))) =
        &mut result.statement_results[0]
    else {
        panic!("source induction");
    };
    proof
}

#[test]
fn induction_replays_original_cases_and_exports_generic_integer_domain() {
    let (result, compiler) = checked();
    let lean = compiler
        .compile_run(&result, "induction_original_cases")
        .expect("captured induction");
    assert!(lean.contains("Litex.integerInductionFromZero"));
    assert!(lean.contains("_induction_hypothesis"));
    assert!(lean.contains("_Host_i"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn induction_rejects_missing_original_parameter_store() {
    let (mut result, compiler) = checked();
    induction(&mut result)
        .introduced_parameter
        .defined_params
        .store_and_infer_results
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "induction_missing_intro")
            .unwrap_err()
            .route,
        "Parameters/StoreCapture"
    );
}

#[test]
fn induction_rejects_missing_original_base_conclusion() {
    let (mut result, compiler) = checked();
    let proof = induction(&mut result);
    let (ByInducBodySuccess::Structured { base, .. }
    | ByInducBodySuccess::Unstructured { base, .. }) = &mut proof.body;
    base.goals_verified.swap_remove(0);
    assert!(compiler
        .compile_run(&result, "induction_missing_base")
        .unwrap_err()
        .route
        .contains("CaseStages"));
}

#[test]
fn induction_rejects_a_successful_conclusion_from_the_other_case() {
    let (mut result, compiler) = checked();
    let proof = induction(&mut result);
    let (ByInducBodySuccess::Structured { base, step }
    | ByInducBodySuccess::Unstructured { base, step }) = &mut proof.body;
    std::mem::swap(&mut base.goals_verified[0], &mut step.goals_verified[0]);
    assert!(compiler
        .compile_run(&result, "induction_wrong_case_conclusion")
        .unwrap_err()
        .route
        .contains("CaseConclusionSubject"));
}

#[test]
fn induction_rejects_a_forged_introduction_identifier_view() {
    let (mut result, compiler) = checked();
    induction(&mut result)
        .introduced_parameter
        .defined_params
        .stored_fact_ids
        .clear();
    assert!(compiler
        .compile_run(&result, "induction_forged_intro_view")
        .is_err());
}

#[test]
fn induction_rejects_missing_original_hypothesis_assumption() {
    let (mut result, compiler) = checked();
    let proof = induction(&mut result);
    let (ByInducBodySuccess::Structured { step, .. }
    | ByInducBodySuccess::Unstructured { step, .. }) = &mut proof.body;
    step.assumptions.pop();
    assert!(compiler
        .compile_run(&result, "induction_missing_ih")
        .unwrap_err()
        .route
        .contains("CaseStages"));
}

#[test]
fn induction_case_facts_do_not_escape_or_become_future_producers() {
    let (result, compiler) = checked();
    let statement = &result.statement_results[0];
    let ExecStmtResult::By(ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof))) =
        statement
    else {
        panic!("source induction");
    };
    let (ByInducBodySuccess::Structured { step, .. }
    | ByInducBodySuccess::Unstructured { step, .. }) = &proof.body;
    let root = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let header = SourcePosition::new(Some(&root), SourceOwner::Induction(proof.into()), 0);
    assert!(header
        .visible_fact(
            proof.goal_domain.store_and_infer.primary_fact_id(),
            &compiler.runtime
        )
        .is_err());
    let case = SourcePosition::new(
        Some(&header),
        SourceOwner::InductionCase(proof.into(), step),
        1,
    );
    assert!(case
        .visible_fact(
            step.assumptions[1].store_and_infer.primary_fact_id(),
            &compiler.runtime
        )
        .is_err());
    let after = SourcePosition::new(None, SourceOwner::Run(&result), 1);
    assert!(after
        .visible_fact(
            step.assumptions[1].store_and_infer.primary_fact_id(),
            &compiler.runtime
        )
        .is_err());
}

#[test]
fn strong_induction_replays_original_bounded_hypotheses_and_both_cases() {
    let (result, compiler) = checked_source(include_str!(
        "../../lean/examples/strong_integer_identity/statement.lit"
    ));
    let output = compiler
        .compile_run(&result, "strong_integer_identity")
        .unwrap();
    assert!(output.contains("Litex.integerStrongInductionFromZero"));
    assert!(output.contains("_induction_hypothesis (Litex.denote _value_i"));
    assert!(!output.contains("sorry") && !output.contains("axiom"));
}

#[test]
fn strong_induction_rejects_changed_or_missing_original_hypothesis_and_conclusions() {
    for change in [
        "upper",
        "lower",
        "conclusion",
        "missing_ih",
        "missing_base",
        "missing_step",
    ] {
        let (mut result, compiler) = checked_source(include_str!(
            "../../lean/examples/strong_integer_identity/statement.lit"
        ));
        let ExecStmtResult::By(ExecByStmtResult::StrongInduc(
            crate::execute::execute_by_stmt::ExecByStrongInducStmtResult::Success(proof),
        )) = &mut result.statement_results[1]
        else {
            panic!("original strong induction")
        };
        let (ByInducBodySuccess::Structured { base, step }
        | ByInducBodySuccess::Unstructured { base, step }) = &mut proof.body;
        match change {
            "missing_ih" => {
                step.assumptions.pop();
            }
            "missing_base" => base.goals_verified.clear(),
            "missing_step" => step.goals_verified.clear(),
            _ => {
                let StoreFactResult::ForallFact(source) =
                    &mut step.assumptions[1].store_and_infer.store
                else {
                    panic!("bounded IH")
                };
                match change {
                    "upper" => {
                        let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) =
                            &mut source.fact.dom_facts[1]
                        else {
                            panic!("upper")
                        };
                        f.right = Obj::Literal(Literal::Number(Number::new("7".into())));
                    }
                    "lower" => {
                        let Fact::AtomicFact(AtomicFact::GreaterEqualFact(f)) =
                            &mut source.fact.dom_facts[0]
                        else {
                            panic!("lower")
                        };
                        f.right = Obj::Literal(Literal::Number(Number::new("7".into())));
                    }
                    "conclusion" => source.fact.then_facts.clear(),
                    _ => unreachable!(),
                }
            }
        }
        assert!(
            compiler
                .compile_run(&result, "corrupted_strong_induction")
                .is_err(),
            "{change}"
        );
    }
}
