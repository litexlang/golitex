use crate::compile_to_lean::LitexToLeanCompiler;
use crate::execute::execute_witness_stmt::{ExecWitnessExistFactStmtResult, ExecWitnessStmtResult};
use crate::prelude::*;

fn checked(source: &str) -> (RunLitexCodeResult, Runtime) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = runtime.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{}",
        crate::json_output::emit_run_detailed(&run, &runtime, "witness", None)
    );
    (run, runtime)
}

const SOURCE: &str = "witness exist m, n R st {n != 0, m = 1 / n} from 1, 1:\n    1 / 1 = 1\nexist x, y R st {y != 0, x = 1 / y}\n";

const PREDICATE: &str = "prop has_copy(a R):\n    exist x R st {x = a}\nthm copy_exists:\n    ? forall a R:\n        $has_copy(a)\n    witness $has_copy(a) from a:\n        a = a\n";

#[test]
fn predicate_witness_replays_its_original_existential_pipeline() {
    let (run, runtime) = checked(PREDICATE);
    let code = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "predicate_witness")
        .unwrap();
    assert!(code.contains("Exists.intro"));
    assert!(code.contains("Litex.semanticObject"));
}

#[test]
fn predicate_witness_rejects_missing_or_mismatched_argument_evidence() {
    use crate::execute::execute_witness_stmt::ExecWitnessAtomicFactStmtResult;
    for missing in [true, false] {
        let source = "prop has_copy(a R):\n    exist x R st {x = a}\nwitness $has_copy(2) from 2\n";
        let (mut run, runtime) = checked(source);
        let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessAtomicFact(
            ExecWitnessAtomicFactStmtResult::Success(p),
        )) = &mut run.statement_results[1]
        else {
            panic!("predicate witness")
        };
        if missing {
            p.prop_argument_type_checks.clear();
        } else {
            let VerifyFactResult::AtomicExceptEquality(check) = &mut p.prop_argument_type_checks[0]
            else {
                panic!("membership")
            };
            let VerifyAtomicExceptEqualityFactResult::Success(check) = check.as_mut() else {
                panic!("successful membership")
            };
            let AtomicFact::InFact(member) = &mut check.fact else {
                panic!("membership subject")
            };
            member.element = Obj::StandardSet(StandardSet::C);
        }
        assert!(LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "bad_witness")
            .is_err());
    }
}

#[test]
fn geo_witness_replays_original_equalities_as_reflexivity_and_cites_exists() {
    let (run, runtime) = checked(SOURCE);
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(proof),
    )) = &run.statement_results[0]
    else {
        panic!("witness")
    };
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "witness")
        .unwrap();
    assert!(output.contains("Litex.semanticObject"));
    for store in &proof.witness_equalities {
        let name = format!("have h_{} :", store.primary_fact_id().value());
        let line = output
            .lines()
            .find(|line| line.contains(&name))
            .expect("original equality declaration");
        assert!(line.ends_with(":= rfl"), "{line}");
    }
    assert!(output.contains(&format!(
        "h_{} (M := M)",
        proof.store_and_infer_result.primary_fact_id().value()
    )));
    assert!(!output.contains("sorry"));
}

#[test]
fn geo_witness_rejects_missing_original_equality_stage() {
    let (mut run, runtime) = checked(SOURCE);
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
        ExecWitnessExistFactStmtResult::Success(proof),
    )) = &mut run.statement_results[0]
    else {
        panic!("witness")
    };
    proof.witness_equalities.pop();
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad_witness")
        .unwrap_err();
    assert_eq!(error.route, "Witness/Stages");
}

#[test]
fn nonempty_witness_compiles_local_membership_and_publishes_only_nonemptiness() {
    let source = include_str!("../../../../lean/examples/nonempty_witness/statement.lit");
    let (run, runtime) = checked(source);
    let compiler = LitexToLeanCompiler::new(runtime);
    let output = compiler.compile_run(&run, "nonempty_witness").unwrap();
    assert!(output.contains("Litex.IsNonempty"));
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    use crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtResult;
    let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessNonemptySet(
        ExecWitnessNonemptySetStmtResult::Success(proof),
    )) = &run.statement_results[0]
    else {
        panic!("witness")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &proof.proof_steps[0] else {
        panic!("proof step")
    };
    let id = step.store_and_infer_result.primary_fact_id();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let statement = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[0]),
        2,
    );
    let before = SourcePosition::new(Some(&statement), SourceOwner::WitnessNonempty(proof), 0);
    assert!(before.visible_fact(id, &compiler.runtime).is_err());
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(after.visible_fact(id, &compiler.runtime).is_ok());
    assert!(statement
        .visible_fact(
            proof.store_and_infer_result.primary_fact_id(),
            &compiler.runtime
        )
        .is_err());
    let outer = SourcePosition { before: 1, ..root };
    assert!(outer.visible_fact(id, &compiler.runtime).is_err());
    assert!(outer
        .visible_fact(
            proof.store_and_infer_result.primary_fact_id(),
            &compiler.runtime
        )
        .is_ok());
}

#[test]
fn nonempty_witness_rejects_missing_body_or_changed_membership() {
    use crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtResult;
    for change in ["body", "membership", "source"] {
        let (mut run, runtime) = checked(include_str!(
            "../../../../lean/examples/nonempty_witness/statement.lit"
        ));
        let ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessNonemptySet(
            ExecWitnessNonemptySetStmtResult::Success(proof),
        )) = &mut run.statement_results[0]
        else {
            panic!("witness")
        };
        if change == "body" {
            proof.proof_steps.clear();
        } else if change == "source" {
            proof.statement.proof[0] = Stmt::Fact(
                crate::compile_to_lean::helper::source_subject(&proof.membership_check).unwrap(),
            );
        } else {
            let VerifyFactResult::AtomicExceptEquality(result) = &mut proof.membership_check else {
                panic!("member")
            };
            let VerifyAtomicExceptEqualityFactResult::Success(result) = result.as_mut() else {
                panic!("verified")
            };
            let AtomicFact::InFact(member) = &mut result.fact else {
                panic!("member")
            };
            member.element = Obj::StandardSet(StandardSet::R);
        }
        assert!(LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "bad_nonempty")
            .is_err());
    }
}
