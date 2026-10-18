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
