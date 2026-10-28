use crate::compile_to_lean::LitexToLeanCompiler;
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
use crate::prelude::*;

fn checked(source: &str) -> (RunLitexCodeResult, Runtime) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let run = runtime.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{}",
        crate::json_output::emit_run_detailed(&run, &runtime, "exist_formation", None)
    );
    (run, runtime)
}

fn predicate(run: &mut RunLitexCodeResult) -> &mut ExecDefPropStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Success(proof),
    )) = &mut run.statement_results[0]
    else {
        panic!("predicate definition")
    };
    proof
}

#[test]
fn geo_exist_formation_keeps_canonical_objects_and_original_guard_ids() {
    let (mut run, runtime) =
        checked("prop reciprocal_copy(a R):\n    exist b R st {b != 0, a = 1 / b}\n");
    let definition = predicate(&mut run);
    let Fact::ExistFact(source) = &definition.statement.iff_facts[0] else {
        panic!("exist clause")
    };
    let object_id = source.typed_parameters.groups[0].params[0].id.value();
    let FactWellDefinedProof::ExistFact(formation) = &definition.assumed_iff_facts[0].well_defined
    else {
        panic!("exist formation")
    };
    let member_id = formation
        .detailed_ref()
        .introduced_params
        .defined_params
        .store_and_infer_results[0]
        .primary_fact_id()
        .value();
    let guard_id = formation.detailed_ref().assumed_body_facts[0]
        .store_and_infer
        .primary_fact_id()
        .value();
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "canonical_exist")
        .unwrap();
    assert!(output.contains(&format!(
        "∃ (_value_i{object_id} : Litex.Obj (M := M) M.Value)"
    )));
    assert!(output.contains(&format!("∃ (h_{member_id} : Litex.In _value_i{object_id} ")));
    let guard = output
        .find(&format!("∃ (h_{guard_id} :"))
        .expect("original guard binder");
    let division = output[guard..]
        .find("Litex.div")
        .expect("dependent division after guard");
    assert!(division > 0);
    assert!(!output.contains("sorry"));
}

#[test]
fn geo_exist_formation_rejects_missing_or_reordered_guard_evidence() {
    for remove in [true, false] {
        let (mut run, runtime) =
            checked("prop reciprocal_copy(a R):\n    exist b R st {b != 0, a = 1 / b}\n");
        let definition = predicate(&mut run);
        let FactWellDefinedProof::ExistFact(formation) =
            &mut definition.assumed_iff_facts[0].well_defined
        else {
            panic!("exist formation")
        };
        if remove {
            formation
                .as_detailed_mut()
                .unwrap()
                .assumed_body_facts
                .remove(0);
        } else {
            formation
                .as_detailed_mut()
                .unwrap()
                .assumed_body_facts
                .swap(0, 1);
        }
        let error = LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "bad_exist_evidence")
            .unwrap_err();
        if remove {
            assert_eq!(error.route, "Exist/FormationStages");
        }
    }
}
