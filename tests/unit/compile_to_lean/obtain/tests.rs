use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::LitexToLeanCompiler;
use crate::execute::execute_proof_block_stmt::{ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::execute::{
    ExecObtainObjFromExistFactStmtResult, ExecObtainObjFromExistFactStmtSuccessResult,
};
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
        crate::json_output::emit_run_detailed(&run, &runtime, "obtain", None)
    );
    (run, runtime)
}

fn obtain(statement: &mut ExecStmtResult) -> &mut ExecObtainObjFromExistFactStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::ObtainObjFromExistFact(
            ExecObtainObjFromExistFactStmtResult::Success(proof),
        ),
    )) = statement
    else {
        panic!("obtain");
    };
    proof
}

const SOURCE: &str = "witness exist m, n R st {n != 0, m = 1 / n} from 1, 1:\n    1 / 1 = 1\nobtain x, y from exist m, n R st {n != 0, m = 1 / n}\ny != 0\nx = 1 / y\n";

#[test]
fn geo_obtain_replays_guarded_formation_at_renamed_witnesses() {
    let (mut run, runtime) = checked(SOURCE);
    let proof = obtain(&mut run.statement_results[1]);
    let ids: Vec<_> = proof
        .statement
        .equal_tos
        .iter()
        .map(|p| p.id.value())
        .collect();
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "obtain")
        .unwrap();
    for id in ids {
        assert!(output.contains(&format!("noncomputable def _value_i{id}")));
        assert!(!output.contains(&format!("variable {{_Host_i{id}")));
    }
    assert!(output.contains("Classical.choose_spec"));
    assert!(output.contains("(fun (_value_i"));
    assert!(!output.contains("sorry"));
}

#[test]
fn geo_obtain_rejects_missing_original_store() {
    let (mut run, runtime) = checked(SOURCE);
    obtain(&mut run.statement_results[1])
        .store_and_infer_result
        .store_and_infer_results
        .pop();
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad")
        .unwrap_err();
    assert_eq!(error.route, "Obtain/Stages");
}

#[test]
fn geo_obtain_rejects_reordered_subjects_even_with_consistent_id_view() {
    let (mut run, runtime) = checked(SOURCE);
    let stores = &mut obtain(&mut run.statement_results[1]).store_and_infer_result;
    stores.store_and_infer_results.swap(2, 3);
    stores.stored_fact_ids = stores
        .store_and_infer_results
        .iter()
        .flat_map(|s| s.stored_fact_ids())
        .collect();
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad")
        .unwrap_err();
    assert_eq!(error.route, "Obtain/StoreSubject");
}

#[test]
fn geo_obtain_rejects_different_output_binders() {
    let (mut run, runtime) = checked(SOURCE);
    obtain(&mut run.statement_results[1])
        .statement
        .equal_tos
        .swap(0, 1);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad")
        .unwrap_err();
    assert_eq!(error.route, "Obtain/StoreSubject");
}

#[test]
fn geo_obtain_constructor_lookup_cannot_reopen_pending_statement_through_ancestor() {
    let (run, _) = checked(SOURCE);
    let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    let pending = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[1]),
        1,
    );
    let found = pending
        .with_visible_obtain(&mut |_, producer| Ok((producer.before > 1).then_some(())))
        .unwrap();
    assert!(found.is_none());
}

#[test]
fn geo_obtain_global_reference_uses_producer_context_before_later_have() {
    let (mut run, runtime) = checked("have a R\nwitness exist m, n R st {n != 0, m = a / n} from a, 1:\n    a / 1 = a\nobtain u, v from exist m, n R st {n != 0, m = a / n}\nhave unrelated R\nu = a / v\n");
    let id = obtain(&mut run.statement_results[2]).statement.equal_tos[0].id;
    let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    let producer = root.global_obtain_position(id).unwrap();
    assert_eq!(producer.before, 2);
    assert_eq!(producer.context_parameters().len(), 1);
    let compiler = LitexToLeanCompiler::new(runtime);
    let reference = compiler.compile_parameter_reference(id, &root).unwrap();
    let context = producer.context_parameters();
    assert!(reference.contains(&format!("_value_i{}", context[0].0.id.value())));
    assert_eq!(reference.matches("_Host_i").count(), 2);
    compiler.compile_run(&run, "obtain_context").unwrap();
}

#[test]
fn geo_obtain_local_elimination_does_not_export_names() {
    let (run, runtime) = checked("claim:\n    ? 1 = 1\n    witness exist m, n R st {n != 0, m = 1 / n} from 1, 1:\n        1 / 1 = 1\n    obtain local_x, local_y from exist m, n R st {n != 0, m = 1 / n}\n    local_y != 0\n    local_x = 1 / local_y\n    1 = 1\n");
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &run.statement_results[0]
    else {
        panic!("claim");
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::ObtainObjFromExistFact(
            ExecObtainObjFromExistFactStmtResult::Success(proof),
        ),
    )) = &claim.body.proof_steps()[1]
    else {
        panic!("obtain");
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(root
        .visible_parameter(proof.statement.equal_tos[0].id, &runtime)
        .is_err());
    assert!(root
        .global_obtain_position(proof.statement.equal_tos[0].id)
        .is_none());
    assert!(root
        .with_visible_obtain(&mut |_, _| Ok(Some(())))
        .unwrap()
        .is_none());
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "local_obtain")
        .unwrap();
    assert!(output.contains("rcases "));
    assert!(!output.contains("noncomputable def _value_i"));
}

const ATOMIC_SOURCE: &str = "prop has_copy(seed R):\n    exist m, n R st {n != 0, m = seed / n}\nwitness exist m, n R st {n != 0, m = 2 / n} from 2, 1:\n    2 / 1 = 2\n$has_copy(2)\nobtain x, y from $has_copy(2)\nx = 2 / y\n";

fn atomic_obtain(
    statement: &mut ExecStmtResult,
) -> &mut crate::execute::ExecObtainObjFromAtomicFactStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
            crate::execute::ExecObtainObjFromAtomicFactStmtResult::Success(proof),
        ),
    )) = statement
    else {
        panic!("atomic obtain");
    };
    proof
}

#[test]
fn geo_atomic_obtain_replays_outer_and_inner_constructor_binders() {
    let (run, runtime) = checked(ATOMIC_SOURCE);
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "atomic_obtain")
        .unwrap();
    assert!(output.contains("Classical.choose_spec"));
    assert!(output.contains("noncomputable def _value_i"));
    assert!(output.contains("(fun {_Host_i"));
    assert!(output.contains(" : Type _}"));
    assert!(!output.contains("sorry"));
}

#[test]
fn geo_atomic_obtain_rejects_changed_projected_clause() {
    let (mut run, runtime) = checked(ATOMIC_SOURCE);
    let ExistShapedFact::Exist(projected) =
        &mut atomic_obtain(&mut run.statement_results[3]).projected_exist
    else {
        panic!("plain");
    };
    projected.facts.swap(0, 1);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad")
        .unwrap_err();
    assert_eq!(error.route, "ObtainAtomic/ProjectionSubject");
}

#[test]
fn geo_atomic_obtain_rejects_changed_output_order() {
    let (mut run, runtime) = checked(ATOMIC_SOURCE);
    atomic_obtain(&mut run.statement_results[3])
        .statement
        .equal_tos
        .swap(0, 1);
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad")
        .unwrap_err();
    assert_eq!(error.route, "Obtain/StoreSubject");
}

#[test]
fn geo_atomic_obtain_rejects_missing_ordered_store() {
    let (mut run, runtime) = checked(ATOMIC_SOURCE);
    atomic_obtain(&mut run.statement_results[3])
        .store_and_infer_result
        .store_and_infer_results
        .pop();
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad")
        .unwrap_err();
    assert_eq!(error.route, "Obtain/Stages");
}

#[test]
fn geo_atomic_obtain_constructor_cannot_reopen_pending_statement() {
    let (run, _) = checked(ATOMIC_SOURCE);
    let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    let pending = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[3]),
        1,
    );
    assert!(pending
        .with_visible_obtain(&mut |_, producer| Ok((producer.before > 1).then_some(())))
        .unwrap()
        .is_none());
}

#[test]
fn geo_atomic_obtain_local_objects_do_not_escape_claim() {
    let source = format!("{ATOMIC_SOURCE}claim:\n    ? 1 = 1\n    obtain local_x, local_y from $has_copy(2)\n    local_x = 2 / local_y\n    1 = 1\n");
    let (run, runtime) = checked(&source);
    let last = run.statement_results.last().unwrap();
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = last
    else {
        panic!("claim");
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
            crate::execute::ExecObtainObjFromAtomicFactStmtResult::Success(proof),
        ),
    )) = &claim.body.proof_steps()[0]
    else {
        panic!("obtain");
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(root
        .visible_parameter(proof.statement.equal_tos[0].id, &runtime)
        .is_err());
    assert!(root
        .global_obtain_position(proof.statement.equal_tos[0].id)
        .is_none());
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "atomic_local")
        .unwrap();
    assert!(output.contains("rcases "));
}

#[test]
fn local_obtain_from_a_multiclause_prop_retains_an_explicit_existential_type() {
    let source = "prop has_nonnegative_representative(x R):\n    x >= 0\n    exist t R st {x = t}\nthm extract_representative:\n    ? forall x R:\n        $has_nonnegative_representative(x)\n        =>:\n            x = x\n    by def $has_nonnegative_representative(x)\n    obtain t from exist t0 R st {x = t0}\n    x = t\n";
    let (run, runtime) = checked(source);
    let lean = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "multiclause_obtain")
        .unwrap();
    assert!(lean.contains("rcases (show"));
}

#[test]
fn obtained_affine_expression_reuses_original_numeric_formation() {
    let source = r#"prop affine_point(p,a,b cart(R,R)):
    exist t R st {0<=t,t<=1,p(1)=(1-t)*a(1)+t*b(1),p(2)=(1-t)*a(2)+t*b(2)}
thm affine_coordinate:
    ? forall p,a,b cart(R,R):
        $affine_point(p,a,b)
        =>:
            p=p
    by def $affine_point(p,a,b)
    obtain t from exist t0 R st {0<=t0,t0<=1,p(1)=(1-t0)*a(1)+t0*b(1),p(2)=(1-t0)*a(2)+t0*b(2)}
    p(1)=(1-t)*a(1)+t*b(1)=a(1)+t*(b(1)-a(1))
    p=p
"#;
    let (run, runtime) = checked(source);
    let output = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "obtained_affine")
        .unwrap();
    assert!(output.contains("_obtained_object"));
}

#[test]
fn have_by_existence_replays_global_and_local_choices() {
    let (run, runtime) = checked(include_str!(
        "../../../../lean/examples/have_from_existence/statement.lit"
    ));
    let compiler = LitexToLeanCompiler::new(runtime);
    let output = compiler.compile_run(&run, "have_by_existence").unwrap();
    assert!(output.contains("Classical.choose"));
    assert!(output.contains("rcases"));
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjByExistFacts(
            crate::execute::ExecHaveObjByExistFactsStmtResult::Success(proof),
        ),
    )) = &run.statement_results[1]
    else {
        panic!("have by existence")
    };
    let id = proof.statement.param_def.ordered_param_ids()[0];
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let before = SourcePosition::new(
        Some(&root),
        SourceOwner::Statement(&run.statement_results[1]),
        0,
    );
    assert!(before.visible_parameter(id, &compiler.runtime).is_err());
    let after = SourcePosition {
        before: 2,
        ..before
    };
    assert!(after.visible_parameter(id, &compiler.runtime).is_ok());
    let bound = SourcePosition::new(
        Some(&after),
        SourceOwner::ExistWD(
            proof.verify_exist.fact.plain(),
            &proof.verify_exist.well_defined_proof,
        ),
        1,
    );
    assert!(bound.global_obtain_position(id).is_none());
    assert_eq!(
        compiler.compile_parameter_reference(id, &bound).unwrap(),
        format!("_value_i{}", id.value())
    );
    assert!(after.global_obtain_position(id).is_some());
}

#[test]
fn have_by_existence_rejects_changed_existential_or_missing_store() {
    for change_source in [true, false] {
        let (mut run, runtime) = checked(include_str!(
            "../../../../lean/examples/have_from_existence/statement.lit"
        ));
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjByExistFacts(
                crate::execute::ExecHaveObjByExistFactsStmtResult::Success(proof),
            ),
        )) = &mut run.statement_results[1]
        else {
            panic!("have by existence")
        };
        if change_source {
            proof.statement.facts.clear();
        } else {
            proof.store_and_infer_result.store_and_infer_results.pop();
        }
        assert!(LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "bad_have_by_existence")
            .is_err());
    }
}

#[test]
fn have_by_existence_does_not_relax_obtain_binder_freshness() {
    let (mut run, runtime) = checked(SOURCE);
    let p = obtain(&mut run.statement_results[1]);
    p.statement.equal_tos[0] =
        p.statement.fact.plain().typed_parameters.groups[0].params[0].clone();
    let error = LitexToLeanCompiler::new(runtime)
        .compile_run(&run, "bad_obtain")
        .unwrap_err();
    assert!(error.to_string().contains("Obtain/ParameterIdentity"));
}
