use super::LitexToLeanCompiler;
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const RELEASE: &str = "thm release_zero:\n    ? forall x R:\n        x+0=x\nrelease thm release_zero(2)\n2+0=2\nby thm release_zero(3) => 3+0=3\n";
const NATURAL: &str = "thm release_nonnegative:\n    ? forall n N:\n        0 <= n\nhave a N\nrelease thm release_nonnegative(a)\na $in N\n";
const EXISTENTIAL: &str = "thm copy_witness:\n    ? forall x R:\n        exist y R st {y=x}\n    witness exist y R st {y=x} from x\nrelease thm copy_witness(2)\nobtain copy from exist y R st {y=2}\ncopy=2\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

#[test]
fn release_existential_return_replays_the_package_and_obtained_witness() {
    let (result, compiler) = checked(EXISTENTIAL);
    let lean = compiler.compile_run(&result, "released_witness").unwrap();
    assert!(lean.contains("∃"));
    assert!(lean.contains("Classical.choose_spec"));
}

#[test]
fn release_existential_return_rejects_missing_formation_and_changed_package() {
    for mutation in 0..3 {
        let (mut result, compiler) = checked(EXISTENTIAL);
        let release = release_mut(&mut result.statement_results[1]);
        match mutation {
            0 => release.conclusions_wd.clear(),
            1 => release.stored_wd.clear(),
            2 => {
                let StoreFactResult::ExistShapedFact(stored) = &mut release.stored[0].store else {
                    panic!("original existential return");
                };
                let ExistShapedFact::Exist(fact) = &mut stored.fact else {
                    panic!("plain existential");
                };
                fact.facts.clear();
            }
            _ => unreachable!(),
        }
        assert!(compiler
            .compile_run(&result, "invalid_released_witness")
            .is_err());
    }
}

fn release_mut(statement: &mut ExecStmtResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(proof),
    )) = statement
    else {
        panic!("actual successful release")
    };
    proof
}

#[test]
fn release_and_by_theorem_replay_their_original_types_stores_and_caller_wd() {
    for source in [RELEASE, NATURAL] {
        let (result, compiler) = checked(source);
        let lean = compiler
            .compile_run(&result, "release_original_pipeline")
            .expect("actual release and ByThm evidence");
        assert!(lean.contains("Litex.Same") || lean.contains("Litex.Le"));
    }
}

#[test]
fn release_rejects_missing_actual_type_store_or_return_caller_wd() {
    let (mut result, compiler) = checked(RELEASE);
    release_mut(&mut result.statement_results[1])
        .type_stores
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "release_missing_type_store")
            .unwrap_err()
            .route,
        "ByThm/TypeStoreStages"
    );
    let (mut result, compiler) = checked(RELEASE);
    release_mut(&mut result.statement_results[1])
        .stored_wd
        .clear();
    assert_eq!(
        compiler
            .compile_run(&result, "release_missing_caller_wd")
            .unwrap_err()
            .route,
        "ReleaseThm/CallerStages"
    );
}

#[test]
fn release_rejects_original_argument_changed_after_execution() {
    let (mut result, compiler) = checked(RELEASE);
    let TheoremCallArguments::Parenthesized(arguments) =
        &mut release_mut(&mut result.statement_results[1]).call.arguments
    else {
        panic!("actual arguments")
    };
    arguments[0] = Obj::Literal(Literal::Number(Number::new("4".into())));
    assert_eq!(
        compiler
            .compile_run(&result, "release_other_argument")
            .unwrap_err()
            .route,
        "ByThm/TypeProof"
    );
}

#[test]
fn completed_release_does_not_export_its_call_local_type_identity() {
    let (mut result, compiler) = checked(NATURAL);
    let local_id = release_mut(&mut result.statement_results[2]).type_stores[0].primary_fact_id();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &mut result.statement_results[3]
    else {
        panic!("actual subsequent membership")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &mut step.verify_result else {
        panic!("actual membership proof")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("actual success")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
        &mut proof.searched_proof
    else {
        panic!("actual earlier ambient membership citation")
    };
    assert_ne!(citation.cite_fact_id, local_id);
    citation.cite_fact_id = local_id;
    assert!(compiler
        .compile_run(&result, "release_call_local_identity_escape")
        .is_err());
}

#[test]
fn bare_release_reuses_the_same_original_declaration_identity() {
    let (result, compiler) =
        checked("thm bare_release:\n    ? 1=1\nrelease thm bare_release\n1=1\n");
    compiler
        .compile_run(&result, "bare_release_retained_identity")
        .expect("original bare theorem declaration");
}
