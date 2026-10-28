use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    SearchProofByKnownForallFact, VerifyEqualitySuccess,
};
use crate::prelude::*;

const SOURCE: &str = "claim:\n    ? forall n N:\n        n = 0 or n > 0\n    n >= 0\n\n\
claim:\n    ? forall n N:\n        n > 0\n        =>:\n            n - 1 >= 0\n    n - 1 $in N\n    n - 1 >= 0\n\n\
have fn equality_known_repeat(n N) R by induc n from 0:\n    case n = 0: 1\n    case n > 0: equality_known_repeat(n - 1)\n\n\
thm equality_known_repeat_step:\n    ? forall n N:\n        0 <= n\n        =>:\n            equality_known_repeat(n + 1) = equality_known_repeat(n)\n    n + 1 > 0\n    (n + 1) - 1 = n\n    equality_known_repeat(n + 1) = equality_known_repeat((n + 1) - 1)\n    equality_known_repeat((n + 1) - 1) = equality_known_repeat(n)\n\n\
have equality_known_direct_arg N\n\
equality_known_repeat(equality_known_direct_arg + 1) = equality_known_repeat(equality_known_direct_arg)\n\n\
have equality_known_symmetric_arg N\n\
equality_known_repeat(equality_known_symmetric_arg) = equality_known_repeat(equality_known_symmetric_arg + 1)\n";

fn checked() -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(SOURCE).expect("known forall source");
    assert!(result.success && result.session_error.is_none());
    (result, LitexToLeanCompiler::new(runtime))
}

fn equality(result: &mut RunLitexCodeResult, symmetric: bool) -> &mut VerifyEqualitySuccess {
    let index = if symmetric { 7 } else { 5 };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[index]
    else {
        panic!("actual original equality statement")
    };
    let VerifyFactResult::Equality(proof) = &mut statement.verify_result else {
        panic!("actual equality result")
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("actual successful equality")
    };
    proof
}

fn application(
    result: &mut RunLitexCodeResult,
    symmetric: bool,
) -> &mut SearchProofByKnownForallFact {
    match &mut equality(result, symmetric).searched_proof {
        EqualFactSearchedProof::ByKnownForallFact(proof) if !symmetric => proof,
        EqualFactSearchedProof::ByKnownForallFactViaSymmetry(proof) if symmetric => {
            &mut proof.known_forall
        }
        _ => panic!("actual original direct or symmetric known forall route"),
    }
}

#[test]
fn equality_known_forall_replays_original_direct_and_symmetric_captures() {
    let (mut result, compiler) = checked();
    for symmetric in [false, true] {
        let application = application(&mut result, symmetric);
        assert_eq!(application.detailed_ref().arg_match_proofs.len(), 2);
        assert_eq!(
            application
                .detailed_ref()
                .instantiation_requirements
                .detailed_ref()
                .param_type_requirements
                .len(),
            1
        );
        assert_eq!(
            application
                .detailed_ref()
                .instantiation_requirements
                .detailed_ref()
                .proof_of_dom_facts
                .len(),
            1
        );
    }
    let lean = compiler
        .compile_run(&result, "original_direct_and_symmetric_equalities")
        .expect("actual typed equality forall citations");
    assert!(lean.contains("(Eq.symm (by"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn equality_known_forall_rejects_missing_original_match_type_and_domain_evidence() {
    for symmetric in [false, true] {
        for missing in 0..3 {
            let (mut result, compiler) = checked();
            let proof = application(&mut result, symmetric);
            match missing {
                0 => {
                    proof.as_detailed_mut().unwrap().arg_match_proofs.pop();
                }
                1 => proof
                    .as_detailed_mut()
                    .unwrap()
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements
                    .clear(),
                _ => proof
                    .as_detailed_mut()
                    .unwrap()
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .proof_of_dom_facts
                    .clear(),
            }
            assert_eq!(
                compiler
                    .compile_run(&result, "missing_known_equality_evidence")
                    .unwrap_err()
                    .route,
                "CompoundKnown/OrderedArity"
            );
        }
    }
}

#[test]
fn equality_known_forall_rejects_reordered_original_endpoint_matches() {
    for symmetric in [false, true] {
        let (mut result, compiler) = checked();
        application(&mut result, symmetric)
            .as_detailed_mut()
            .unwrap()
            .arg_match_proofs
            .swap(0, 1);
        assert_eq!(
            compiler
                .compile_run(&result, "reordered_known_equality_matches")
                .unwrap_err()
                .route,
            "CompoundKnown/StructureSubject"
        );
    }
}

#[test]
fn equality_known_forall_rejects_exchanging_original_type_and_domain_certificates() {
    for symmetric in [false, true] {
        let (mut result, compiler) = checked();
        let requirements = application(&mut result, symmetric)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap();
        std::mem::swap(
            &mut requirements.param_type_requirements[0].proof,
            &mut requirements.proof_of_dom_facts[0],
        );
        assert_eq!(
            compiler
                .compile_run(&result, "exchanged_known_equality_requirements")
                .unwrap_err()
                .route,
            "CompoundKnown/TypeIdentity"
        );
    }
}

#[test]
fn equality_known_forall_rejects_changing_the_captured_argument() {
    for symmetric in [false, true] {
        let (mut result, compiler) = checked();
        application(&mut result, symmetric)
            .as_detailed_mut()
            .unwrap()
            .forall_parameters_match_what_args[0] =
            Obj::Literal(Literal::Number(Number::new("2".into())));
        assert_eq!(
            compiler
                .compile_run(&result, "changed_known_equality_argument")
                .unwrap_err()
                .route,
            "CompoundKnown/BoundParameter"
        );
    }
}

#[test]
fn equality_known_forall_symmetry_rejects_changed_original_reversed_endpoint() {
    let (mut result, compiler) = checked();
    let EqualFactSearchedProof::ByKnownForallFactViaSymmetry(proof) =
        &mut equality(&mut result, true).searched_proof
    else {
        panic!("actual original symmetric known forall")
    };
    proof.reversed_equal.left = proof.reversed_equal.right.clone();
    assert_eq!(
        compiler
            .compile_run(&result, "changed_known_equality_reversed_endpoint")
            .unwrap_err()
            .route,
        "Equality/KnownForallSymmetryEndpoints"
    );
}
