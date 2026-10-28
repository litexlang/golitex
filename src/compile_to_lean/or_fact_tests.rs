use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::verify_or_fact::OrFactSearchProofByKnownOrFact;
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
use crate::prelude::*;

const SOURCE: &str =
    "claim:\n    ? forall n N:\n        n = 0 or n > 0\n    n >= 0\nhave n N\nn = 0 or n > 0\n";
const KNOWN_OR: &str = "have fn or_gate(x, y R: x < 0 or y < 0) R = x + y\nprop or_gate_checked(a, b, c, d R):\n    a = c\n    b = d\n    a < 0 and b < 0 or a = b\n    a < 0 or b < 0\n    or_gate(c, d) = c + d\n    c < 0 or d < 0\n";
const EXIST_KNOWN_OR: &str = "have fn or_gate(x, y R: x < 0 or y < 0) R = x + y\nprop or_gate_exists(z R):\n    exist x, y R st {x < 0 or y < 0, z = or_gate(x, y)}\n";

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
    let result = runtime.run_litex_code(source).expect("Or source");
    assert!(result.success && result.session_error.is_none());
    (result, LitexToLeanCompiler::new(runtime))
}

fn property(result: &mut RunLitexCodeResult) -> &mut ExecDefPropStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Success(proof),
    )) = &mut result.statement_results[1]
    else {
        panic!("actual concrete predicate definition");
    };
    proof
}

fn known_call_guard(wd: &mut ObjWellDefinedProof) -> &mut OrFactSearchProofByKnownOrFact {
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = (wd).as_detailed_mut().unwrap()
    else {
        panic!("actual original function-call constructor");
    };
    let VerifyFactResult::OrFact(guard) = &mut call.requirement_fact_verified[2] else {
        panic!("actual ordered disjunction guard");
    };
    let VerifyOrFactResult::Success(guard) = guard.as_mut() else {
        panic!("successful original guard verification");
    };
    let OrFactSearchedProof::ByKnownOrFact(known) = &mut guard.searched_proof else {
        panic!("this original result selected a known-Or citation");
    };
    known
}

fn transported_guard(result: &mut RunLitexCodeResult) -> &mut OrFactSearchProofByKnownOrFact {
    let FactWellDefinedProof::Equality(equal) =
        &mut property(result).assumed_iff_facts[4].well_defined
    else {
        panic!("actual equality clause formation");
    };
    known_call_guard(&mut equal.as_detailed_mut().unwrap().left)
}

#[test]
fn known_or_replays_original_argument_paths_in_source_order() {
    let (mut result, compiler) = checked_source(KNOWN_OR);
    let id = property(&mut result).assumed_iff_facts[3]
        .store_and_infer
        .primary_fact_id();
    let known = transported_guard(&mut result);
    assert_eq!(known.cite_fact_id, id);
    assert_eq!(
        known.why_parameters_of_known_fact_are_equal_to_givens.len(),
        4
    );
    for index in [0, 2] {
        assert!(matches!(
            known.why_parameters_of_known_fact_are_equal_to_givens[index],
            EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(_)
            )
        ));
    }
    let lean = compiler
        .compile_run(&result, "known_or_argument_paths")
        .expect("the original ordered equality paths transport the cited disjunction");
    assert!(lean.contains("Or.elim"));
    assert!(lean.matches(&format!("h_{}", id.value())).count() >= 2);
}

#[test]
fn known_or_replays_the_prior_exist_clause_without_reopening_its_scope() {
    let (mut result, compiler) = checked_source(EXIST_KNOWN_OR);
    let FactWellDefinedProof::ExistFact(exist) =
        &mut property(&mut result).assumed_iff_facts[0].well_defined
    else {
        panic!("original existential clause formation");
    };
    let id = exist.as_detailed_mut().unwrap().assumed_body_facts[0]
        .store_and_infer
        .primary_fact_id();
    let FactWellDefinedProof::Equality(equal) =
        &mut exist.as_detailed_mut().unwrap().assumed_body_facts[1].well_defined
    else {
        panic!("original second existential clause");
    };
    let known = known_call_guard(&mut equal.as_detailed_mut().unwrap().right);
    assert_eq!(known.cite_fact_id, id);
    assert!(known
        .why_parameters_of_known_fact_are_equal_to_givens
        .iter()
        .all(|proof| matches!(
            proof,
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
        )));
    compiler
        .compile_run(&result, "known_or_exist_clause")
        .expect("the exact preceding Or assumption supplies the function guard");
}

#[test]
fn known_or_rejects_a_citation_to_another_fact_family_or_branch_shape() {
    for (clause, expected) in [(0, "Or/KnownCitationFamily"), (2, "Or/KnownShape")] {
        let (mut result, compiler) = checked_source(KNOWN_OR);
        let wrong = property(&mut result).assumed_iff_facts[clause]
            .store_and_infer
            .primary_fact_id();
        transported_guard(&mut result).cite_fact_id = wrong;
        assert_eq!(
            compiler
                .compile_run(&result, "wrong_known_or_citation")
                .unwrap_err()
                .route,
            expected
        );
    }
}

#[test]
fn known_or_rejects_missing_or_future_citations() {
    for future in [false, true] {
        let (mut result, compiler) = checked_source(KNOWN_OR);
        let wrong = if future {
            property(&mut result).assumed_iff_facts[5]
                .store_and_infer
                .primary_fact_id()
        } else {
            FactId::new(u64::MAX)
        };
        transported_guard(&mut result).cite_fact_id = wrong;
        assert_eq!(
            compiler
                .compile_run(&result, "unavailable_known_or_citation")
                .unwrap_err()
                .route,
            if future {
                // The completed local environment retains this fact, but
                // its source producer is later than the current call.
                "FactId/Producer"
            } else {
                "FactId/Resolution"
            }
        );
    }
}

#[test]
fn known_or_rejects_missing_original_argument_evidence() {
    let (mut result, compiler) = checked_source(KNOWN_OR);
    transported_guard(&mut result)
        .why_parameters_of_known_fact_are_equal_to_givens
        .pop();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_known_or_argument")
            .unwrap_err()
            .route,
        "Or/KnownArgumentArity"
    );
}

#[test]
fn known_or_rejects_reordered_original_argument_paths() {
    let (mut result, compiler) = checked_source(KNOWN_OR);
    transported_guard(&mut result)
        .why_parameters_of_known_fact_are_equal_to_givens
        .swap(0, 2);
    assert_eq!(
        compiler
            .compile_run(&result, "reordered_known_or_arguments")
            .unwrap_err()
            .route,
        "Equality/PathOrder"
    );
}

#[test]
fn or_replays_integer_coverage_and_exact_known_forall_instantiation() {
    let (result, compiler) = checked();
    let lean = compiler
        .compile_run(&result, "original_or_coverage")
        .expect("Or original routes");
    assert!(lean.contains("Litex.integerSuccessorTail"));
    assert!(lean.contains("Or.elim"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn or_rejects_missing_original_branch_formation() {
    let (mut result, compiler) = checked();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[2]
    else {
        panic!("source Or");
    };
    let VerifyFactResult::OrFact(verify) = &mut fact.verify_result else {
        panic!("Or result");
    };
    let VerifyOrFactResult::Success(proof) = verify.as_mut() else {
        panic!("Or success");
    };
    proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .branches
        .clear();
    assert!(compiler
        .compile_run(&result, "missing_or_wd")
        .unwrap_err()
        .route
        .contains("FormationArity"));
}

#[test]
fn or_rejects_changed_original_branch_subject() {
    let (mut result, compiler) = checked();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = &mut result.statement_results[2]
    else {
        panic!("source Or");
    };
    let VerifyFactResult::OrFact(verify) = &mut fact.verify_result else {
        panic!("Or result");
    };
    let VerifyOrFactResult::Success(proof) = verify.as_mut() else {
        panic!("Or success");
    };
    proof.fact.facts.swap(0, 1);
    assert!(compiler.compile_run(&result, "changed_or_subject").is_err());
}

#[test]
fn or_integer_tail_rejects_swapped_original_memberships() {
    use crate::execute::execute_proof_block_stmt::{
        ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
    };
    let (mut result, compiler) = checked();
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &mut result.statement_results[0]
    else {
        panic!("original claim");
    };
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("universal claim");
    };
    let VerifyFactResult::OrFact(verify) = &mut body.conclusion_proofs[0] else {
        panic!("original disjunction");
    };
    let VerifyOrFactResult::Success(proof) = verify.as_mut() else {
        panic!("successful disjunction");
    };
    let OrFactSearchedProof::ByBuiltinRule(OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(
        selected,
    )) = &mut proof.searched_proof
    else {
        panic!("selected integer coverage");
    };
    std::mem::swap(&mut selected.subject_in_z, &mut selected.base_in_z);
    assert_eq!(
        compiler
            .compile_run(&result, "swapped_integer_memberships")
            .unwrap_err()
            .route,
        "Or/IntegerTailMembership"
    );
}
