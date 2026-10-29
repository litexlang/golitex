use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{result::EqualFactSearchedProof, EqualitySearchProofByBuiltinRule};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_sequence_limit::SequenceLimitEqualityProof;
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::prelude::*;

const SELECTED: &str =
    include_str!("../../../lean/examples/sequence_limit_selected_value/statement.lit");

fn selected(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess{
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("forall")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &mut body.proof_steps[0] else {
        panic!("fact")
    };
    let VerifyFactResult::Equality(result) = &mut stmt.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(proof) = result.as_mut() else {
        panic!("verified")
    };
    proof
}

#[test]
fn sequence_limit_replays_candidate_and_both_signature_shapes() {
    for source in [
        SELECTED,
        include_str!("../../../lean/examples/sequence_limit_function_signature/statement.lit"),
        include_str!("../../../lean/examples/sequence_limit_reverse_equality/statement.lit"),
        include_str!("../../../lean/examples/sequence_limit_exists_object/statement.lit"),
        include_str!("../../../lean/examples/sequence_limit_real/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "sequence_limit").expect(source);
        assert!(lean.contains("Litex.sequenceLimit"));
    }
    let (mut run, _) = super::execute(SELECTED);
    assert!(matches!(
        selected(&mut run).searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SequenceLimit(
            SequenceLimitEqualityProof::SelectedValue(_)
        ))
    ));
}

#[test]
fn sequence_limit_rejects_changed_candidate_and_wd() {
    for change in ["candidate", "sequence", "wd"] {
        let (mut run, compiler) = super::execute(SELECTED);
        let equality = selected(&mut run);
        if change == "wd" {
            let wd = equality.well_defined_proof.as_detailed_mut().unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
            compiler
                .compile_run(&run, "invalid_sequence_limit")
                .expect_err(change);
            continue;
        }
        let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SequenceLimit(
            SequenceLimitEqualityProof::SelectedValue(p),
        )) = &mut equality.searched_proof
        else {
            panic!("selected limit")
        };
        let AtomicFact::HasSequenceLimitFact(f) = &mut p.candidate.fact else {
            panic!("limit fact")
        };
        match change {
            "candidate" => {
                f.value = Obj::Literal(Literal::Number(Number::new("9".into())));
            }
            _ => {
                f.sequence = Obj::Literal(Literal::Number(Number::new("9".into())));
            }
        }
        compiler
            .compile_run(&run, "invalid_sequence_limit")
            .expect_err(change);
    }
}

#[test]
fn sequence_limit_without_convergence_is_not_well_defined() {
    let source = "claim:\n    ? forall a seq(R):\n        $is_set(lim(a))\n    $is_set(lim(a))";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}

#[test]
fn sequence_limit_uniqueness_replays_both_candidate_citations() {
    for source in [
        include_str!("../../../lean/examples/sequence_limit_unique/statement.lit"),
        include_str!(
            "../../../lean/examples/sequence_limit_unique_function_signature/statement.lit"
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert!(matches!(
            selected(&mut run).searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SequenceLimit(
                SequenceLimitEqualityProof::Uniqueness(_)
            ))
        ));
        assert!(compiler
            .compile_run(&run, "sequence_unique")
            .expect(source)
            .contains("Litex.sequenceLimitCandidatesEqual"));
    }
}

#[test]
fn sequence_limit_uniqueness_rejects_a_changed_candidate() {
    let source = include_str!("../../../lean/examples/sequence_limit_unique/statement.lit");
    let (mut run, compiler) = super::execute(source);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SequenceLimit(
        SequenceLimitEqualityProof::Uniqueness(p),
    )) = &mut selected(&mut run).searched_proof
    else {
        panic!("uniqueness proof")
    };
    let AtomicFact::HasSequenceLimitFact(f) = &mut p.right.fact else {
        panic!("candidate")
    };
    f.sequence = Obj::Literal(Literal::Number(Number::new("9".into())));
    compiler
        .compile_run(&run, "invalid_sequence_unique")
        .expect_err("different sequence");
}

#[test]
fn sequence_limit_uniqueness_rejects_invalid_citation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
    let source = include_str!("../../../lean/examples/sequence_limit_unique/statement.lit");
    let (mut run, compiler) = super::execute(source);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SequenceLimit(
        SequenceLimitEqualityProof::Uniqueness(p),
    )) = &mut selected(&mut run).searched_proof
    else {
        panic!("uniqueness proof")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
        p.right.searched_proof.as_mut()
    else {
        panic!("known citation")
    };
    citation.cite_fact_id = FactId::new(u64::MAX);
    compiler
        .compile_run(&run, "invalid_sequence_unique_citation")
        .expect_err("invalid citation");
}
