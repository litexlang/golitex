use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave6::AbsNonnegEqualsSelfBuiltinRuleProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByBuiltinRule;
use crate::execute::execute_proof_block_stmt::{ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult};
use crate::prelude::*;

const STRICT: &str =
    include_str!("../../../lean/examples/absolute_value_of_positive/statement.lit");

fn requirement(run: &mut RunLitexCodeResult) -> &mut AbsNonnegEqualsSelfBuiltinRuleProof {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        p,
    ))) = &mut run.statement_results[0]
    else {
        panic!("claim")
    };
    let ExecClaimBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = p.proof_steps.last_mut().unwrap()
    else {
        panic!("fact")
    };
    let VerifyFactResult::Equality(p) = &mut p.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(p) = p.as_mut() else {
        panic!("accepted")
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(p),
    ) = &mut p.searched_proof
    else {
        panic!("absolute value rule")
    };
    p
}

#[test]
fn absolute_value_replays_strict_or_weak_nonnegative_evidence() {
    let (mut run, compiler) = super::execute(STRICT);
    let p = requirement(&mut run);
    assert!(matches!(
        &super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]).fact,
        AtomicFact::LessFact(_)
    ));
    let lean = compiler.compile_run(&run, "absolute_positive").unwrap();
    assert!(lean.contains("Litex.ltToLe"));
    assert!(lean.contains("Litex.absOfNonnegative"));
    let weak = "claim:\n    ? forall a R:\n        0 <= a\n        =>:\n            abs(a) = a\n    abs(a) = a";
    let (run, compiler) = super::execute(weak);
    assert!(compiler
        .compile_run(&run, "absolute_nonnegative")
        .unwrap()
        .contains("Litex.absOfNonnegative"));
}

#[test]
fn absolute_value_rejects_missing_or_other_argument_evidence() {
    for missing in [true, false] {
        let (mut run, compiler) = super::execute(STRICT);
        let p = requirement(&mut run);
        if missing {
            p.proof_of_requirement_facts.clear();
        } else {
            let AtomicFact::LessFact(f) =
                &mut super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]).fact
            else {
                panic!("strict positivity")
            };
            f.right = Obj::Literal(Literal::Number(Number::new("5".into())));
        }
        compiler
            .compile_run(&run, "wrong_absolute_argument")
            .expect_err("actual argument proof required");
    }
}

#[test]
fn absolute_value_identity_is_not_valid_for_a_negative_argument() {
    let source = "have a R = -1\nabs(a) = a";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(source)
            .unwrap()
            .success
    );
}
