use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::{
        less::LessFactSearchProofByBuiltinRule, less_equal::LessEqualFactSearchProofByBuiltinRule,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const EXP_LT: &str = r#"# exp preserves strict order on its real domain.
claim:
    ? forall x R, y R:
        x < y
        =>:
            exp(x) < exp(y)
    exp(x) < exp(y)
"#;
const EXP_LE: &str = r#"# exp preserves weak order on its real domain.
claim:
    ? forall x R, y R:
        x <= y
        =>:
            exp(x) <= exp(y)
    exp(x) <= exp(y)
"#;
const LN_LT: &str = r#"# ln preserves strict order on its real domain.
claim:
    ? forall x R+, y R+:
        x < y
        =>:
            ln(x) < ln(y)
    ln(x) < ln(y)
"#;
const LN_LE: &str = r#"# ln preserves weak order on its real domain.
claim:
    ? forall x R+, y R+:
        x <= y
        =>:
            ln(x) <= ln(y)
    ln(x) <= ln(y)
"#;
const EXP_LT_REV: &str = r#"# exp reflects strict order on its real domain.
claim:
    ? forall x R, y R:
        exp(x) < exp(y)
        =>:
            x < y
    x < y
"#;
const EXP_LE_REV: &str = r#"# exp reflects weak order on its real domain.
claim:
    ? forall x R, y R:
        exp(x) <= exp(y)
        =>:
            x <= y
    x <= y
"#;
const LN_LT_REV: &str = r#"# ln reflects strict order on its real domain.
claim:
    ? forall x R+, y R+:
        ln(x) < ln(y)
        =>:
            x < y
    x < y
"#;
const LN_LE_REV: &str = r#"# ln reflects weak order on its real domain.
claim:
    ? forall x R+, y R+:
        ln(x) <= ln(y)
        =>:
            x <= y
    x <= y
"#;

fn selected_premise(run: &mut RunLitexCodeResult) -> (&mut VerifyFactResult, &'static str) {
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
    let VerifyFactResult::AtomicExceptEquality(result) = &mut stmt.verify_result else {
        panic!("atomic")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified")
    };
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::ExpStrictMonotone(p),
            ),
        ) => (&mut p.argument_order, "Litex.expLtIff"),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::LnStrictMonotone(p),
            ),
        ) => (&mut p.argument_order, "Litex.lnLtIff"),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::ExpWeakMonotone(p),
            ),
        ) => (&mut p.argument_order, "Litex.expLeIff"),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::LnWeakMonotone(p),
            ),
        ) => (&mut p.argument_order, "Litex.lnLeIff"),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::ExpStrictOrderReflection(p),
            ),
        ) => (&mut p.image_order, "Litex.expLtIff"),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                LessFactSearchProofByBuiltinRule::LnStrictOrderReflection(p),
            ),
        ) => (&mut p.image_order, "Litex.lnLtIff"),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::ExpWeakOrderReflection(p),
            ),
        ) => (&mut p.image_order, "Litex.expLeIff"),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::LnWeakOrderReflection(p),
            ),
        ) => (&mut p.image_order, "Litex.lnLeIff"),
        _ => panic!("selected exponential or logarithm monotonicity"),
    }
}

#[test]
fn exp_ln_monotonicity_replays_selected_order() {
    for source in [
        EXP_LT, EXP_LE, LN_LT, LN_LE, EXP_LT_REV, EXP_LE_REV, LN_LT_REV, LN_LE_REV,
    ] {
        let (mut run, compiler) = super::execute(source);
        let (_, theorem) = selected_premise(&mut run);
        assert!(compiler
            .compile_run(&run, "exp_ln_order")
            .expect(source)
            .contains(theorem));
    }
}

#[test]
fn exp_ln_monotonicity_rejects_changed_argument_order() {
    for source in [
        EXP_LT, EXP_LE, LN_LT, LN_LE, EXP_LT_REV, EXP_LE_REV, LN_LT_REV, LN_LE_REV,
    ] {
        let (mut run, compiler) = super::execute(source);
        let (premise, _) = selected_premise(&mut run);
        let VerifyFactResult::AtomicExceptEquality(result) = premise else {
            panic!("atomic premise")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
            panic!("verified premise")
        };
        match &mut proof.fact {
            AtomicFact::LessFact(f) => {
                f.right = Obj::Literal(Literal::Number(Number::new("3".into())))
            }
            AtomicFact::LessEqualFact(f) => {
                f.right = Obj::Literal(Literal::Number(Number::new("3".into())))
            }
            _ => panic!("order premise"),
        }
        compiler
            .compile_run(&run, "invalid_exp_ln_order")
            .expect_err("changed premise");
    }
}

#[test]
fn exp_ln_monotonicity_rejects_missing_goal_wd() {
    for source in [
        EXP_LT, EXP_LE, LN_LT, LN_LE, EXP_LT_REV, EXP_LE_REV, LN_LT_REV, LN_LE_REV,
    ] {
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Success(claim),
        )) = &mut run.statement_results[0]
        else {
            panic!("claim")
        };
        let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
            panic!("forall")
        };
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &mut body.proof_steps[0]
        else {
            panic!("fact")
        };
        let VerifyFactResult::AtomicExceptEquality(result) = &mut stmt.verify_result else {
            panic!("atomic")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
            panic!("verified")
        };
        proof
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter
            .clear();
        compiler
            .compile_run(&run, "missing_exp_ln_order_wd")
            .expect_err("missing goal WD");
    }
}

#[test]
fn logarithm_order_requires_positive_arguments() {
    let source = "ln(0) <= ln(1)";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
