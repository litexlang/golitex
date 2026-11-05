use crate::execute::execute_by_stmt::{
    ExecByStmtResult, ExecByThmStmtResult, ExecByThmStmtSuccess, ExecReleaseThmStmtResult,
    ExecReleaseThmStmtSuccess,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::{ExecDefinitionStmtResult, ExecReleaseAndExpandStmtResult};
use crate::prelude::*;

const IDENTITY: &str = r#"# Prove the identity function limit from its formula and real-domain accumulation.
have fn identity_limit_example(x R) R = x
release thm fn_limit_at_real_accumulation(2)
by thm fn_limit_at_identity(identity_limit_example,2) => $has_limit_at(identity_limit_example,2,2)
"#;
const ACCUMULATION: &str = r#"# The real line has points arbitrarily close from the at approach.
thm reals_accumulate_at:
    ? forall p R, r R+:
        exist x R st {0<(abs(x-p)) and (abs(x-p))<r}
    release thm fn_limit_at_real_accumulation(p)
"#;

fn identity(run: &mut RunLitexCodeResult) -> &mut ExecByThmStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
        &mut run.statement_results[2]
    else {
        panic!("identity invocation")
    };
    p
}
fn accumulation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("accumulation theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut p.proof_steps[0]
    else {
        panic!("real accumulation invocation")
    };
    p
}

#[test]
fn real_accumulation_rejects_missing_point_proof_and_altered_witness_domain() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(ACCUMULATION);
        let p = accumulation(&mut run);
        match mutation {
            0 => p.dom_proofs.clear(),
            1 => p.stored_wd.clear(),
            2 => {
                let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().conclusions[0] else {
                    panic!("radius")
                };
                let ExistOrAndChainAtomicFact::ExistFact(e) = &mut f.then_facts[0] else {
                    panic!("witness")
                };
                e.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::Q));
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "invalid_real_accumulation")
            .expect_err("exact source point, witness domain and caller WD");
    }
}

#[test]
fn identity_limit_rejects_missing_domain_or_altered_pointwise_equation() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(IDENTITY);
        let p = identity(&mut run);
        match mutation {
            0 => {
                p.dom_proofs.pop();
            }
            1 => {
                let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[6] else {
                    panic!("identity formula")
                };
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(e)) =
                    &mut f.then_facts[0]
                else {
                    panic!("equation")
                };
                e.right = Obj::Literal(Literal::Number(Number::new("3".into())));
            }
            2 => {
                let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f)) =
                    &mut p.builtin.as_mut().unwrap().conclusions[0]
                else {
                    panic!("limit")
                };
                f.value = Obj::Literal(Literal::Number(Number::new("3".into())));
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "invalid_identity_limit")
            .expect_err("identity value equals the original approach point");
    }
}
