use super::LitexToLeanCompiler;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::LimitOperatorObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::sequence_limit::SequenceConvergenceProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_sequence_limsup::SequenceLimsupEqualityProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
use crate::prelude::*;

const SELECTED: &str = r#"# A finite limsup candidate identifies its proof-consuming selector and its real codomain.
forall a seq(R), L R:
    $has_seq_limsup(a,L)
    =>:
        limsup(a) = L
        limsup(a) $in R
"#;
fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let body = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut body.proved_then_facts[0].verify_result)
}
#[test]
fn finite_extremum_wd_rejects_another_sequence() {
    let (mut run, compiler) = super::execute(SELECTED);
    let left = &mut equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left;
    let ObjWellDefinedProof::Detailed(p) = left else {
        panic!("detailed WD")
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::LimitOperator(
                LimitOperatorObjWellDefinedProofByDef::SequenceLimsup(p),
            ),
        ..
    } = p.as_mut()
    else {
        panic!("limsup WD")
    };
    let SequenceConvergenceProof::Candidate(candidate) = &mut p.convergence else {
        panic!("candidate")
    };
    let AtomicFact::HasSequenceLimsupFact(f) = &mut candidate.fact else {
        panic!("limsup")
    };
    f.sequence = Obj::Literal(Literal::Number(Number::new("9".into())));
    compiler
        .compile_run(&run, "bad_sequence")
        .expect_err("wrong WD subject");
}
#[test]
fn finite_extremum_wd_rejects_a_changed_existence_candidate() {
    let source="forall a seq(R):\n    exist L R st {$has_seq_limsup(a,L)}\n    =>:\n        limsup(a)=limsup(a)";
    let (mut run, compiler) = super::execute(source);
    let left = &mut equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left;
    let ObjWellDefinedProof::Detailed(p) = left else {
        panic!("detailed WD")
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::LimitOperator(
                LimitOperatorObjWellDefinedProofByDef::SequenceLimsup(p),
            ),
        ..
    } = p.as_mut()
    else {
        panic!("limsup WD")
    };
    let SequenceConvergenceProof::Existence {
        fact: Fact::ExistFact(f),
        ..
    } = &mut p.convergence
    else {
        panic!("existence")
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::HasSequenceLimsupFact(candidate)) =
        &mut f.facts[0]
    else {
        panic!("candidate")
    };
    candidate.value = Obj::Literal(Literal::Number(Number::new("9".into())));
    compiler
        .compile_run(&run, "bad_existence")
        .expect_err("must quantify the selected value");
}
#[test]
fn finite_extremum_equality_rejects_invalid_candidate_citation() {
    let (mut run, compiler) = super::execute(SELECTED);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SequenceLimsup(
        SequenceLimsupEqualityProof::SelectedValue(p),
    )) = &mut equality(&mut run).searched_proof
    else {
        panic!("selected")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
        p.candidate.searched_proof.as_mut()
    else {
        panic!("citation")
    };
    c.cite_fact_id = FactId::new(u64::MAX);
    compiler
        .compile_run(&run, "bad_citation")
        .expect_err("unknown candidate citation");
}
#[test]
fn finite_extrema_without_selection_are_not_well_defined() {
    for name in ["limsup", "liminf"] {
        let source = format!("forall a seq(R):\n    {name}(a)={name}(a)");
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
        let mut runtime = Runtime::new(command);
        let result = runtime.run_litex_code(&source).unwrap();
        assert!(!result.success);
        LitexToLeanCompiler::new(runtime)
            .compile_run(&result, "missing_extremum")
            .expect_err("failed source run");
    }
}
#[test]
fn finite_extremum_definition_rejects_deleted_tail_hits() {
    use crate::execute::execute_by_stmt::ExecByDefStmtResult;
    use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition as Definition,
        BuiltinPropDefinitionProof as Builtin,
    };
    use crate::execute::ExecDefinitionStmtResult;
    let source = r#"# The finite limsup definition requires both an eventual bound and hits on every tail.
thm limsup_from_two_clauses:
    ? forall a seq(R), L R:
        forall epsilon R+:
            exist n0 N+ st {{n N+:n>=n0} $subset preimage_set(a,{v R:v<L+epsilon})}
        forall epsilon R+, n0 N+:
            exist n N+ st {n>=n0 and L-epsilon<a(n)}
        =>:
            $has_seq_limsup(a,L)
    by def $has_seq_limsup(a,L)
"#;
    let (mut run, compiler) = super::execute(source);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
        panic!("forall")
    };
    let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
        &mut body.proof_steps[0]
    else {
        panic!("by def")
    };
    let p = super::atomic_proof_mut(&mut p.proof);
    let AtomicExceptEqualityFactSearchedProof::ByDefinition(Definition::BuiltinProp(
        Builtin::SequenceLimsup(p),
    )) = &mut p.searched_proof
    else {
        panic!("extremum definition")
    };
    p.requirement_facts.pop();
    p.proof_of_requirement_facts.pop();
    compiler
        .compile_run(&run, "bound_without_hits")
        .expect_err("an eventual bound alone is insufficient");
}
#[test]
fn finite_extremum_explicit_theorem_rejects_missing_stage_or_wrong_formula() {
    use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
    use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
    use crate::execute::ExecDefinitionStmtResult;
    use crate::execute::ExecReleaseAndExpandStmtResult;
    for missing in [true, false] {
        let source = r#"# A constant real sequence has finite limsup equal to its value.
thm limsup_constant:
    ? forall a seq(R), L R:
        forall n N+:
            a(n)=L
        =>:
            $has_seq_limsup(a,L)
    release thm seq_limsup_constant(a,L)
"#;
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) = &mut run.statement_results[0]
        else {
            panic!("theorem")
        };
        let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
            panic!("forall")
        };
        let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
            ExecReleaseThmStmtResult::Success(p),
        )) = &mut body.proof_steps[0]
        else {
            panic!("release")
        };
        if missing {
            p.dom_proofs.pop();
        } else {
            let Fact::ForallFact(f) = &mut p.builtin.as_mut().unwrap().requirements[2] else {
                panic!("formula")
            };
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                &mut f.then_facts[0]
            else {
                panic!("formula equality")
            };
            eq.right = Obj::Literal(Literal::Number(Number::new("99".into())));
        }
        compiler
            .compile_run(&run, "invalid_extremum_theorem")
            .expect_err("original formula and ordered proof stages required");
    }
}
