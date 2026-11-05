use crate::execute::execute_def_thm_stmt::{
    ExecDefThmBodyProof, ExecDefThmForallProof, ExecDefThmStmtResult, ExecDefThmStmtSuccess,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::VerifyAtomicExceptEqualityFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferFunctionContinuousAtDefinitionResult,
    InferFunctionContinuousAtFactResult, InferResult,
};

const SOURCES: [&str; 5] = [
    r#"# Cite positive and negative two-sided continuity facts on their original real function domain.
thm at_continuity_citation:
    ? forall f fn(x R) R, p R:
        $is_continuous_at(f,p)
        =>:
            $is_continuous_at(f,p)

thm at_discontinuity_citation:
    ? forall f fn(x R) R, p R:
        not $is_continuous_at(f,p)
        =>:
            not $is_continuous_at(f,p)
"#,
    r#"# Cite positive and negative left-sided continuity facts on their original real function domain.
thm left_continuity_citation:
    ? forall f fn(x R) R, p R:
        $is_continuous_left(f,p)
        =>:
            $is_continuous_left(f,p)

thm left_discontinuity_citation:
    ? forall f fn(x R) R, p R:
        not $is_continuous_left(f,p)
        =>:
            not $is_continuous_left(f,p)
"#,
    r#"# Cite positive and negative right-sided continuity facts on their original real function domain.
thm right_continuity_citation:
    ? forall f fn(x R) R, p R:
        $is_continuous_right(f,p)
        =>:
            $is_continuous_right(f,p)

thm right_discontinuity_citation:
    ? forall f fn(x R) R, p R:
        not $is_continuous_right(f,p)
        =>:
            not $is_continuous_right(f,p)
"#,
    r#"# Semantic equality transports continuity between equivalent functions and points.
thm continuity_semantic_transport:
    ? forall f,g fn(x R) R, p,q R:
        f=g
        p=q
        $is_continuous_at(f,p)
        =>:
            $is_continuous_at(g,q)
"#,
    r#"# Cite continuity on a punctured real function domain with its original nonzero condition.
thm guarded_continuity_citation:
    ? forall f fn(x R: x != 0) R, p R:
        p != 0
        $is_continuous_at(f,p)
        =>:
            $is_continuous_at(f,p)
"#,
];
fn theorem(run: &mut RunLitexCodeResult) -> &mut ExecDefThmStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    p
}
fn body(p: &mut ExecDefThmStmtSuccess) -> &mut ExecDefThmForallProof {
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall")
    };
    p
}
fn definition(p: &mut ExecDefThmForallProof) -> &mut InferFunctionContinuousAtDefinitionResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionContinuousAtFact(rules))) =
        &mut p.assumed_dom_facts[0].store_and_infer.infer
    else {
        panic!("continuity inference")
    };
    let [InferFunctionContinuousAtFactResult::Definition(p)] = rules.as_mut_slice() else {
        panic!("definition")
    };
    p
}
#[test]
fn continuity_definition_rejects_missing_or_changed_domain_evidence() {
    for mutation in 0..4 {
        let (mut run, c) = super::execute(SOURCES[0]);
        let p = definition(body(theorem(&mut run)));
        match mutation {
            0 => p.source_fact_id = p.derived[0].primary_fact_id(),
            1 => p.derived.clear(),
            2 => p.function_domain.domain = Obj::StandardSet(StandardSet::C),
            _ => {
                let VerifyFactResult::AtomicExceptEquality(proof) =
                    p.function_domain.input_real.as_mut()
                else {
                    panic!("subset proof")
                };
                let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
                    panic!("success")
                };
                let AtomicFact::SubsetFact(f) = &mut proof.fact else {
                    panic!("subset")
                };
                f.right = Obj::StandardSet(StandardSet::C);
            }
        }
        c.compile_run(&run, "changed_continuity_domain")
            .expect_err("exact original domain evidence");
    }
}
#[test]
fn continuity_requires_original_point_membership() {
    let (mut run, c) = super::execute(SOURCES[0]);
    let FactWellDefinedProof::AtomicExceptEquality(proof) =
        &mut body(theorem(&mut run)).assumed_dom_facts[0].well_defined
    else {
        panic!("continuity WD")
    };
    let PredicateDomainProof::FunctionAnalysis(p) =
        &mut proof.as_detailed_mut().unwrap().predicate_domain
    else {
        panic!("analysis WD")
    };
    p.requirements.clear();
    c.compile_run(&run, "missing_continuity_point")
        .expect_err("original point membership");
}

const LAWS: [&str; 7] = [
    r#"# Derive at continuity from its epsilon-delta control on the complete real domain.
thm explicit_at_continuity_intro:
    ? forall f fn(x R) R, p R:
        forall epsilon R+:
            exist delta R+ st {{x R: abs(x-p)<delta} $subset preimage_set(f,{v R:abs(v-f(p))<epsilon})}
        =>:
            $is_continuous_at(f,p)
    by thm fn_continuous_at_from_epsilon(f,p) => $is_continuous_at(f,p)
"#,
    r#"# Obtain an epsilon-delta control from at continuity on the complete real domain.
thm explicit_at_continuity_control:
    ? forall f fn(x R) R, p R, epsilon R+:
        $is_continuous_at(f,p)
        =>:
            exist delta R+ st {{x R: abs(x-p)<delta} $subset preimage_set(f,{v R:abs(v-f(p))<epsilon})}
    release thm fn_continuous_at_control(f,p,epsilon)
"#,
    r#"# Derive left continuity from its epsilon-delta control on the complete real domain.
thm explicit_left_continuity_intro:
    ? forall f fn(x R) R, p R:
        forall epsilon R+:
            exist delta R+ st {{x R: x<=p, p-x<delta} $subset preimage_set(f,{v R:abs(v-f(p))<epsilon})}
        =>:
            $is_continuous_left(f,p)
    by thm fn_continuous_left_from_epsilon(f,p) => $is_continuous_left(f,p)
"#,
    r#"# Obtain an epsilon-delta control from left continuity on the complete real domain.
thm explicit_left_continuity_control:
    ? forall f fn(x R) R, p R, epsilon R+:
        $is_continuous_left(f,p)
        =>:
            exist delta R+ st {{x R: x<=p, p-x<delta} $subset preimage_set(f,{v R:abs(v-f(p))<epsilon})}
    release thm fn_continuous_left_control(f,p,epsilon)
"#,
    r#"# Derive right continuity from its epsilon-delta control on the complete real domain.
thm explicit_right_continuity_intro:
    ? forall f fn(x R) R, p R:
        forall epsilon R+:
            exist delta R+ st {{x R: p<=x, x-p<delta} $subset preimage_set(f,{v R:abs(v-f(p))<epsilon})}
        =>:
            $is_continuous_right(f,p)
    by thm fn_continuous_right_from_epsilon(f,p) => $is_continuous_right(f,p)
"#,
    r#"# Obtain an epsilon-delta control from right continuity on the complete real domain.
thm explicit_right_continuity_control:
    ? forall f fn(x R) R, p R, epsilon R+:
        $is_continuous_right(f,p)
        =>:
            exist delta R+ st {{x R: p<=x, x-p<delta} $subset preimage_set(f,{v R:abs(v-f(p))<epsilon})}
    release thm fn_continuous_right_control(f,p,epsilon)
"#,
    r#"# Derive at continuity from its epsilon-delta control on the complete real domain.
thm at_continuity_from_definition:
    ? forall f fn(x R) R, p R:
        forall epsilon R+:
            exist delta R+ st {{x R: abs(x-p)<delta} $subset preimage_set(f,{v R:abs(v-f(p))<epsilon})}
        =>:
            $is_continuous_at(f,p)
"#,
];
const FORMULAS: [&str; 6] = [
    r#"# A function equal to the constant formula is at-continuous on its complete real domain.
thm at_constant_continuity:
    ? forall f fn(x R) R, p R, c R:
        forall x R:
            f(x)=c
        =>:
            $is_continuous_at(f,p)
    by thm fn_continuous_at_constant(f,p,c) => $is_continuous_at(f,p)
"#,
    r#"# A function equal to the identity formula is at-continuous on its complete real domain.
thm at_identity_continuity:
    ? forall f fn(x R) R, p R:
        forall x R:
            f(x)=x
        =>:
            $is_continuous_at(f,p)
    by thm fn_continuous_at_identity(f,p) => $is_continuous_at(f,p)
"#,
    r#"# A function equal to the constant formula is left-continuous on its complete real domain.
thm left_constant_continuity:
    ? forall f fn(x R) R, p R, c R:
        forall x R:
            f(x)=c
        =>:
            $is_continuous_left(f,p)
    by thm fn_continuous_left_constant(f,p,c) => $is_continuous_left(f,p)
"#,
    r#"# A function equal to the identity formula is left-continuous on its complete real domain.
thm left_identity_continuity:
    ? forall f fn(x R) R, p R:
        forall x R:
            f(x)=x
        =>:
            $is_continuous_left(f,p)
    by thm fn_continuous_left_identity(f,p) => $is_continuous_left(f,p)
"#,
    r#"# A function equal to the constant formula is right-continuous on its complete real domain.
thm right_constant_continuity:
    ? forall f fn(x R) R, p R, c R:
        forall x R:
            f(x)=c
        =>:
            $is_continuous_right(f,p)
    by thm fn_continuous_right_constant(f,p,c) => $is_continuous_right(f,p)
"#,
    r#"# A function equal to the identity formula is right-continuous on its complete real domain.
thm right_identity_continuity:
    ? forall f fn(x R) R, p R:
        forall x R:
            f(x)=x
        =>:
            $is_continuous_right(f,p)
    by thm fn_continuous_right_identity(f,p) => $is_continuous_right(f,p)
"#,
];
#[test]
fn continuity_certificates_reject_changed_side_point_or_missing_stage() {
    for source in LAWS[..6].iter().chain(FORMULAS.iter()) {
        for mutation in 0..6 {
            let (mut run, c) = super::execute(source);
            use crate::execute::{
                execute_by_stmt::{
                    ExecByStmtResult, ExecByThmStmtResult, ExecReleaseThmStmtResult,
                },
                ExecReleaseAndExpandStmtResult,
            };
            let (dom_proofs, dom_stores, conclusions_wd, derivation, builtin) =
                match &mut body(theorem(&mut run)).proof_steps[0] {
                    ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) => (
                        &mut p.dom_proofs,
                        &mut p.dom_stores,
                        &mut p.conclusions_wd,
                        &mut p.theorem_derivation,
                        p.builtin.as_mut().unwrap(),
                    ),
                    ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                        ExecReleaseThmStmtResult::Success(p),
                    )) => (
                        &mut p.dom_proofs,
                        &mut p.dom_stores,
                        &mut p.conclusions_wd,
                        &mut p.theorem_derivation,
                        p.builtin.as_mut().unwrap(),
                    ),
                    _ => panic!("builtin call"),
                };
            match mutation {
                0 => {
                    dom_proofs.pop();
                }
                1 => dom_stores.clear(),
                2 => conclusions_wd.clear(),
                3 => {
                    *derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
                4 => {
                    let b = builtin;
                    use crate::builtin_theorem::BuiltinTheoremId::*;
                    let f = if matches!(
                        b.theorem,
                        FnContinuousAtControl | FnContinuousLeftControl | FnContinuousRightControl
                    ) {
                        &mut b.requirements[4]
                    } else {
                        &mut b.conclusions[0]
                    };
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) = f else {
                        panic!("continuity")
                    };
                    f.side = if f.side == RealApproachSide::Both {
                        RealApproachSide::Left
                    } else {
                        RealApproachSide::Both
                    };
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut builtin.requirements[3]
                    else {
                        panic!("point domain")
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
            }
            c.compile_run(&run, "changed_continuity_certificate")
                .expect_err("original stages, point and approach side");
        }
    }
}
