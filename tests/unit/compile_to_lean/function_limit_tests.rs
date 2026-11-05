use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_function_limit::FunctionLimitEqualityProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FunctionLimitApproachWellDefinedProof, FunctionLimitObjWellDefinedProof, LimitOperatorObjWellDefinedProofByDef,
    ObjWellDefinedProofByDef,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SELECTED: &str = r#"# A proved finite real function-limit candidate determines fn_lim(f,x0).
claim:
    ? forall f fn(x R) R, x0 R, L R:
        $has_limit_at(f,x0,L)
        =>:
            fn_lim(f,x0) = L
    fn_lim(f,x0) = L
"#;
const UNIQUE: &str = r#"# Two finite real limits of the same function at the same point are equal.
claim:
    ? forall f fn(x R) R, x0 R, L R, K R:
        $has_limit_at(f,x0,L)
        $has_limit_at(f,x0,K)
        =>:
            L = K
    L = K
"#;

fn equality(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess{
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
    let VerifyFactResult::Equality(proof) = &mut stmt.verify_result else {
        panic!("equality")
    };
    let VerifyEqualityResult::Success(proof) = proof.as_mut() else {
        panic!("verified")
    };
    proof
}

fn limit_wd(run: &mut RunLitexCodeResult) -> &mut FunctionLimitObjWellDefinedProof {
    let wd = equality(run).well_defined_proof.as_detailed_mut().unwrap();
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::LimitOperator(LimitOperatorObjWellDefinedProofByDef::Function(
                proof,
            )),
        ..
    } = wd.left.as_detailed_mut().unwrap()
    else {
        panic!("limit WD")
    };
    proof
}

#[test]
fn function_limit_replays_the_selected_uniqueness_rule() {
    let (mut run, compiler) = super::execute(UNIQUE);
    assert!(matches!(
        equality(&mut run).searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::FunctionLimit(
            FunctionLimitEqualityProof::Uniqueness(_)
        ))
    ));
    assert!(compiler
        .compile_run(&run, "function_limit_unique")
        .unwrap()
        .contains("Litex.finiteFunctionLimitCandidatesEqual"));
}

#[test]
fn function_limit_rejects_a_changed_point_or_direction() {
    for direction in [false, true] {
        let (mut run, compiler) = super::execute(SELECTED);
        let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::FunctionLimit(
            FunctionLimitEqualityProof::SelectedValue(p),
        )) = &mut equality(&mut run).searched_proof
        else {
            panic!("selected")
        };
        let AtomicFact::HasFunctionLimitFact(candidate) = &mut p.candidate.fact else {
            panic!("candidate")
        };
        candidate.approach = if direction {
            LimitApproach::FromLeft(candidate.approach.point().unwrap().clone().into())
        } else {
            LimitApproach::AtPoint(Obj::Literal(Literal::Number(Number::new("9".into()))).into())
        };
        compiler
            .compile_run(&run, "changed_candidate")
            .expect_err("candidate approach differs");
    }
}

#[test]
fn function_limit_rejects_missing_original_point_wd() {
    let (mut run, compiler) = super::execute(SELECTED);
    let proof = limit_wd(&mut run);
    let FunctionLimitApproachWellDefinedProof::Finite { point_wd } = &mut proof.approach_wd else {
        panic!("finite")
    };
    std::mem::swap(point_wd, &mut proof.function_wd);
    compiler
        .compile_run(&run, "wrong_point_wd")
        .expect_err("original child WD required");
}

#[test]
fn function_limit_rejects_a_changed_effective_domain() {
    let source = r#"# A proved finite real function-limit candidate determines fn_lim(f,x0).
claim:
    ? forall f fn(x R: x != 0) R, x0 R, L R:
        $has_limit_at(f,x0,L)
        =>:
            fn_lim(f,x0) = L
    fn_lim(f,x0) = L
"#;
    let (mut run, compiler) = super::execute(source);
    limit_wd(&mut run).function_domain.domain = Obj::StandardSet(StandardSet::R);
    compiler
        .compile_run(&run, "removed_guard")
        .expect_err("effective domain includes original guard");
}

#[test]
fn function_limit_uniqueness_rejects_cross_side_candidates() {
    let (mut run, compiler) = super::execute(UNIQUE);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::FunctionLimit(
        FunctionLimitEqualityProof::Uniqueness(p),
    )) = &mut equality(&mut run).searched_proof
    else {
        panic!("unique")
    };
    let AtomicFact::HasFunctionLimitFact(right) = &mut p.right.fact else {
        panic!("candidate")
    };
    right.approach = LimitApproach::FromLeft(right.approach.point().unwrap().clone().into());
    compiler
        .compile_run(&run, "cross_side")
        .expect_err("same approach required");
}

#[test]
fn function_limit_rejects_an_invalid_candidate_citation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
    let (mut run, compiler) = super::execute(SELECTED);
    let EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::FunctionLimit(
        FunctionLimitEqualityProof::SelectedValue(p),
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
        .compile_run(&run, "missing_candidate")
        .expect_err("exact citation required");
}

#[test]
fn function_limit_without_a_convergence_proof_is_rejected() {
    let source = "claim:\n    ? forall f fn(x R) R, x0 R:\n        $is_set(fn_lim(f,x0))\n    $is_set(fn_lim(f,x0))";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(source)
            .unwrap()
            .success
    );
}

pub(super) fn definition(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::BuiltinFunctionLimitDefinitionProof{
    use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByStmtResult};
    use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition, AtomicExceptEqualityFactSearchedProof,
        BuiltinPropDefinitionProof,
    };
    use crate::execute::ExecDefinitionStmtResult;
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(t),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(body) = &mut t.body else {
        panic!("forall")
    };
    let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
        body.proof_steps.last_mut().unwrap()
    else {
        panic!("by def")
    };
    let atomic = super::atomic_proof_mut(&mut p.proof);
    let AtomicExceptEqualityFactSearchedProof::ByDefinition(
        AtomicExceptEqualityFactSearchProofByDefinition::BuiltinProp(
            BuiltinPropDefinitionProof::FunctionLimit(p),
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("function-limit definition")
    };
    p
}

#[test]
fn function_limit_definition_replays_both_required_clauses() {
    for source in [
        r#"# Accumulation and epsilon-delta clauses prove the finite function-limit predicate.
thm checked_function_limit_intro:
    ? forall f fn(x R) R, x0 R, L R:
        forall r R+:
            exist x R st {0 < abs(x-x0) and abs(x-x0) < r}
        forall epsilon R+:
            exist delta R+ st {{x R: 0 < abs(x-x0) and abs(x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_at(f,x0,L)
    by def $has_limit_at(f,x0,L)
"#,
        r#"# Relative finite limits retain the function's nonzero input domain.
thm checked_guarded_function_limit_intro:
    ? forall f fn(t R: t != 0) R, x0 R, L R:
        forall r R+:
            exist x {t R: t != 0} st {0 < abs(x-x0) and abs(x-x0) < r}
        forall epsilon R+:
            exist delta R+ st {{x {t R: t != 0}: 0 < abs(x-x0) and abs(x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_at(f,x0,L)
    by def $has_limit_at(f,x0,L)
"#,
        r#"# Accumulation and epsilon-delta clauses prove the left-sided function-limit predicate.
thm checked_left_function_limit_intro:
    ? forall f fn(x R) R, x0 R, L R:
        forall r R+:
            exist x R st {0 < (x0-x) and (x0-x) < r}
        forall epsilon R+:
            exist delta R+ st {{x R: 0 < (x0-x) and (x0-x) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_left(f,x0,L)
    by def $has_limit_left(f,x0,L)
"#,
        r#"# Accumulation and epsilon-delta clauses prove the right-sided function-limit predicate.
thm checked_right_function_limit_intro:
    ? forall f fn(x R) R, x0 R, L R:
        forall r R+:
            exist x R st {0 < (x-x0) and (x-x0) < r}
        forall epsilon R+:
            exist delta R+ st {{x R: 0 < (x-x0) and (x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_right(f,x0,L)
    by def $has_limit_right(f,x0,L)
"#,
    ] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(definition(&mut run).proof_of_requirement_facts.len(), 2);
        assert!(compiler
            .compile_run(&run, "function_limit_definition")
            .expect(source)
            .contains("Litex.finiteFunctionLimitOfForall"));
    }
}

#[test]
fn function_limit_definition_rejects_missing_or_reordered_proofs() {
    let source = r#"# Accumulation and epsilon-delta clauses prove the finite function-limit predicate.
thm checked_function_limit_intro:
    ? forall f fn(x R) R, x0 R, L R:
        forall r R+:
            exist x R st {0 < abs(x-x0) and abs(x-x0) < r}
        forall epsilon R+:
            exist delta R+ st {{x R: 0 < abs(x-x0) and abs(x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_at(f,x0,L)
    by def $has_limit_at(f,x0,L)
"#;
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(source);
        let p = definition(&mut run);
        if missing {
            p.proof_of_requirement_facts.pop();
        } else {
            p.proof_of_requirement_facts.swap(0, 1);
        }
        compiler
            .compile_run(&run, "wrong_clauses")
            .expect_err("both exact ordered clauses required");
    }
}

#[test]
fn function_limit_definition_rejects_a_changed_accumulation_domain() {
    let source = r#"# Accumulation and epsilon-delta clauses prove the finite function-limit predicate.
thm checked_function_limit_intro:
    ? forall f fn(x R) R, x0 R, L R:
        forall r R+:
            exist x R st {0 < abs(x-x0) and abs(x-x0) < r}
        forall epsilon R+:
            exist delta R+ st {{x R: 0 < abs(x-x0) and abs(x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_at(f,x0,L)
    by def $has_limit_at(f,x0,L)
"#;
    let (mut run, compiler) = super::execute(source);
    let p = definition(&mut run);
    let Fact::ForallFact(f) = &mut p.requirement_facts[0] else {
        panic!("forall")
    };
    let ExistOrAndChainAtomicFact::ExistFact(e) = &mut f.then_facts[0] else {
        panic!("exist")
    };
    e.typed_parameters.groups[0].param_type = ParamType::Obj(Obj::StandardSet(StandardSet::N));
    compiler
        .compile_run(&run, "wrong_accumulation_domain")
        .expect_err("actual domain required");
}

#[test]
fn function_limit_definition_rejects_changed_epsilon_binders_and_preimage() {
    let source = r#"# Accumulation and epsilon-delta clauses prove the finite function-limit predicate.
thm checked_function_limit_intro:
    ? forall f fn(x R) R, x0 R, L R:
        forall r R+:
            exist x R st {0 < abs(x-x0) and abs(x-x0) < r}
        forall epsilon R+:
            exist delta R+ st {{x R: 0 < abs(x-x0) and abs(x-x0) < delta} $subset preimage_set(f,{v R: abs(v-L) < epsilon})}
        =>:
            $has_limit_at(f,x0,L)
    by def $has_limit_at(f,x0,L)
"#;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(source);
        let p = definition(&mut run);
        let Fact::ForallFact(f) = &mut p.requirement_facts[1] else {
            panic!("epsilon")
        };
        let ExistOrAndChainAtomicFact::ExistFact(e) = &mut f.then_facts[0] else {
            panic!("delta")
        };
        match mutation {
            0 => {
                e.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R))
            }
            1 => {
                e.typed_parameters.groups[0].params[0].id =
                    f.typed_parameters.groups[0].params[0].id
            }
            _ => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset)) =
                    &mut e.facts[0]
                else {
                    panic!("inclusion")
                };
                let Obj::FunctionSpace(FunctionSpace::PreimageSet(image)) = &mut subset.right
                else {
                    panic!("preimage")
                };
                image.function = Box::new(Obj::StandardSet(StandardSet::R));
            }
        }
        compiler
            .compile_run(&run, "changed_epsilon_clause")
            .expect_err("exact epsilon evidence required");
    }
}

#[test]
fn function_limit_cross_side_uniqueness_is_not_a_valid_source_rule() {
    let source = "claim:\n    ? forall f fn(x R) R, p R, L R, K R:\n        $has_limit_left(f,p,L)\n        $has_limit_right(f,p,K)\n        =>:\n            L = K\n    L = K";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    assert!(
        !Runtime::new(command)
            .run_litex_code(source)
            .unwrap()
            .success
    );
}
