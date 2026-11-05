use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::function_domain::{
    FunctionDomainEmptyCarrierEvidence as E, FunctionDomainEmptyProof as D,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnBodyInReturnSetProof, AnonymousFnObjWellDefinedProof,
};
use crate::execute::{ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult};
use crate::prelude::*;

const EMPTY: &str = r#"# Functions on empty carriers still check their bodies and can return into the empty set.
have fn empty_constant(k {}) {} = 0
have fn empty_coordinate(k {}) {} = k
have fn empty_four(a,b R,k {},d R) {} = a+d
$is_set(empty_constant)
$is_set(empty_coordinate)
$is_set(empty_four)
"#;
const GUARDED: &str = r#"# Previously proved universal exclusions make complete input guards incompatible; body WD remains required.
forall k R:
    k=k

have fn empty_negative(k R:k!=k) {} = k
forall k R:
    k<0
    =>:
        not k>0

have fn empty_between(k R:k>0,k<0) {} = k
$is_set(empty_negative)
$is_set(empty_between)
forall k R:
    k>0
    =>:
        not k<0

have fn empty_between_reverse(k R:k<0,k>0) {} = k
$is_set(empty_between_reverse)
forall k R+:
    not k<0

have fn empty_positive(k R+:k<0) {} = k
$is_set(empty_positive)
"#;

fn declaration(statement: &mut ExecStmtResult) -> &mut ExecHaveFnEqualStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(proof),
    )) = statement
    else {
        panic!("named formula")
    };
    proof
}

fn anonymous(statement: &mut ExecStmtResult) -> &mut AnonymousFnObjWellDefinedProof {
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                proof,
            )),
        ..
    }) = declaration(statement)
        .anonymous_fn_well_defined
        .as_detailed_success_mut()
        .unwrap()
    else {
        panic!("original anonymous function WD")
    };
    proof
}

#[test]
fn empty_function_return_keeps_original_carrier_signature_and_body_wd() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(EMPTY);
        let wd = anonymous(&mut run.statement_results[0]);
        if mutation == 5 {
            std::mem::swap(&mut wd.body_well_defined, &mut wd.ret_set_well_defined);
        } else {
            let AnonymousFnBodyInReturnSetProof::EmptyCompleteDomain(D::ParameterCarrier(p)) =
                &mut wd.body_in_ret_set
            else {
                panic!("empty carrier")
            };
            match mutation {
                0 => p.parameter_group_index = usize::MAX,
                1 => p.empty_carrier = Obj::StandardSet(StandardSet::R),
                2 => p.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
                3 => {
                    p.signature.set_bound_parameters.groups[0].params[0].id =
                        IdentifierId::new(u64::MAX)
                }
                4 => p.evidence = E::EmptyIntegerRange,
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, "changed_empty_return")
            .expect_err("vacuity does not replace signature, carrier or body WD");
    }
}

#[test]
fn empty_function_return_keeps_the_excluded_guard_and_all_original_assumptions() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(GUARDED);
        let wd = anonymous(&mut run.statement_results[1]);
        if mutation == 2 {
            wd.assumed_dom_facts.clear();
        } else {
            let AnonymousFnBodyInReturnSetProof::EmptyCompleteDomain(D::GuardExclusion(p)) =
                &mut wd.body_in_ret_set
            else {
                panic!("guard exclusion")
            };
            match mutation {
                0 => p.excluded_guard_index = usize::MAX,
                1 => p.signature.dom_facts.clear(),
                _ => unreachable!(),
            }
        }
        compiler
            .compile_run(&run, "changed_empty_guard")
            .expect_err("exact complete-domain guard evidence");
    }
}

#[test]
fn empty_function_return_absence_cannot_cite_its_own_parameter_or_guard() {
    let (run, compiler) = super::execute(GUARDED);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(declaration),
    )) = &run.statement_results[1]
    else {
        panic!("named formula")
    };
    let VerifyObjWellDefinedResult::Success(original) = &declaration.anonymous_fn_well_defined
    else {
        panic!("formation")
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                wd,
            )),
        ..
    } = original.detailed_ref()
    else {
        panic!("formula WD")
    };
    let AnonymousFnBodyInReturnSetProof::EmptyCompleteDomain(D::GuardExclusion(empty)) =
        &wd.body_in_ret_set
    else {
        panic!("guard exclusion")
    };
    let prefix = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    let formed = SourcePosition::new(Some(&prefix), SourceOwner::WD(original), usize::MAX);
    let prior = formed
        .function_domain_empty_verify_prior(&empty.exclusion)
        .unwrap();
    assert_eq!(prior.before, wd.param_type_well_defined.len());
    for id in [
        wd.defined_params.store_and_infer_results[0].primary_fact_id(),
        wd.assumed_dom_facts[0].store_and_infer.primary_fact_id(),
    ] {
        assert!(
            compiler.cited_fact_reference(id, &formed).is_ok(),
            "positive visibility control"
        );
        assert!(
            compiler.cited_fact_reference(id, &prior).is_err(),
            "absence precedes this assumption"
        );
    }
}

#[test]
fn empty_function_return_strict_exclusions_keep_the_original_oriented_premise() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
        not_greater::NotGreaterFactSearchProofByBuiltinRule as NG,
        not_less::NotLessFactSearchProofByBuiltinRule as NL,
    };
    use AtomicExceptEqualityFactSearchProofByBuiltinRule as R;
    for source in [
        "forall a,b R:\n    a<b\n    =>:\n        not a>b\n",
        "forall a,b R:\n    a>b\n    =>:\n        not a<b\n",
    ] {
        let (mut run, compiler) = super::execute(source);
        compiler.compile_run(&run, "strict_exclusion").unwrap();
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let goal = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) = &mut goal.searched_proof
        else {
            panic!("selected strict exclusion")
        };
        let premise = match rule {
            R::NotGreaterFact(NG::FromKnownLess(p)) => &mut p.premise_proof.fact,
            R::NotLessFact(NL::FromKnownGreater(p)) => &mut p.premise_proof.fact,
            _ => panic!("original strict exclusion rule"),
        };
        match premise {
            AtomicFact::LessFact(f) => std::mem::swap(&mut f.left, &mut f.right),
            AtomicFact::GreaterFact(f) => std::mem::swap(&mut f.left, &mut f.right),
            _ => panic!("strict premise"),
        }
        compiler
            .compile_run(&run, "reversed_strict_exclusion")
            .expect_err("a true proof cannot be applied in the opposite direction");
    }
}
