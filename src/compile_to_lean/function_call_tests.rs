use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnObjDomainFnSetEvidence, FnObjObjWellDefinedProof,
};
use crate::prelude::*;

const REAL_PAIR: &str =
    "have fn call_defined_pair(x R, y R: y != 0) R = x / y\n$is_set(call_defined_pair(3, 2))\n";
const MIXED_PAIR: &str =
    "have fn call_defined_mixed(x Q, y R: y != 0) R = x / y\n$is_set(call_defined_mixed(3, 2))\n";
const LITERAL: &str = "$is_set(fn(x R: x != 0) R {x}(2))\n";
const EQUALITY_ALIAS: &str = "let call_alias = fn(x R) R {x}\n$is_set(call_alias(2))\n";
const TWO_GUARDS: &str =
    "have fn call_two_guards(x R: x != 0, x > 0) R = x\n$is_set(call_two_guards(2))\n";
const OR_GUARD: &str = "have fn call_either_nonzero(x, y R: x != 0 or y != 0) R = x + y\n$is_set(call_either_nonzero(0, 2))\n";
const COMPOUND_OR_GUARD: &str = "have fn call_or_compound(x R: 0 < x < 3 or x = 4 and x != 0) R = x\n$is_set(call_or_compound(2))\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let result = runtime.run_litex_code(source).expect("typed source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn call_atomic(
    result: &RunLitexCodeResult,
    index: usize,
) -> &VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &result.statement_results[index]
    else {
        panic!("call sethood statement");
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &statement.verify_result else {
        panic!("atomic call sethood result");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
        panic!("successful call sethood result");
    };
    proof
}

fn call_parts(
    proof: &VerifyAtomicExceptEqualityFactSuccess,
) -> (&ObjWellDefinedProof, &FnObj, &FnObjObjWellDefinedProof) {
    let wd = &proof.well_defined_proof.well_defined_of_each_parameter[0];
    let ObjWellDefinedProof::ByDef {
        obj: Obj::FnObj(call),
        proof: ObjWellDefinedProofByDef::FnObj(evidence),
    } = wd
    else {
        panic!("actual call constructor WD");
    };
    (wd, call, evidence)
}

fn call_evidence_mut(
    result: &mut RunLitexCodeResult,
    index: usize,
) -> &mut FnObjObjWellDefinedProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut result.statement_results[index]
    else {
        panic!("call sethood statement");
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &mut statement.verify_result else {
        panic!("atomic result");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("successful atomic result");
    };
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(evidence),
        ..
    } = &mut proof.well_defined_proof.well_defined_of_each_parameter[0]
    else {
        panic!("actual call WD");
    };
    evidence
}

fn compile_leaf(
    result: &RunLitexCodeResult,
    compiler: &LitexToLeanCompiler,
    index: usize,
) -> Result<(String, StandardSet, String), LeanCompileError> {
    let statement = &result.statement_results[index];
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = statement else {
        panic!("successful source fact");
    };
    let atomic = call_atomic(result, index);
    let (wd, call, evidence) = call_parts(atomic);
    let run = SourcePosition::new(None, SourceOwner::Run(result), index);
    let statement = SourcePosition::new(Some(&run), SourceOwner::Statement(statement), 0);
    let verify = SourcePosition::new(
        Some(&statement),
        SourceOwner::Verify(&success.verify_result),
        0,
    );
    let atomic = SourcePosition::new(
        Some(&verify),
        SourceOwner::AtomicWD(&atomic.well_defined_proof),
        0,
    );
    let wd = SourcePosition::new(Some(&atomic), SourceOwner::WD(wd), 0);
    let term = compiler.compile_fn_obj_wd(call, evidence, &wd)?;
    let (output, membership) = compiler.compile_fn_output_membership(call, evidence, &wd)?;
    Ok((term, output, membership))
}

fn selected_citation(proof: &FnObjObjWellDefinedProof) -> FactId {
    match proof
        .domain_fn_set
        .as_ref()
        .expect("selected source signature")
    {
        FnObjDomainFnSetEvidence::InFunctionSet { fact_id, .. } => *fact_id,
        _ => panic!("actual source citation"),
    }
}

#[test]
fn function_calls_preserve_distinct_real_parameter_groups_and_original_membership() {
    let (result, compiler) = checked(REAL_PAIR);
    let (_, call, proof) = call_parts(call_atomic(&result, 1));
    let FnObjDomainFnSetEvidence::InFunctionSet {
        fn_set, fact_id, ..
    } = proof.domain_fn_set.as_ref().unwrap()
    else {
        panic!("original membership");
    };
    assert_eq!(fn_set.set_bound_parameters.groups.len(), 2);
    assert_eq!(
        call.body.len(),
        1,
        "two parameter groups are one simultaneous call layer"
    );
    assert_eq!(proof.child_obj_well_defined.len(), 2);
    assert_eq!(proof.requirement_fact_verified.len(), 3);
    assert!(matches!(
        compiler.runtime.fact_by_id_in_stack(*fact_id),
        Some(Fact::AtomicFact(AtomicFact::InFact(_)))
    ));
    let (term, output, member) =
        compile_leaf(&result, &compiler, 1).expect("certified simultaneous call");
    assert_eq!(output, StandardSet::R);
    assert!(term.contains(&format!("h_{}", fact_id.value())));
    assert!(member.contains("Litex.call2InOutput"));
    compiler
        .compile_run(&result, "two_source_parameter_groups")
        .expect("full owned-function artifact");
}

#[test]
fn function_calls_preserve_mixed_numeric_parameter_domains() {
    let (result, compiler) = checked(MIXED_PAIR);
    let (_, _, proof) = call_parts(call_atomic(&result, 1));
    for (index, set) in [StandardSet::Q, StandardSet::R].iter().enumerate() {
        assert!(
            matches!(super::helper::source_subject(&proof.requirement_fact_verified[index]).unwrap(), Fact::AtomicFact(AtomicFact::InFact(f)) if f.set == Obj::StandardSet(set.clone()))
        );
    }
    let (_, output, member) = compile_leaf(&result, &compiler, 1).expect("source Q/R domains");
    assert_eq!(output, StandardSet::R);
    assert!(member.contains("Litex.call2InOutput"));
    compiler
        .compile_run(&result, "mixed_source_parameter_domains")
        .expect("full mixed-domain artifact");
}

#[test]
fn anonymous_function_calls_consume_actual_head_construction_and_guard() {
    let (result, compiler) = checked(LITERAL);
    let (_, call, proof) = call_parts(call_atomic(&result, 0));
    assert!(matches!(
        proof.domain_fn_set,
        Some(FnObjDomainFnSetEvidence::AnonymousLiteral { .. })
    ));
    assert_eq!(
        proof.child_obj_well_defined.len(),
        2,
        "literal head precedes its single argument"
    );
    assert_eq!(proof.requirement_fact_verified.len(), 2);
    let FnObjHead::AnonymousFnLiteral(function) = call.head.as_ref() else {
        panic!("literal head");
    };
    assert_eq!(
        proof.child_obj_well_defined[0].obj().ir(),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone())).ir()
    );
    let (term, output, member) = compile_leaf(&result, &compiler, 0).expect("owned literal call");
    assert_eq!(output, StandardSet::R);
    assert!(term.contains("Litex.formulaFnInFnSet"));
    assert!(member.contains("Litex.callInOutput"));
    compiler
        .compile_run(&result, "literal_call_owned_head")
        .expect("full literal-call artifact");
}

#[test]
fn function_call_replays_the_actual_literal_equality_citation() {
    let (result, compiler) = checked(EQUALITY_ALIAS);
    let (_, _, proof) = call_parts(call_atomic(&result, 1));
    let id = selected_citation(proof);
    assert!(
        matches!(
            compiler.runtime.fact_by_id_in_stack(id),
            Some(Fact::AtomicFact(AtomicFact::EqualFact(_)))
        ),
        "this source really selects equality, not an alternative membership"
    );
    let (term, _, _) =
        compile_leaf(&result, &compiler, 1).expect("original equality to the formula graph");
    assert!(term.contains(&format!("h_{}", id.value())));
    assert!(term.contains("Litex.formulaFnInFnSet"));
    compiler
        .compile_run(&result, "literal_alias_call")
        .expect("full original-equality artifact");
}

#[test]
fn function_call_output_law_consumes_all_ordered_guard_clauses() {
    let (result, compiler) = checked(TWO_GUARDS);
    let (_, _, proof) = call_parts(call_atomic(&result, 1));
    assert_eq!(proof.requirement_fact_verified.len(), 3);
    assert!(matches!(
        super::helper::source_subject(&proof.requirement_fact_verified[1]).unwrap(),
        Fact::AtomicFact(AtomicFact::NotEqualFact(_))
    ));
    assert!(matches!(
        super::helper::source_subject(&proof.requirement_fact_verified[2]).unwrap(),
        Fact::AtomicFact(AtomicFact::GreaterFact(_))
    ));
    let (_, output, _) =
        compile_leaf(&result, &compiler, 1).expect("both actual guards are replayed");
    assert_eq!(output, StandardSet::R);
    compiler
        .compile_run(&result, "two_guard_call")
        .expect("full constructor consumes the entire conjunction");
}

#[test]
fn function_call_replays_exact_disjunction_guard_substitution() {
    for (source, guard_index, namespace) in [
        (OR_GUARD, 2, "atomic_or_guard"),
        (COMPOUND_OR_GUARD, 1, "compound_or_guard"),
    ] {
        let (result, compiler) = checked(source);
        let (_, _, proof) = call_parts(call_atomic(&result, 1));
        let Fact::OrFact(guard) =
            super::helper::source_subject(&proof.requirement_fact_verified[guard_index]).unwrap()
        else {
            panic!("the recorded call guard is a disjunction");
        };
        assert_eq!(guard.facts.len(), 2);
        if source == COMPOUND_OR_GUARD {
            assert!(matches!(guard.facts[0], AndChainAtomicFact::ChainFact(_)));
            assert!(matches!(guard.facts[1], AndChainAtomicFact::AndFact(_)));
        }
        let (_, output, _) = compile_leaf(&result, &compiler, 1)
            .expect("the actual ordered disjunction guard instantiates its recorded binders");
        assert_eq!(output, StandardSet::R);
        compiler
            .compile_run(&result, namespace)
            .expect("the complete constructor replays the original disjunction proof");
    }
}

fn or_guard_mut(result: &mut RunLitexCodeResult) -> &mut OrFact {
    let VerifyFactResult::OrFact(guard) =
        &mut call_evidence_mut(result, 1).requirement_fact_verified[2]
    else {
        panic!("actual disjunction guard result");
    };
    let VerifyOrFactResult::Success(guard) = guard.as_mut() else {
        panic!("successful original disjunction guard");
    };
    &mut guard.fact
}

#[test]
fn function_call_rejects_reordered_disjunction_guard_branches() {
    let (mut result, compiler) = checked(OR_GUARD);
    or_guard_mut(&mut result).facts.swap(0, 1);
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/GuardSubject"
    );
}

#[test]
fn function_call_rejects_a_missing_disjunction_guard_branch() {
    let (mut result, compiler) = checked(OR_GUARD);
    or_guard_mut(&mut result).facts.pop();
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/GuardSubject"
    );
}

#[test]
fn function_call_rejects_a_disjunction_guard_branch_for_another_argument() {
    let (mut result, compiler) = checked(OR_GUARD);
    let guard = or_guard_mut(&mut result);
    guard.facts[1] = guard.facts[0].clone();
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/GuardSubject"
    );
}

#[test]
fn function_call_rejects_missing_selected_domain_evidence() {
    let (mut result, compiler) = checked(REAL_PAIR);
    call_evidence_mut(&mut result, 1).domain_fn_set = None;
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/DomainEvidence"
    );
}

#[test]
fn function_call_rejects_missing_owned_argument_wd() {
    let (mut result, compiler) = checked(REAL_PAIR);
    call_evidence_mut(&mut result, 1)
        .child_obj_well_defined
        .pop();
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/StageArity"
    );
}

#[test]
fn function_call_rejects_reordered_parameter_truths() {
    let (mut result, compiler) = checked(REAL_PAIR);
    call_evidence_mut(&mut result, 1)
        .requirement_fact_verified
        .swap(0, 1);
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/ParameterMembership"
    );
}

#[test]
fn function_call_rejects_a_true_guard_for_another_actual_argument() {
    let (mut result, compiler) = checked(REAL_PAIR);
    let (_, call, _) = call_parts(call_atomic(&result, 1));
    let other_argument = call.body[0][0].as_ref().clone();
    let proof = call_evidence_mut(&mut result, 1);
    let VerifyFactResult::AtomicExceptEquality(guard) = &mut proof.requirement_fact_verified[2]
    else {
        panic!("guard result");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(guard) = guard.as_mut() else {
        panic!("verified guard");
    };
    let AtomicFact::NotEqualFact(fact) = &mut guard.fact else {
        panic!("actual nonzero guard");
    };
    fact.left = other_argument;
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/GuardSubject"
    );
}

#[test]
fn function_call_rejects_an_unrecorded_return_upper_bound() {
    let (mut result, compiler) = checked(REAL_PAIR);
    let FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. } = call_evidence_mut(&mut result, 1)
        .domain_fn_set
        .as_mut()
        .unwrap()
    else {
        panic!("selected signature");
    };
    fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "WD/FnObj/Signature"
    );
}

#[test]
fn function_call_rejects_a_bad_recorded_head_equality_edge() {
    let (mut result, compiler) = checked(EQUALITY_ALIAS);
    let (_, call, proof) = call_parts(call_atomic(&result, 1));
    let FnObjHead::Identifier(head) = call.head.as_ref() else {
        panic!("source alias head");
    };
    let head = Obj::Identifier(head.clone());
    let other = call.body[0][0].as_ref().clone();
    let id = selected_citation(proof);
    let FnObjDomainFnSetEvidence::InFunctionSet { function_equal, .. } =
        call_evidence_mut(&mut result, 1)
            .domain_fn_set
            .as_mut()
            .unwrap()
    else {
        panic!("original selected path");
    };
    function_equal.path.push((head, other, id));
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "Equality/PathSubject"
    );
}

#[test]
fn function_call_cannot_recover_a_removed_definition_from_final_runtime() {
    let (mut result, compiler) = checked(REAL_PAIR);
    result.statement_results.remove(0);
    let error = compiler
        .compile_run(&result, "missing_original_function")
        .expect_err("the final Runtime still knows the function but the original producer is gone");
    assert!(error.route.ends_with("/Producer"), "{error:?}");
}
