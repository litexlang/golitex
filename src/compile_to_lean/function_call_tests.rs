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
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
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
    let wd = &proof
        .well_defined_proof
        .detailed_ref()
        .well_defined_of_each_parameter[0];
    let DetailedObjWellDefinedProof::ByDef {
        obj: Obj::FnObj(call),
        proof: ObjWellDefinedProofByDef::FnObj(evidence),
    } = (wd).as_detailed().unwrap()
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
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(evidence),
        ..
    } = (&mut proof
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0])
        .as_detailed_mut()
        .unwrap()
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
        if source == OR_GUARD {
            let VerifyFactResult::OrFact(verified) = &proof.requirement_fact_verified[guard_index]
            else {
                panic!("actual verified disjunction");
            };
            assert!(
                matches!(verified.as_ref(), VerifyOrFactResult::Success(verified)
                if matches!(verified.searched_proof, OrFactSearchedProof::ByBuiltinRule(
                    OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(_))))
            );
        }
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

fn or_guard_proof_mut(result: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let VerifyFactResult::OrFact(guard) =
        &mut call_evidence_mut(result, 1).requirement_fact_verified[2]
    else {
        panic!("actual disjunction guard result");
    };
    let VerifyOrFactResult::Success(guard) = guard.as_mut() else {
        panic!("successful original disjunction guard");
    };
    guard
}

fn or_guard_mut(result: &mut RunLitexCodeResult) -> &mut OrFact {
    &mut or_guard_proof_mut(result).fact
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
fn function_call_rejects_square_sum_evidence_for_another_recorded_component() {
    let (mut result, compiler) = checked(OR_GUARD);
    let OrFactSearchedProof::ByBuiltinRule(
        OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(selected),
    ) = &mut or_guard_proof_mut(&mut result).searched_proof
    else {
        panic!("actual original square-sum component rule");
    };
    selected.left = selected.right.clone();
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "Or/SquareSumSubject"
    );
}

#[test]
fn function_call_rejects_square_sum_child_for_another_pair() {
    let (mut result, compiler) = checked(OR_GUARD);
    let OrFactSearchedProof::ByBuiltinRule(
        OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(selected),
    ) = &mut or_guard_proof_mut(&mut result).searched_proof
    else {
        panic!("actual original square-sum component rule");
    };
    let VerifyFactResult::AtomicExceptEquality(child) = &mut selected.square_sum_nonzero else {
        panic!("actual original square-sum nonzero child");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(child) = child.as_mut() else {
        panic!("successful original square-sum nonzero child");
    };
    let AtomicFact::NotEqualFact(child) = &mut child.fact else {
        panic!("original nonzero child subject");
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &mut child.left else {
        panic!("original squared-component sum");
    };
    sum.right = sum.left.clone();
    assert_eq!(
        compile_leaf(&result, &compiler, 1).unwrap_err().route,
        "Or/SquareSumPremise"
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

#[test]
fn function_arity_replays_ordered_inputs_guards_and_nested_calls() {
    for source in [
        r#"# Evaluate a weighted sum with four independent real inputs.
have fn weighted_total(a, b, c, d R) R = a + 2*b + 3*c + 4*d
weighted_total(1, 2, 3, 4) = 30
"#,
        r#"# The nonzero fourth argument certifies division in a four-input function.
have fn guarded_average(a, b, c, d R: d != 0) R = (a + b + c) / d
guarded_average(1, 2, 3, 2) = 3
"#,
        r#"# Apply a four-input real function through a function-valued parameter.
have fn weighted_total(a, b, c, d R) R = a + 2*b + 3*c + 4*d
have fn apply_four(g fn(a, b, c, d R) R, a, b, c, d R) R = g(a, b, c, d)
apply_four(weighted_total, 1, 2, 3, 4) = 30
"#,
        r#"# A returned four-input function retains its outer offset and both call stages.
have fn shift_four(t R) fn(a, b, c, d R) R = fn(a, b, c, d R) R {t + a + 2*b + 3*c + 4*d}
shift_four(10)(1, 2, 3, 4) = 40
"#,
        r#"# A four-input function over arbitrary sets returns and exposes its first and last coordinates.
have A, B, D, E set
have fn edge_pair(a A, b B, d D, z E) cart(A, E) = (a, z)
forall a A, b B, d D, z E:
    edge_pair(a, b, d, z) = (a, z)
    edge_pair(a, b, d, z)(1) = a
    edge_pair(a, b, d, z)(2) = z
"#,
        r#"# A function uses its integral-candidate premise to certify and evaluate an integral in its body.
have fn integral_offset(f fn(x R) R, a, b, I, t R: $has_riemann_integral(f, a, b, I)) R = integral(f, a, b) + t
forall f fn(x R) R, a, b, I, t R:
    $has_riemann_integral(f, a, b, I)
    =>:
        integral_offset(f, a, b, I, t) = I + t
"#,
    ] {
        let (run, compiler) = checked(source);
        compiler.compile_run(&run, "function_arity").expect(source);
    }
}

#[test]
fn analysis_selector_beta_replays_original_existence_guards_in_function_bodies() {
    for source in [
        r#"# Evaluate a derivative-valued function using its original differentiability premise.
have fn slope_offset(f fn(x R) R, p, d, t R: $has_derivative_at(f,p,d)) R = derivative(f,p)+t
forall f fn(x R) R, p, d, t R:
    $has_derivative_at(f,p,d)
    =>:
        slope_offset(f,p,d,t)=d+t
"#,
        r#"# Shift a sequence limit, limsup, or liminf through a function with the matching existence premise.
have fn sequence_offset(a seq(R), L,t R: $has_seq_limit(a,L)) R = lim(a)+t
forall a seq(R), L,t R:
    $has_seq_limit(a,L)
    =>:
        sequence_offset(a,L,t)=L+t

have fn upper_offset(a seq(R), L,t R: $has_seq_limsup(a,L)) R = limsup(a)+t
forall a seq(R), L,t R:
    $has_seq_limsup(a,L)
    =>:
        upper_offset(a,L,t)=L+t

have fn lower_offset(a seq(R), L,t R: $has_seq_liminf(a,L)) R = liminf(a)+t
forall a seq(R), L,t R:
    $has_seq_liminf(a,L)
    =>:
        lower_offset(a,L,t)=L+t
"#,
        r#"# Preserve the selected approach when a function returns a shifted real function limit.
have fn left_limit_offset(f fn(x R) R, p,L,t R: $has_limit_left(f,p,L)) R = lim_left(f,p)+t
forall f fn(x R) R, p,L,t R:
    $has_limit_left(f,p,L)
    =>:
        left_limit_offset(f,p,L,t)=L+t

have fn point_limit_offset(f fn(x R) R, p,L,t R: $has_limit_at(f,p,L)) R = fn_lim(f,p)+t
forall f fn(x R) R, p,L,t R:
    $has_limit_at(f,p,L)
    =>:
        point_limit_offset(f,p,L,t)=L+t

have fn right_limit_offset(f fn(x R) R, p,L,t R: $has_limit_right(f,p,L)) R = lim_right(f,p)+t
forall f fn(x R) R, p,L,t R:
    $has_limit_right(f,p,L)
    =>:
        right_limit_offset(f,p,L,t)=L+t

have fn positive_limit_offset(f fn(x R) R, L,t R: $has_limit_pos_inf(f,L)) R = lim_pos_inf(f)+t
forall f fn(x R) R, L,t R:
    $has_limit_pos_inf(f,L)
    =>:
        positive_limit_offset(f,L,t)=L+t

have fn negative_limit_offset(f fn(x R) R, L,t R: $has_limit_neg_inf(f,L)) R = lim_neg_inf(f)+t
forall f fn(x R) R, L,t R:
    $has_limit_neg_inf(f,L)
    =>:
        negative_limit_offset(f,L,t)=L+t
"#,
    ] {
        let (run, compiler) = checked(source);
        compiler
            .compile_run(&run, "analysis_selector_beta")
            .expect(source);
    }
}

#[test]
fn multivariable_selector_beta_replays_original_existence_guards_in_function_bodies() {
    for source in [
        r#"# Add a real offset to a certified coordinate partial derivative.
have fn partial_offset(f fn(x cart_n(R,2)) R, p cart_n(R,2), d,t R: $has_partial_derivative_at(f,p,2,1,d)) R = partial_derivative(f,p,2,1)+t
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d,t R:
    $has_partial_derivative_at(f,p,2,1,d)
    =>:
        partial_offset(f,p,d,t)=d+t
"#,
        r#"# Add real offsets to certified multivariable limits, divergences and Laplacians.
have fn divergence_offset(f fn(x cart_n(R,2)) cart_n(R,2), p cart_n(R,2), d R, t R: $has_divergence_at(f,p,2,d)) R = divergence(f,p,2)+t
forall f fn(x cart_n(R,2)) cart_n(R,2), p cart_n(R,2), d R, t R:
    $has_divergence_at(f,p,2,d)
    =>:
        divergence_offset(f,p,d,t)=d+t

have fn laplacian_offset(f fn(x cart_n(R,2)) R, p cart_n(R,2), d R, t R: $has_laplacian_at(f,p,2,d)) R = laplacian(f,p,2)+t
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d R, t R:
    $has_laplacian_at(f,p,2,d)
    =>:
        laplacian_offset(f,p,d,t)=d+t

have fn multi_limit_offset(f fn(x cart_n(R,2)) R, p cart_n(R,2), L R, t R: $has_multi_limit_at(f,p,2,L)) R = lim_multi_at(f,p,2)+t
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R, t R:
    $has_multi_limit_at(f,p,2,L)
    =>:
        multi_limit_offset(f,p,L,t)=L+t
"#,
        r#"# Return certified scalar differentials, total differentials, Jacobians and Hessians through formula functions.
have fn scalar_diff_value(f fn(x cart_n(R,2)) R, p cart_n(R,2), A matrix(R,1,2): $has_scalar_differential_at(f,p,2,A)) matrix(R,1,2) = scalar_differential(f,p,2)
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), A matrix(R,1,2):
    $has_scalar_differential_at(f,p,2,A)
    =>:
        scalar_diff_value(f,p,A)=A

have fn total_diff_value(f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), A matrix(R,3,2): $has_total_derivative_at(f,p,2,3,A)) matrix(R,3,2) = differential(f,p,2,3)
forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), A matrix(R,3,2):
    $has_total_derivative_at(f,p,2,3,A)
    =>:
        total_diff_value(f,p,A)=A

have fn jacobian_value(f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), J matrix(R,3,2): $has_jacobian_at(f,p,2,3,J)) matrix(R,3,2) = jacobian(f,p,2,3)
forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), J matrix(R,3,2):
    $has_jacobian_at(f,p,2,3,J)
    =>:
        jacobian_value(f,p,J)=J

have fn hessian_value(f fn(x cart_n(R,2)) R, p cart_n(R,2), H matrix(R,2,2): $has_hessian_at(f,p,2,H)) matrix(R,2,2) = hessian(f,p,2)
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), H matrix(R,2,2):
    $has_hessian_at(f,p,2,H)
    =>:
        hessian_value(f,p,H)=H
"#,
        r#"# Return certified gradients, curls and vector limits through formula functions.
have fn gradient_value(f fn(x cart_n(R,2)) R, p cart_n(R,2), g cart_n(R,2): $has_gradient_at(f,p,2,g)) cart_n(R,2) = gradient_at(f,p,2)
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), g cart_n(R,2):
    $has_gradient_at(f,p,2,g)
    =>:
        gradient_value(f,p,g)=g

have fn curl_value(f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3): $has_curl_at(f,p,c)) cart_n(R,3) = curl(f,p)
forall f fn(x cart_n(R,3)) cart_n(R,3), p cart_n(R,3), c cart_n(R,3):
    $has_curl_at(f,p,c)
    =>:
        curl_value(f,p,c)=c

have fn vector_limit_value(f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), L cart_n(R,3): $has_vector_limit_at(f,p,2,3,L)) cart_n(R,3) = lim_vector_at(f,p,2,3)
forall f fn(x cart_n(R,2)) cart_n(R,3), p cart_n(R,2), L cart_n(R,3):
    $has_vector_limit_at(f,p,2,3,L)
    =>:
        vector_limit_value(f,p,L)=L
"#,
    ] {
        let (run, compiler) = checked(source);
        compiler
            .compile_run(&run, "multivariable_selector_beta")
            .expect(source);
    }
}

#[test]
fn function_input_carrier_locals_keep_original_stage_visibility() {
    use crate::execute::ExecHaveFnEqualStmtResult;
    let (run, _) = checked(
        r#"# Add a real offset to a certified coordinate partial derivative.
have fn partial_offset(f fn(x cart_n(R,2)) R, p cart_n(R,2), d,t R: $has_partial_derivative_at(f,p,2,1,d)) R = partial_derivative(f,p,2,1)+t
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d,t R:
    $has_partial_derivative_at(f,p,2,1,d)
    =>:
        partial_offset(f,p,d,t)=d+t
"#,
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(declaration),
    )) = &run.statement_results[0]
    else {
        panic!("formula declaration")
    };
    let VerifyObjWellDefinedResult::Success(original) = &declaration.anonymous_fn_well_defined
    else {
        panic!("formula formation")
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
    for emitted in 0..=wd.param_type_well_defined.len() {
        let at = SourcePosition::new(None, SourceOwner::WDLocals(original, emitted), 0);
        for (index, child) in wd.param_type_well_defined.iter().enumerate() {
            assert_eq!(at.bound_wd_child(child).is_some(), index < emitted);
        }
        assert!(at.bound_wd_child(&wd.ret_set_well_defined).is_none());
        assert!(at.bound_wd_child(&wd.body_well_defined).is_none());
    }
}

#[test]
fn function_input_carrier_locals_reject_missing_reordered_and_changed_evidence() {
    use crate::execute::ExecHaveFnEqualStmtResult;
    for mutation in 0..3 {
        let (mut run, compiler) = checked(
            r#"# Add a real offset to a certified coordinate partial derivative.
have fn partial_offset(f fn(x cart_n(R,2)) R, p cart_n(R,2), d,t R: $has_partial_derivative_at(f,p,2,1,d)) R = partial_derivative(f,p,2,1)+t
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d,t R:
    $has_partial_derivative_at(f,p,2,1,d)
    =>:
        partial_offset(f,p,d,t)=d+t
"#,
        );
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(declaration),
        )) = &mut run.statement_results[0]
        else {
            panic!("formula declaration")
        };
        let Some(DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(wd),
                ),
            ..
        }) = declaration
            .anonymous_fn_well_defined
            .as_detailed_success_mut()
            .unwrap()
        else {
            panic!("formula WD")
        };
        match mutation {
            0 => {
                wd.param_type_well_defined.pop();
            }
            1 => wd.param_type_well_defined.swap(0, 1),
            _ => std::mem::swap(
                &mut wd.param_type_well_defined[0],
                &mut wd.ret_set_well_defined,
            ),
        }
        compiler
            .compile_run(&run, "changed_function_input_carriers")
            .expect_err("carrier bindings cannot replace validation of the original capture");
    }
}

#[test]
fn function_arity_preserves_every_original_child_requirement_and_signature() {
    let source =
        "have fn average(a, b, c, d R: d != 0) R = (a + b + c) / d\n$is_set(average(1, 2, 3, 2))\n";
    for mutation in 0..5 {
        let (mut run, compiler) = checked(source);
        let evidence = call_evidence_mut(&mut run, 1);
        assert_eq!(evidence.child_obj_well_defined.len(), 4);
        assert_eq!(evidence.requirement_fact_verified.len(), 5);
        match mutation {
            0 => {
                evidence.child_obj_well_defined.pop();
            }
            1 => evidence.child_obj_well_defined.swap(0, 3),
            2 => {
                evidence.requirement_fact_verified.pop();
            }
            3 => evidence.requirement_fact_verified.swap(0, 4),
            _ => {
                let Some(FnObjDomainFnSetEvidence::InFunctionSet { fact_id, .. }) =
                    evidence.domain_fn_set.as_mut()
                else {
                    panic!("original function-set citation");
                };
                *fact_id = FactId::new(u64::MAX);
            }
        }
        compiler
            .compile_run(&run, "changed_function_arity")
            .expect_err("every original argument and domain certificate remains necessary");
    }
}
