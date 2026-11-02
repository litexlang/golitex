use crate::prelude::*;

#[test]
fn known_symdiff_original_self_and_definition_trees() {
    for (definition, source) in [(false, SELF), (true, DEFINITION)] {
        let (mut run, compiler) = super::execute(source);
        let proof = original_application(&mut run);
        let matches = &proof.detailed_ref().arg_match_proofs;
        assert_eq!(matches.len(), 2);
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{pattern,goal_arg,child_matches}=matches[0].detailed_ref() else{panic!("original symmetric difference")};
        assert!(matches!(
            pattern,
            Obj::SetOperator(SetOperator::SymmetricDifference(_))
        ));
        assert!(matches!(
            goal_arg,
            Obj::SetOperator(SetOperator::SymmetricDifference(_))
        ));
        assert_eq!(child_matches.len(), 2);
        assert!(matches!(child_matches[0].detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam{..}));
        if definition {
            assert!(matches!(child_matches[1].detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam{..}));
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{pattern,goal_arg,child_matches}=matches[1].detailed_ref() else{panic!("original definition union")};
            assert!(matches!(pattern, Obj::SetOperator(SetOperator::Union(_))));
            assert!(matches!(goal_arg, Obj::SetOperator(SetOperator::Union(_))));
            assert_eq!(child_matches.len(), 2);
            for minus in child_matches {
                let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{pattern,goal_arg,child_matches}=minus.detailed_ref() else{panic!("original definition minus")};
                assert!(matches!(
                    pattern,
                    Obj::SetOperator(SetOperator::SetMinus(_))
                ));
                assert!(matches!(
                    goal_arg,
                    Obj::SetOperator(SetOperator::SetMinus(_))
                ));
                assert_eq!(child_matches.len(), 2);
                assert!(child_matches.iter().all(|p|matches!(p.detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{..})));
            }
        } else {
            assert!(matches!(child_matches[1].detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{..}));
            assert!(matches!(matches[1].detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::NonParamEqual{..}));
        }
        let output = super::compile_run(&run, &compiler, "symdiff_original_tree").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "symdiff_original_tree").unwrap()
        );
    }
}

#[test]
fn known_symdiff_replays_actual_three_operation_profiles() {
    for source in ALL {
        let (run, compiler) = super::execute(source);
        let output = super::compile_run(&run, &compiler, "binary_set_profiles").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "binary_set_profiles").unwrap()
        );
    }
}
#[test]
fn known_symdiff_requires_both_original_captured_subjects() {
    for source in [DEFINITION, SELF] {
        for change_pattern in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { pattern, goal_arg, .. } = left_match(&mut run) else { panic!() };
            if change_pattern {
                *pattern = Obj::StandardSet(StandardSet::R);
            } else {
                *goal_arg = Obj::StandardSet(StandardSet::R);
            }
            reject(&run, &compiler, "captured_subject");
        }
    }
}
#[test]
fn known_symdiff_needs_exactly_two_original_children() {
    for source in [DEFINITION, SELF] {
        for count in [0, 1, 3] {
            let (mut run, compiler) = super::execute(source);
            let (mut donor, _) = super::execute(source);
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = left_match(&mut donor) else { panic!() };
            let original = child_matches.pop().unwrap();
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = left_match(&mut run) else { panic!() };
            if count == 3 {
                child_matches.push(original);
            } else {
                child_matches.truncate(count);
            }
            reject(&run, &compiler, "child_count");
        }
    }
}
#[test]
fn known_symdiff_preserves_original_operand_child_order() {
    for source in [DEFINITION, SELF] {
        let (mut run, compiler) = super::execute(source);
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = left_match(&mut run) else { panic!() };
        child_matches.swap(0, 1);
        reject(&run, &compiler, "operand_order");
    }
}
#[test]
fn known_symdiff_preserves_original_bound_parameter_identity() {
    let (mut run, compiler) = super::execute(DEFINITION);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = left_match(&mut run) else { panic!() };
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } = child_matches[0].as_detailed_mut().unwrap() else { panic!() };
    *param_id = IdentifierId::new(u64::MAX);
    reject(&run, &compiler, "bound_identity");
}
#[test]
fn known_symdiff_keeps_each_child_pattern_and_goal() {
    for pattern_side in [false, true] {
        let (mut run, compiler) = super::execute(DEFINITION);
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = left_match(&mut run) else { panic!() };
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam { pattern, goal_arg, .. } = child_matches[0].as_detailed_mut().unwrap() else { panic!() };
        if pattern_side {
            *pattern = Obj::StandardSet(StandardSet::C);
        } else {
            *goal_arg = Obj::StandardSet(StandardSet::C);
        }
        reject(&run, &compiler, "child_subject");
    }
}
#[test]
fn known_symdiff_does_not_replace_original_substitution() {
    let (mut run, compiler) = super::execute(DEFINITION);
    original_application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "substitution");
}
#[test]
fn known_symdiff_needs_all_original_set_requirements() {
    for source in [DEFINITION, SELF] {
        let (mut run, compiler) = super::execute(source);
        original_application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .param_type_requirements
            .pop();
        reject(&run, &compiler, "set_requirement_count");
    }
}
#[test]
fn known_symdiff_keeps_original_requirement_subject() {
    let (mut run, compiler) = super::execute(DEFINITION);
    let requirements = original_application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap();
    let proof = super::atomic_proof_mut(&mut requirements.param_type_requirements[0].proof);
    let AtomicFact::IsSetFact(fact) = &mut proof.fact else {
        panic!()
    };
    fact.set = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "set_requirement_subject");
}
#[test]
fn known_symdiff_requires_exact_prior_theorem_citation() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(DEFINITION);
        let target = last_equality(&mut run).fact.fact_id;
        original_application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .cite
            .fact_id = if missing {
            FactId::new(u64::MAX)
        } else {
            target
        };
        reject(&run, &compiler, "theorem_citation");
    }
}
#[test]
fn known_symdiff_cannot_borrow_a_closed_sibling_theorem() {
    let private="forall set37_private R:\n    forall set37_private_A,set37_private_B set:\n        union(set37_private_A,set37_private_B)=union(set37_private_B,set37_private_A)\n    =>:\n        set37_private=set37_private\n";
    let (mut run, compiler) = super::execute(&format!("{private}\n{DEFINITION}"));
    super::compile_run(&run, &compiler, "private_scope_baseline").unwrap();
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let StoreFactResult::ForallFact(store) = &first.assumed_dom_facts[0].store_and_infer.store
    else {
        panic!()
    };
    let foreign = store.fact_id;
    original_application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .cite
        .fact_id = foreign;
    reject(&run, &compiler, "private_theorem");
}
#[test]
fn known_symdiff_keeps_both_original_endpoint_wd() {
    for source in [DEFINITION, SELF] {
        let (mut run, compiler) = super::execute(source);
        let wd = last_equality(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject(&run, &compiler, "endpoint_wd");
    }
}
#[test]
fn known_symdiff_keeps_the_checked_goal_operands() {
    let (mut run, compiler) = super::execute(DEFINITION);
    let Obj::SetOperator(SetOperator::SymmetricDifference(p)) =
        &mut last_equality(&mut run).fact.left
    else {
        panic!()
    };
    p.left = Box::new(Obj::StandardSet(StandardSet::C));
    reject(&run, &compiler, "goal_operand");
}
#[test]
fn known_symdiff_keeps_original_rebound_subjects() {
    for previous_side in [false, true] {
        let (mut run, compiler) = super::execute(SELF);
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {previous,goal_arg,..}=child_matches[1].as_detailed_mut().unwrap() else {panic!()};
        if previous_side {
            *previous = Obj::StandardSet(StandardSet::C);
        } else {
            *goal_arg = Obj::StandardSet(StandardSet::C);
        }
        reject(&run, &compiler, "rebound_subject");
    }
}
#[test]
fn known_symdiff_keeps_rebound_strict_equality_certificate() {
    let (mut run, compiler) = super::execute(SELF);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {equal,..}=child_matches[1].as_detailed_mut().unwrap() else {panic!()};
    equal.equal_fact.left = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "rebound_equal_subject");
}
#[test]
fn known_symdiff_keeps_rebound_parameter_identity() {
    let (mut run, compiler) = super::execute(SELF);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {param_id,..}=child_matches[1].as_detailed_mut().unwrap() else {panic!()};
    *param_id = IdentifierId::new(u64::MAX);
    reject(&run, &compiler, "rebound_identity");
}
#[test]
fn known_symdiff_keeps_original_empty_result_match() {
    let (mut run, compiler) = super::execute(SELF);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::NonParamEqual{pattern_after_subst,..}=original_application(&mut run).as_detailed_mut().unwrap().arg_match_proofs[1].as_detailed_mut().unwrap() else{panic!()};
    *pattern_after_subst = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "empty_result_match");
}
#[test]
fn known_symdiff_needs_nested_constructor_children() {
    let (mut run, compiler) = super::execute(DEFINITION_NESTED);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else {panic!()};
    child_matches.clear();
    reject(&run, &compiler, "nested_child_count");
}
#[test]
fn known_symdiff_preserves_original_carrier_and_guard() {
    for source in [
        SELF_GUARD.replace("replay39_sgw>0", "replay39_sgw>1"),
        SELF.replace("fn(replay39_sw R) R", "C"),
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.clone()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}

#[test]
fn known_symdiff_keeps_original_constructor_wd_stages() {
    let (mut run, compiler) = super::execute(SELF);
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetOperator(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::SymmetricDifference(p)),..}=last_equality(&mut run).well_defined_proof.as_detailed_mut().unwrap().left.as_detailed_mut().unwrap() else{panic!()};
    assert_eq!(p.child_obj_well_defined.len(), 2);
    p.child_obj_well_defined.clear();
    reject(&run, &compiler, "constructor_wd_stages");
}
#[test]
fn known_symdiff_requires_original_literal_distinctness() {
    let (mut run, compiler) = super::execute(PAIR);
    literal_wd(&mut run).requirement_fact_verified.clear();
    reject(&run, &compiler, "literal_distinctness");
}
#[test]
fn known_symdiff_keeps_original_literal_distinctness_subject() {
    let (mut run, compiler) = super::execute(PAIR);
    let p = literal_wd(&mut run);
    let AtomicFact::NotEqualFact(f) =
        &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[0]).fact
    else {
        panic!()
    };
    f.right = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "literal_distinctness_subject");
}

fn last_verify(run: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    fn last(result: &mut VerifyFactResult) -> &mut VerifyFactResult {
        if matches!(result, VerifyFactResult::ForallFact(_)) {
            let VerifyFactResult::ForallFact(p) = result else {
                unreachable!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!()
            };
            return last(&mut p.proved_then_facts.last_mut().unwrap().verify_result);
        }
        result
    }
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    last(&mut statement.verify_result)
}
fn last_equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    super::equality_proof_mut(last_verify(run))
}
fn original_application(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact{
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut last_equality(run).searched_proof
    else {
        panic!("original known forall")
    };
    p
}
fn left_match(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof{
    original_application(run)
        .as_detailed_mut()
        .unwrap()
        .arg_match_proofs[0]
        .as_detailed_mut()
        .unwrap()
}
fn reject(
    run: &RunLitexCodeResult,
    compiler: &crate::compile_to_lean::LitexToLeanCompiler,
    name: &str,
) {
    assert!(
        super::compile_run(run, compiler, name).is_err(),
        "altered original evidence accepted: {name}"
    );
}
fn literal_wd(run:&mut RunLitexCodeResult)->&mut crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ListSetObjWellDefinedProof{
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetOperator(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::SymmetricDifference(p)),..}=last_equality(run).well_defined_proof.as_detailed_mut().unwrap().left.as_detailed_mut().unwrap() else{panic!()};
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetFormer(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef::ListSet(p)),..}=p.child_obj_well_defined[0].as_detailed_mut().unwrap() else{panic!()};
    assert_eq!(p.requirement_fact_verified.len(), 1);
    p
}
const SELF:&str="# Self symmetric difference reuses an ordinary general identity.\n# Former source (strict source success,second statement compiler rejection):\n# forall replay39_A set:\n#     set_diff(replay39_A,replay39_A)={}\n# set_diff(fn(replay39_sv R) R,fn(replay39_sw R) R)={}\n# Former compiler result: CompoundKnown/StructureConstructor.\n# Current replay must retain ordered operand matches and original strict equality.\nforall replay39_A set:\n    set_diff(replay39_A,replay39_A)={}\nset_diff(fn(replay39_sv R) R,fn(replay39_sw R) R)={}\n# Check: litex -lean -strict -f lean/examples/known_symdiff_self/statement.lit\n";
const DEFINITION:&str="forall replay39_DA,replay39_DB set:\n    set_diff(replay39_DA,replay39_DB)=union(set_minus(replay39_DA,replay39_DB),set_minus(replay39_DB,replay39_DA))\nset_diff(fn(replay39_dv R) R,C)=union(set_minus(fn(replay39_dw R) R,C),set_minus(C,fn(replay39_dz R) R))\n";
const SELF_GUARD:&str="# Preserve the positive-domain carrier guard.\nforall replay39_A set:\n    set_diff(replay39_A,replay39_A)={}\nset_diff(fn(replay39_sgv R:replay39_sgv>0) R,fn(replay39_sgw R:replay39_sgw>0) R)={}\n";
const DEFINITION_NESTED:&str="# Compose powerset,union,and difference matches in source order.\nforall replay39_NA,replay39_NB set:\n    set_diff(power_set(replay39_NA),union(replay39_NB,{}))=union(set_minus(power_set(replay39_NA),union(replay39_NB,{})),set_minus(union(replay39_NB,{}),power_set(replay39_NA)))\nset_diff(power_set(fn(replay39_dnv R) R),union(C,{}))=union(set_minus(power_set(fn(replay39_dnw R) R),union(C,{})),set_minus(union(C,{}),power_set(fn(replay39_dnz R) R)))\n";
const PAIR:&str="# Literal pair formation retains its original distinctness premise.\nforall replay39_QA,replay39_QB set:\n    replay39_QA!=replay39_QB\n    =>:\n        set_diff({replay39_QA,replay39_QB},{replay39_QA,replay39_QB})={}\nforall replay39_QS set:\n    fn(replay39_sqv R) R!=replay39_QS\n    =>:\n        set_diff({fn(replay39_sqv R) R,replay39_QS},{fn(replay39_sqw R) R,replay39_QS})={}\n";
const ALL:&[&str]=&[
"# Self symmetric difference reuses an ordinary general identity.\n# Former source (strict source success,second statement compiler rejection):\n# forall replay39_A set:\n#     set_diff(replay39_A,replay39_A)={}\n# set_diff(fn(replay39_sv R) R,fn(replay39_sw R) R)={}\n# Former compiler result: CompoundKnown/StructureConstructor.\n# Current replay must retain ordered operand matches and original strict equality.\nforall replay39_A set:\n    set_diff(replay39_A,replay39_A)={}\nset_diff(fn(replay39_sv R) R,fn(replay39_sw R) R)={}\n# Check: litex -lean -strict -f lean/examples/known_symdiff_self/statement.lit\n",
"# Preserve the positive-domain carrier guard.\nforall replay39_A set:\n    set_diff(replay39_A,replay39_A)={}\nset_diff(fn(replay39_sgv R:replay39_sgv>0) R,fn(replay39_sgw R:replay39_sgw>0) R)={}\n",
"# Preserve ordered mixed function-space parameter groups.\nforall replay39_A set:\n    set_diff(replay39_A,replay39_A)={}\nset_diff(fn(replay39_smv R,replay39_smu C) C,fn(replay39_smw R,replay39_smt C) C)={}\n",
"# Reuse self-difference through original nested powerset matches.\nforall replay39_PA set:\n    set_diff(power_set(replay39_PA),power_set(replay39_PA))={}\nset_diff(power_set(fn(replay39_spv R) R),power_set(fn(replay39_spw R) R))={}\n",
"# Reuse self-difference through original singleton literal matches.\nforall replay39_LA set:\n    set_diff({replay39_LA},{replay39_LA})={}\nset_diff({fn(replay39_slv R) R},{fn(replay39_slw R) R})={}\n",
"# Literal pair formation retains its original distinctness premise.\nforall replay39_QA,replay39_QB set:\n    replay39_QA!=replay39_QB\n    =>:\n        set_diff({replay39_QA,replay39_QB},{replay39_QA,replay39_QB})={}\nforall replay39_QS set:\n    fn(replay39_sqv R) R!=replay39_QS\n    =>:\n        set_diff({fn(replay39_sqv R) R,replay39_QS},{fn(replay39_sqw R) R,replay39_QS})={}\n",
"forall replay39_DA,replay39_DB set:\n    set_diff(replay39_DA,replay39_DB)=union(set_minus(replay39_DA,replay39_DB),set_minus(replay39_DB,replay39_DA))\nset_diff(fn(replay39_dv R) R,C)=union(set_minus(fn(replay39_dw R) R,C),set_minus(C,fn(replay39_dz R) R))\n",
"# Preserve the guarded operand in the defining union of differences.\nforall replay39_DA,replay39_DB set:\n    set_diff(replay39_DA,replay39_DB)=union(set_minus(replay39_DA,replay39_DB),set_minus(replay39_DB,replay39_DA))\nset_diff(fn(replay39_dgv R:replay39_dgv>0) R,C)=union(set_minus(fn(replay39_dgw R:replay39_dgw>0) R,C),set_minus(C,fn(replay39_dgz R:replay39_dgz>0) R))\n",
"# Preserve mixed parameter groups across all three original occurrences.\nforall replay39_DA,replay39_DB set:\n    set_diff(replay39_DA,replay39_DB)=union(set_minus(replay39_DA,replay39_DB),set_minus(replay39_DB,replay39_DA))\nset_diff(fn(replay39_dmv R,replay39_dmu C) C,R)=union(set_minus(fn(replay39_dmw R,replay39_dmt C) C,R),set_minus(R,fn(replay39_dmz R,replay39_dmq C) C))\n",
"# Compose powerset,union,and difference matches in source order.\nforall replay39_NA,replay39_NB set:\n    set_diff(power_set(replay39_NA),union(replay39_NB,{}))=union(set_minus(power_set(replay39_NA),union(replay39_NB,{})),set_minus(union(replay39_NB,{}),power_set(replay39_NA)))\nset_diff(power_set(fn(replay39_dnv R) R),union(C,{}))=union(set_minus(power_set(fn(replay39_dnw R) R),union(C,{})),set_minus(union(C,{}),power_set(fn(replay39_dnz R) R)))\n",
"# Reuse a returned natural membership in each finite carrier bound.\nforall replay39_DA,replay39_DB set:\n    set_diff(replay39_DA,replay39_DB)=union(set_minus(replay39_DA,replay39_DB),set_minus(replay39_DB,replay39_DA))\nforall replay39_h fn(replay39_t R) N,replay39_a R:\n    replay39_h(replay39_a) $in N\n    set_diff(fn(replay39_drv closed_range(1,replay39_h(replay39_a))) R,C)=union(set_minus(fn(replay39_drw closed_range(1,replay39_h(replay39_a))) R,C),set_minus(C,fn(replay39_drz closed_range(1,replay39_h(replay39_a))) R))\n",
"# Retain the singleton constructor under symmetric difference and both differences.\nforall replay39_TA,replay39_TB set:\n    set_diff({replay39_TA},replay39_TB)=union(set_minus({replay39_TA},replay39_TB),set_minus(replay39_TB,{replay39_TA}))\nset_diff({fn(replay39_dlv R) R},C)=union(set_minus({fn(replay39_dlw R) R},C),set_minus(C,{fn(replay39_dlz R) R}))\n",
];
