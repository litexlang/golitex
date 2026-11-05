use crate::prelude::*;

#[test]
fn known_set_binary_original_tree_records_ordered_and_rebound_children() {
    for (kind, source) in [("union", UNION), ("intersect", INTERSECT), ("minus", MINUS)] {
        let (mut run, compiler) = super::execute(source);
        let proof = original_application(&mut run);
        let matches = &proof.detailed_ref().arg_match_proofs;
        assert_eq!(matches.len(), 2);
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { pattern, goal_arg, child_matches } = matches[0].detailed_ref() else { panic!("original structure") };
        assert!(matches!(pattern, Obj::SetOperator(_)));
        assert!(matches!(goal_arg, Obj::SetOperator(_)));
        assert_eq!(child_matches.len(), 2);
        assert!(matches!(child_matches[0].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam {..}));
        match kind {
            "union" => {
                assert!(matches!(child_matches[1].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam {..}));
                let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = matches[1].detailed_ref() else { panic!("original right union") };
                assert_eq!(child_matches.len(), 2);
                assert!(child_matches.iter().all(|p| matches!(p.detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {..})));
            }
            "intersect" => {
                assert!(matches!(child_matches[1].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {..}));
                assert!(matches!(matches[1].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {..}));
            }
            "minus" => {
                assert!(matches!(child_matches[1].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::NonParamEqual {..}));
                assert!(matches!(matches[1].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {..}));
            }
            _ => unreachable!(),
        }
        let output = super::compile_run(&run, &compiler, "original_binary_set_tree").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "original_binary_set_tree").unwrap()
        );
    }
}
#[test]
fn known_set_binary_requires_both_original_captured_subjects() {
    for source in [UNION, INTERSECT, MINUS] {
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
fn known_set_binary_needs_exactly_two_original_children() {
    for source in [UNION, INTERSECT, MINUS] {
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
fn known_set_binary_preserves_original_operand_child_order() {
    for source in [UNION, INTERSECT, MINUS] {
        let (mut run, compiler) = super::execute(source);
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = left_match(&mut run) else { panic!() };
        child_matches.swap(0, 1);
        reject(&run, &compiler, "operand_order");
    }
}
#[test]
fn known_set_binary_preserves_original_bound_parameter_identity() {
    let (mut run, compiler) = super::execute(UNION);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = left_match(&mut run) else { panic!() };
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } = child_matches[0].as_detailed_mut().unwrap() else { panic!() };
    *param_id = IdentifierId::new(u64::MAX);
    reject(&run, &compiler, "bound_identity");
}
#[test]
fn known_set_binary_keeps_each_child_pattern_and_goal() {
    for pattern_side in [false, true] {
        let (mut run, compiler) = super::execute(UNION);
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
fn known_set_binary_does_not_replace_original_substitution() {
    let (mut run, compiler) = super::execute(UNION);
    original_application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "substitution");
}
#[test]
fn known_set_binary_needs_all_original_set_requirements() {
    for source in [UNION, INTERSECT, MINUS] {
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
fn known_set_binary_keeps_original_requirement_subject() {
    let (mut run, compiler) = super::execute(UNION);
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
fn known_set_binary_requires_exact_prior_theorem_citation() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(UNION);
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
fn known_set_binary_cannot_borrow_a_closed_sibling_theorem() {
    let private="forall set37_private R:\n    forall set37_private_A,set37_private_B set:\n        union(set37_private_A,set37_private_B)=union(set37_private_B,set37_private_A)\n    =>:\n        set37_private=set37_private\n";
    let (mut run, compiler) = super::execute(&format!("{private}\n{UNION}"));
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
fn known_set_binary_keeps_both_original_endpoint_wd() {
    for source in [UNION, INTERSECT, MINUS] {
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
fn known_set_binary_keeps_the_checked_goal_operands() {
    let (mut run, compiler) = super::execute(UNION);
    let Obj::SetOperator(SetOperator::Union(p)) = &mut last_equality(&mut run).fact.left else {
        panic!()
    };
    p.left = Box::new(Obj::StandardSet(StandardSet::C));
    reject(&run, &compiler, "goal_operand");
}
#[test]
fn known_set_binary_keeps_original_rebound_subjects() {
    for previous_side in [false, true] {
        let (mut run, compiler) = super::execute(INTERSECT);
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
fn known_set_binary_keeps_rebound_strict_equality_certificate() {
    let (mut run, compiler) = super::execute(INTERSECT);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {equal,..}=child_matches[1].as_detailed_mut().unwrap() else {panic!()};
    equal.equal_fact.left = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "rebound_equal_subject");
}
#[test]
fn known_set_binary_keeps_rebound_parameter_identity() {
    let (mut run, compiler) = super::execute(INTERSECT);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {param_id,..}=child_matches[1].as_detailed_mut().unwrap() else {panic!()};
    *param_id = IdentifierId::new(u64::MAX);
    reject(&run, &compiler, "rebound_identity");
}
#[test]
fn known_set_binary_keeps_fixed_empty_operand_match() {
    let (mut run, compiler) = super::execute(MINUS);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::NonParamEqual {pattern_after_subst,..}=child_matches[1].as_detailed_mut().unwrap() else {panic!()};
    *pattern_after_subst = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "fixed_empty_match");
}
#[test]
fn known_set_binary_needs_nested_constructor_children() {
    let (mut run, compiler) = super::execute(ASSOC);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=left_match(&mut run) else {panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else {panic!()};
    child_matches.clear();
    reject(&run, &compiler, "nested_child_count");
}
#[test]
fn known_set_binary_keeps_guards_and_difference_orientation() {
    for source in [
        UNION_GUARD.replace("replay37_gw>0", "replay37_gw>1"),
        MINUS.replace(
            "set_minus(fn(replay37_dv R) R,{})",
            "set_minus({},fn(replay37_dv R) R)",
        ),
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.clone()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}

fn last_equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    super::equality_proof_mut(&mut statement.verify_result)
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
const UNION: &str = "# Union commutativity is reused at an alpha-renamed function-space carrier.\n# Before: source success,second-fact compiler rejection.\n# forall replay37_A,replay37_B set:\n#     union(replay37_A,replay37_B)=union(replay37_B,replay37_A)\n# union(fn(replay37_v R) R,C)=union(C,fn(replay37_w R) R)\n# Former compiler result: CompoundKnown/StructureConstructor.\n# Now: replay ordered operand matches and original strict rebound equalities.\n# Reuse union commutativity at equal alpha-renamed function-space carriers.\nforall replay37_A,replay37_B set:\n    union(replay37_A,replay37_B)=union(replay37_B,replay37_A)\nunion(fn(replay37_v R) R,C)=union(C,fn(replay37_w R) R)\n# Boundary: a changed operand guard remains unproved.\n# Evidence: litex -lean -strict -f corpus case known_set_union\n# Evidence: known_set_binary_match_tests rejects altered certificates and scope escapes.\n";
const INTERSECT: &str = "# Reuse intersection idempotence with original repeated-parameter evidence.\nforall replay37_I set:\n    intersect(replay37_I,replay37_I)=replay37_I\nintersect(fn(replay37_iv R) R,fn(replay37_iw R) R)=fn(replay37_iz R) R\n";
const MINUS: &str = "# Reuse empty-set subtraction at an alpha-renamed function-space carrier.\nforall replay37_D set:\n    set_minus(replay37_D,{})=replay37_D\nset_minus(fn(replay37_dv R) R,{})=fn(replay37_dw R) R\n";
const ASSOC: &str = "# Reuse associativity with nested union constructor matches.\nforall replay37_aA,replay37_aB,replay37_aC set:\n    union(union(replay37_aA,replay37_aB),replay37_aC)=union(replay37_aA,union(replay37_aB,replay37_aC))\nunion(union(fn(replay37_av R) R,R),C)=union(fn(replay37_aw R) R,union(R,C))\n";
const UNION_GUARD: &str = "# Reuse union commutativity at equal alpha-renamed function-space carriers.\nforall replay37_A,replay37_B set:\n    union(replay37_A,replay37_B)=union(replay37_B,replay37_A)\nunion(fn(replay37_gv R:replay37_gv>0) R,C)=union(C,fn(replay37_gw R:replay37_gw>0) R)\n";
