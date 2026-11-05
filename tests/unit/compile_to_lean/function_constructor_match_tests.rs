use crate::prelude::*;

#[test]
fn function_constructor_original_three_match_trees() {
    for name in ["range", "point_preimage", "set_preimage"] {
        let (mut run, compiler) = super::execute(source(name));
        assert_eq!(
            original_application(&mut run)
                .detailed_ref()
                .arg_match_proofs
                .len(),
            2
        );
        for right in [false, true] {
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{pattern,goal_arg,child_matches}=constructor_match(&mut run,right) else{panic!()};
            assert_eq!(child_matches.len(), if name == "range" { 1 } else { 2 });
            assert!(match (pattern, goal_arg, name) {
                (
                    Obj::FunctionSpace(FunctionSpace::FnRange(_)),
                    Obj::FunctionSpace(FunctionSpace::FnRange(_)),
                    "range",
                ) => true,
                (
                    Obj::FunctionSpace(FunctionSpace::Preimage(_)),
                    Obj::FunctionSpace(FunctionSpace::Preimage(_)),
                    "point_preimage",
                ) => true,
                (
                    Obj::FunctionSpace(FunctionSpace::PreimageSet(_)),
                    Obj::FunctionSpace(FunctionSpace::PreimageSet(_)),
                    "set_preimage",
                ) => true,
                _ => false,
            });
            assert!(if right {
                matches!(child_matches[0].detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{..})
            } else {
                matches!(child_matches[0].detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam{..})
            });
        }
        super::compile_run(&run, &compiler, "original_three").unwrap();
    }
}
#[test]
fn function_constructor_replays_all_actual_profiles_deterministically() {
    let mut errors = Vec::new();
    for (name, src) in SOURCES {
        let (run, c) = super::execute(src);
        match super::compile_run(&run, &c, name) {
            Ok(output) => assert_eq!(output, super::compile_run(&run, &c, name).unwrap()),
            Err(error) => errors.push(format!("{name}: {error}")),
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}
#[test]
fn function_constructor_preserves_captured_constructor_subjects() {
    for name in ["range", "point_preimage", "set_preimage"] {
        for right in [false, true] {
            for pattern_side in [false, true] {
                let (mut run, c) = super::execute(source(name));
                let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{pattern,goal_arg,..}=constructor_match(&mut run,right) else{panic!()};
                if pattern_side {
                    *pattern = Obj::StandardSet(StandardSet::C)
                } else {
                    *goal_arg = Obj::StandardSet(StandardSet::C)
                };
                reject(&run, &c, "captured_constructor");
            }
        }
    }
}
#[test]
fn function_constructor_requires_exact_original_child_arity() {
    for name in ["range", "point_preimage", "set_preimage"] {
        for right in [false, true] {
            for extra in [false, true] {
                let (mut run, c) = super::execute(source(name));
                let (mut donor, _) = super::execute(source(name));
                let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut donor,right) else{panic!()};
                let spare = child_matches.pop().unwrap();
                let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,right) else{panic!()};
                if extra {
                    child_matches.push(spare)
                } else {
                    child_matches.pop();
                }
                reject(&run, &c, "child_arity");
            }
        }
    }
}
#[test]
fn function_constructor_preserves_function_then_target_order() {
    for name in ["point_preimage", "set_preimage"] {
        for right in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,right) else{panic!()};
            child_matches.swap(0, 1);
            reject(&run, &c, "child_order");
        }
    }
}
#[test]
fn function_constructor_preserves_bound_identity_and_subjects() {
    for change in 0..3 {
        let (mut run, c) = super::execute(source("range"));
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,false) else{panic!()};
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam{param_id,pattern,goal_arg}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
        match change {
            0 => *param_id = IdentifierId::new(u64::MAX),
            1 => *pattern = Obj::StandardSet(StandardSet::C),
            _ => *goal_arg = Obj::StandardSet(StandardSet::C),
        };
        reject(&run, &c, "bound_subject");
    }
}
#[test]
fn function_constructor_preserves_rebound_identity_and_subjects() {
    for change in 0..4 {
        let (mut run, c) = super::execute(source("point_preimage"));
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,true) else{panic!()};
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{param_id,previous,goal_arg,equal}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
        match change {
            0 => *param_id = IdentifierId::new(u64::MAX),
            1 => *previous = Obj::StandardSet(StandardSet::C),
            2 => *goal_arg = Obj::StandardSet(StandardSet::C),
            _ => equal.equal_fact.left = Obj::StandardSet(StandardSet::C),
        };
        reject(&run, &c, "rebound_subject");
    }
}
#[test]
fn function_constructor_preserves_original_fixed_target_equalities() {
    for change in 0..3 {
        let (mut run, c) = super::execute(source("set_preimage"));
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,true) else{panic!()};
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::NonParamEqual{pattern,pattern_after_subst,equal,..}=child_matches[1].as_detailed_mut().unwrap() else{panic!()};
        match change {
            0 => *pattern = Obj::StandardSet(StandardSet::C),
            1 => *pattern_after_subst = Obj::StandardSet(StandardSet::C),
            _ => equal.equal_fact.right = Obj::StandardSet(StandardSet::C),
        };
        reject(&run, &c, "fixed_target");
    }
}
#[test]
fn function_constructor_preserves_independent_target_binding_and_rebound() {
    for name in ["point_target_alpha", "set_target_alpha"] {
        let (mut run, c) = super::execute(source(name));
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,true) else{panic!()};
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{equal,..}=child_matches[1].as_detailed_mut().unwrap() else{panic!()};
        equal.equal_fact.left = Obj::StandardSet(StandardSet::C);
        reject(&run, &c, "target_rebound");
    }
}
#[test]
fn function_constructor_uses_original_closed_numeric_target_certificate() {
    let (mut run, c) = super::execute(source("point_target_calc"));
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,true) else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{equal,..}=child_matches[1].as_detailed_mut().unwrap() else{panic!()};
    assert!(matches!(equal.equal_proof,crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::StrictEqualArgProof::ByClosedCalculation(_)));
    equal.equal_fact.right = Obj::StandardSet(StandardSet::C);
    reject(&run, &c, "numeric_target_certificate");
}
#[test]
fn function_constructor_preserves_original_substitution() {
    for name in ["range", "point_preimage", "set_preimage"] {
        let (mut run, c) = super::execute(source(name));
        original_application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::C);
        reject(&run, &c, "substitution");
    }
}
#[test]
fn function_constructor_requires_all_original_instantiation_requirements() {
    for name in ["range", "point_preimage", "set_preimage"] {
        let (mut run, c) = super::execute(source(name));
        original_application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .param_type_requirements
            .pop();
        reject(&run, &c, "requirement_count");
    }
}
#[test]
fn function_constructor_preserves_original_membership_requirement_subject() {
    let (mut run, c) = super::execute(source("range"));
    let p = original_application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap();
    let AtomicFact::InFact(f) =
        &mut super::atomic_proof_mut(&mut p.param_type_requirements[0].proof).fact
    else {
        panic!()
    };
    f.element = Obj::StandardSet(StandardSet::C);
    reject(&run, &c, "requirement_subject");
}
#[test]
fn function_constructor_requires_original_prior_citation() {
    for missing in [false, true] {
        let (mut run, c) = super::execute(source("range"));
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
        reject(&run, &c, "citation");
    }
}
#[test]
fn function_constructor_cannot_borrow_closed_sibling_theorem() {
    let private="forall fc41_private R:\n    forall fc41_private_A set:\n        set_minus(fc41_private_A,{})=fc41_private_A\n    =>:\n        fc41_private=fc41_private\n";
    let (mut run, c) = super::execute(&format!("{private}\n{}", source("range")));
    super::compile_run(&run, &c, "scope_baseline").unwrap();
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let StoreFactResult::ForallFact(store) = &first.assumed_dom_facts[0].store_and_infer.store
    else {
        panic!()
    };
    let id = store.fact_id;
    original_application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .cite
        .fact_id = id;
    reject(&run, &c, "sibling_citation");
}
#[test]
fn function_constructor_preserves_both_endpoint_wd() {
    for name in ["range", "point_preimage", "set_preimage"] {
        let (mut run, c) = super::execute(source(name));
        let wd = last_equality(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject(&run, &c, "endpoint_wd");
    }
}
#[test]
fn function_constructor_requires_original_constructor_wd_children() {
    for name in ["range", "point_preimage", "set_preimage"] {
        let (mut run, c) = super::execute(source(name));
        right_children(&mut run).clear();
        reject(&run, &c, "wd_children");
    }
}
#[test]
fn function_constructor_requires_original_range_domain_signature() {
    for clear in [false, true] {
        let (mut run, c) = super::execute(source("range"));
        let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::FnRange(p)=right_wd(&mut run) else{panic!()};
        assert!(!p.function_domains.is_empty());
        if clear {
            p.function_domains.clear()
        } else {
            p.function_domains[0].signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C))
        }
        reject(&run, &c, "original_range_signature");
    }
}
#[test]
fn function_constructor_requires_original_preimage_signature_and_builder() {
    for name in ["point_preimage", "set_preimage"] {
        for signature in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let p = preimage_construction(&mut run);
            if signature {
                p.source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C))
            } else {
                p.builder.param_set = Box::new(Obj::StandardSet(StandardSet::C))
            }
            reject(&run, &c, "original_preimage_construction");
        }
    }
}
#[test]
fn function_constructor_keeps_point_and_set_target_predicates_distinct() {
    for name in ["point_preimage", "set_preimage"] {
        let (mut run, c) = super::execute(source(name));
        let p = preimage_construction(&mut run);
        match p.builder.facts.last_mut().unwrap() {
            QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(f)) => {
                f.right = Obj::StandardSet(StandardSet::C)
            }
            QuantifierFreeFact::AtomicFact(AtomicFact::InFact(f)) => {
                f.set = Obj::StandardSet(StandardSet::C)
            }
            _ => panic!(),
        };
        reject(&run, &c, "target_predicate");
    }
}
#[test]
fn function_constructor_requires_original_set_target_sethood() {
    let (mut run, c) = super::execute(source("set_preimage"));
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::PreimageSet(p)=right_wd(&mut run) else{panic!()};
    assert_eq!(p.requirement_fact_verified.len(), 1);
    p.requirement_fact_verified.clear();
    reject(&run, &c, "set_target_sethood");
}
#[test]
fn function_constructor_requires_original_nested_matches() {
    for name in ["range_nested", "point_nested", "set_nested"] {
        let (mut run, c) = super::execute(source(name));
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,true) else{panic!()};
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
        child_matches.clear();
        reject(&run, &c, "nested_arity");
    }
}
#[test]
fn function_constructor_preserves_source_guards_bodies_and_targets() {
    for changed in [
        source("range_guard").replace("fc41_guard_w>0", "fc41_guard_w>1"),
        source("range_body").replace("{fc41_w+1}", "{fc41_w+2}"),
        source("point_preimage").replace("{replay41_qw},1)", "{replay41_qw},2)"),
        source("set_target_alpha").replace("fn(fc41_st_b R) R)", "fn(fc41_st_b R) C)"),
    ] {
        let cmd = parse_launch_command(&["-strict".into(), "-e".into(), changed.clone()]).unwrap();
        let mut rt =
            Runtime::new_with_result_detail(cmd, crate::result_detail::OutputDetail::Detailed);
        assert!(
            !rt.run_litex_code(&changed).unwrap().success,
            "changed source unexpectedly accepted: {changed}"
        );
    }
}
#[test]
fn function_constructor_accepts_group_packaging_without_signature_weakening() {
    let (mut run, c) = super::execute(source("range_groups"));
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::FnRange(p)=right_wd(&mut run) else{panic!()};
    let actual = p.function_domains[0].signature.clone();
    assert_eq!(actual.set_bound_parameters.groups.len(), 1);
    assert_eq!(actual.set_bound_parameters.groups[0].params.len(), 2);
    let mut expanded = actual.clone();
    let first = expanded.set_bound_parameters.groups[0].clone();
    expanded.set_bound_parameters.groups = first
        .params
        .iter()
        .map(|param| {
            let mut group = first.clone();
            group.params = vec![param.clone()];
            group
        })
        .collect();
    let carrier = Obj::FunctionSpace(FunctionSpace::FnSet(actual));
    c.validate_function_carrier_signature(&carrier, &expanded)
        .unwrap();
    for change in 0..6 {
        let mut bad = expanded.clone();
        match change {
            0 => bad.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            1 => {
                bad.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::C))
            }
            2 => {
                bad.set_bound_parameters.groups.pop();
            }
            3 => bad.set_bound_parameters.groups[0].params.clear(),
            4 => {
                bad.set_bound_parameters.groups[1].params[0].id =
                    bad.set_bound_parameters.groups[0].params[0].id
            }
            _ => {
                bad.dom_facts
                    .push(QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(
                        EqualFact {
                            fact_id: FactId::new(u64::MAX),
                            left: Obj::StandardSet(StandardSet::R),
                            right: Obj::StandardSet(StandardSet::C),
                            line_file: None,
                        },
                    )));
            }
        }
        assert!(c
            .validate_function_carrier_signature(&carrier, &bad)
            .is_err());
    }
}
#[test]
fn function_constructor_preserves_selected_group_normalization_and_signature_proof() {
    for change in 0..3 {
        let (mut run, c) = super::execute(source("range_groups"));
        let p = original_application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap();
        let atomic = super::atomic_proof_mut(&mut p.param_type_requirements[0].proof);
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::InFactSearchProofByKnownSpecialProperty::DeclaredFunctionInExactCarrier(selected)))=&mut atomic.searched_proof else{panic!("original grouped selected carrier proof")};
        assert_eq!(
            selected
                .declared_signature
                .set_bound_parameters
                .groups
                .len(),
            1
        );
        assert_eq!(
            selected
                .normalized_signature
                .set_bound_parameters
                .groups
                .len(),
            2
        );
        match change {
            0 => selected.declared_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            1 => selected.normalized_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            _ => selected.target_signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
        };
        reject(&run, &c, "selected_group_normalization");
    }
}
fn right_wd(run:&mut RunLitexCodeResult)->&mut crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef{
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::FunctionSpace(p),..}=last_equality(run).well_defined_proof.as_detailed_mut().unwrap().right.as_detailed_mut().unwrap() else{panic!()};
    p
}
fn right_children(
    run: &mut RunLitexCodeResult,
) -> &mut Vec<
    Box<crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProof>,
> {
    match right_wd(run){crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::FnRange(p)=>&mut p.child_obj_well_defined,crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::Preimage(p)=>&mut p.child_obj_well_defined,crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::PreimageSet(p)=>&mut p.child_obj_well_defined,_=>panic!()}
}
fn preimage_construction(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof {
    match right_wd(run){crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::Preimage(p)=>&mut p.construction,crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::PreimageSet(p)=>&mut p.construction,_=>panic!()}
}
fn source(name: &str) -> &'static str {
    SOURCES.iter().find(|(n, _)| *n == name).unwrap().1
}

fn constructor_match(run:&mut RunLitexCodeResult,right:bool)->&mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof{
    let roots = &mut original_application(run)
        .as_detailed_mut()
        .unwrap()
        .arg_match_proofs;
    if right {
        return roots[1].as_detailed_mut().unwrap();
    }
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=roots[0].as_detailed_mut().unwrap() else{panic!()};
    child_matches[0].as_detailed_mut().unwrap()
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

const SOURCES:&[(&str,&str)]=&[
("range","# Subtracting the empty set preserves a function image,also at renamed formula functions.\n# Former source:the two active statements below;strict source success,statement2 compiler rejection.\n# Former compiler result:CompoundKnown/StructureConstructor.\n# Replay now composes original ordered function matches and scoped range WD.\nforall replay41_g fn(replay41_gx R) R:\n    set_minus(fn_range(replay41_g),{})=fn_range(replay41_g)\nset_minus(fn_range(fn(replay41_gv R) R {replay41_gv}),{})=fn_range(fn(replay41_gw R) R {replay41_gw})\n# Check:litex -lean -strict -f corpus case function_range_empty_subtraction\n"),
("set_preimage","forall replay41_p fn(replay41_px R) R:\n    set_minus(preimage_set(replay41_p,R),{})=preimage_set(replay41_p,R)\nset_minus(preimage_set(fn(replay41_pv R) R {replay41_pv},R),{})=preimage_set(fn(replay41_pw R) R {replay41_pw},R)\n"),
("point_preimage","forall replay41_q fn(replay41_qx R) R,replay41_qy R:\n    set_minus(preimage(replay41_q,replay41_qy),{})=preimage(replay41_q,replay41_qy)\nset_minus(preimage(fn(replay41_qv R) R {replay41_qv},1),{})=preimage(fn(replay41_qw R) R {replay41_qw},1)\n"),
("range_body","forall replay41_g fn(replay41_gx R) R:\n    set_minus(fn_range(replay41_g),{})=fn_range(replay41_g)\nset_minus(fn_range(fn(fc41_v R) R {fc41_v+1}),{})=fn_range(fn(fc41_w R) R {fc41_w+1})\n"),
("range_guard","forall fc41_guard_f fn(fc41_guard_x R:fc41_guard_x>0) R:\n    set_minus(fn_range(fc41_guard_f),{})=fn_range(fc41_guard_f)\nset_minus(fn_range(fn(fc41_guard_v R:fc41_guard_v>0) R {fc41_guard_v}),{})=fn_range(fn(fc41_guard_w R:fc41_guard_w>0) R {fc41_guard_w})\n"),
("range_groups","forall fc41_group_f fn(fc41_group_x,fc41_group_y R) R:\n    set_minus(fn_range(fc41_group_f),{})=fn_range(fc41_group_f)\nset_minus(fn_range(fn(fc41_group_v,fc41_group_u R) R {fc41_group_v+fc41_group_u}),{})=fn_range(fn(fc41_group_w,fc41_group_t R) R {fc41_group_w+fc41_group_t})\n"),
("range_complex","forall fc41_complex_f fn(fc41_complex_x C) C:\n    set_minus(fn_range(fc41_complex_f),{})=fn_range(fc41_complex_f)\nset_minus(fn_range(fn(fc41_complex_v C) C {fc41_complex_v}),{})=fn_range(fn(fc41_complex_w C) C {fc41_complex_w})\n"),
("point_guard","forall fc41_guard_f fn(fc41_guard_x R:fc41_guard_x>0) R:\n    set_minus(preimage(fc41_guard_f,1),{})=preimage(fc41_guard_f,1)\nset_minus(preimage(fn(fc41_guard_v R:fc41_guard_v>0) R {fc41_guard_v},1),{})=preimage(fn(fc41_guard_w R:fc41_guard_w>0) R {fc41_guard_w},1)\n"),
("point_groups","forall fc41_group_f fn(fc41_group_x,fc41_group_y R) R:\n    set_minus(preimage(fc41_group_f,1),{})=preimage(fc41_group_f,1)\nset_minus(preimage(fn(fc41_group_v,fc41_group_u R) R {fc41_group_v+fc41_group_u},1),{})=preimage(fn(fc41_group_w,fc41_group_t R) R {fc41_group_w+fc41_group_t},1)\n"),
("point_complex","forall fc41_complex_f fn(fc41_complex_x C) C:\n    set_minus(preimage(fc41_complex_f,1),{})=preimage(fc41_complex_f,1)\nset_minus(preimage(fn(fc41_complex_v C) C {fc41_complex_v},1),{})=preimage(fn(fc41_complex_w C) C {fc41_complex_w},1)\n"),
("set_guard","forall fc41_guard_f fn(fc41_guard_x R:fc41_guard_x>0) R:\n    set_minus(preimage_set(fc41_guard_f,R),{})=preimage_set(fc41_guard_f,R)\nset_minus(preimage_set(fn(fc41_guard_v R:fc41_guard_v>0) R {fc41_guard_v},R),{})=preimage_set(fn(fc41_guard_w R:fc41_guard_w>0) R {fc41_guard_w},R)\n"),
("set_groups","forall fc41_group_f fn(fc41_group_x,fc41_group_y R) R:\n    set_minus(preimage_set(fc41_group_f,R),{})=preimage_set(fc41_group_f,R)\nset_minus(preimage_set(fn(fc41_group_v,fc41_group_u R) R {fc41_group_v+fc41_group_u},R),{})=preimage_set(fn(fc41_group_w,fc41_group_t R) R {fc41_group_w+fc41_group_t},R)\n"),
("set_complex","forall fc41_complex_f fn(fc41_complex_x C) C:\n    set_minus(preimage_set(fc41_complex_f,C),{})=preimage_set(fc41_complex_f,C)\nset_minus(preimage_set(fn(fc41_complex_v C) C {fc41_complex_v},C),{})=preimage_set(fn(fc41_complex_w C) C {fc41_complex_w},C)\n"),
("set_target_alpha","forall fc41_target_f fn(fc41_target_x R) R,fc41_target_A set:\n    set_minus(preimage_set(fc41_target_f,fc41_target_A),{})=preimage_set(fc41_target_f,fc41_target_A)\nset_minus(preimage_set(fn(fc41_st_v R) R {fc41_st_v},fn(fc41_st_a R) R),{})=preimage_set(fn(fc41_st_w R) R {fc41_st_w},fn(fc41_st_b R) R)\n"),
("point_target_alpha","forall fc41_value_f fn(fc41_value_x R) R,fc41_value_y set:\n    set_minus(preimage(fc41_value_f,fc41_value_y),{})=preimage(fc41_value_f,fc41_value_y)\nset_minus(preimage(fn(fc41_pt_v R) R {fc41_pt_v},fn(fc41_pt_a R) R),{})=preimage(fn(fc41_pt_w R) R {fc41_pt_w},fn(fc41_pt_b R) R)\n"),
("point_target_calc","forall replay41_q fn(replay41_qx R) R,replay41_qy R:\n    set_minus(preimage(replay41_q,replay41_qy),{})=preimage(replay41_q,replay41_qy)\nset_minus(preimage(fn(fc41_pc_v R) R {fc41_pc_v},1+0),{})=preimage(fn(fc41_pc_w R) R {fc41_pc_w},1)\n"),
("range_returned","forall replay41_g fn(replay41_gx R) R:\n    set_minus(fn_range(replay41_g),{})=fn_range(replay41_g)\nforall fc41_return_h fn(fc41_return_a R) fn(fc41_return_x R) R:\n    fc41_return_h(0) $in fn(fc41_return_z R) R\n    set_minus(fn_range(fc41_return_h(0)),{})=fn_range(fc41_return_h(0))\n"),
("range_nested","forall fc41_nested_f fn(fc41_nested_x R) R:\n    set_minus(power_set(fn_range(fc41_nested_f)),{})=power_set(fn_range(fc41_nested_f))\nset_minus(power_set(fn_range(fn(fc41_nested_v R) R {fc41_nested_v})),{})=power_set(fn_range(fn(fc41_nested_w R) R {fc41_nested_w}))\n"),
("point_returned","forall replay41_q fn(replay41_qx R) R,replay41_qy R:\n    set_minus(preimage(replay41_q,replay41_qy),{})=preimage(replay41_q,replay41_qy)\nforall fc41_return_h fn(fc41_return_a R) fn(fc41_return_x R) R:\n    fc41_return_h(0) $in fn(fc41_return_z R) R\n    set_minus(preimage(fc41_return_h(0),1),{})=preimage(fc41_return_h(0),1)\n"),
("point_nested","forall fc41_nested_f fn(fc41_nested_x R) R:\n    set_minus(power_set(preimage(fc41_nested_f,1)),{})=power_set(preimage(fc41_nested_f,1))\nset_minus(power_set(preimage(fn(fc41_nested_v R) R {fc41_nested_v},1)),{})=power_set(preimage(fn(fc41_nested_w R) R {fc41_nested_w},1))\n"),
("set_returned","forall replay41_p fn(replay41_px R) R:\n    set_minus(preimage_set(replay41_p,R),{})=preimage_set(replay41_p,R)\nforall fc41_return_h fn(fc41_return_a R) fn(fc41_return_x R) R:\n    fc41_return_h(0) $in fn(fc41_return_z R) R\n    set_minus(preimage_set(fc41_return_h(0),R),{})=preimage_set(fc41_return_h(0),R)\n"),
("set_nested","forall fc41_nested_f fn(fc41_nested_x R) R:\n    set_minus(power_set(preimage_set(fc41_nested_f,R)),{})=power_set(preimage_set(fc41_nested_f,R))\nset_minus(power_set(preimage_set(fn(fc41_nested_v R) R {fc41_nested_v},R)),{})=power_set(preimage_set(fn(fc41_nested_w R) R {fc41_nested_w},R))\n"),
("range_empty_domain","forall fc41_empty_f fn(fc41_empty_x {}) R:\n    set_minus(fn_range(fc41_empty_f),{})=fn_range(fc41_empty_f)\nset_minus(fn_range(fn(fc41_empty_v {}) R {0}),{})=fn_range(fn(fc41_empty_w {}) R {0})\n"),
];
