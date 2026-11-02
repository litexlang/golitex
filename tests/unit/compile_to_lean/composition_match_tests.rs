use crate::prelude::*;

#[test]
fn composition_match_original_ordered_tree_and_compatibility() {
    let (mut run, c) = super::execute(SOURCE);
    assert_eq!(
        original_application(&mut run)
            .detailed_ref()
            .arg_match_proofs
            .len(),
        2
    );
    for right in [false, true] {
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{pattern,goal_arg,child_matches}=constructor_match(&mut run,right) else{panic!()};
        assert!(matches!(
            pattern,
            Obj::FunctionSpace(FunctionSpace::Composition(_))
        ));
        assert!(matches!(
            goal_arg,
            Obj::FunctionSpace(FunctionSpace::Composition(_))
        ));
        assert_eq!(child_matches.len(), 2);
        for p in child_matches {
            assert!(if right {
                matches!(p.detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{..})
            } else {
                matches!(p.detailed_ref(),crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam{..})
            });
        }
    }
    let p = composition_wd(&mut run);
    assert_eq!(
        p.outer_domain
            .signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum::<usize>(),
        1
    );
    assert_eq!(
        p.inner_domain
            .signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.params.len())
            .sum::<usize>(),
        1
    );
    assert!(matches!(p.function.equal_to.as_ref(), Obj::FnObj(_)));
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::FunctionSpace(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(checked)),..}=p.function_well_defined.detailed_ref() else{panic!()};
    assert!(matches!(checked.body_well_defined.detailed_ref(),crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::FnObj(_),..}));
    eprintln!(
        "ORIGINAL42 outer={} inner={} expanded={}",
        p.outer_domain.signature.display_string(),
        p.inner_domain.signature.display_string(),
        p.function.equal_to.display_string()
    );
    let output = super::compile_run(&run, &c, "composition_original_tree").unwrap();
    assert_eq!(
        output,
        super::compile_run(&run, &c, "composition_original_tree").unwrap()
    );
}
#[test]
fn composition_match_preserves_captured_constructor_subjects() {
    for name in ["basic"] {
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
fn composition_match_requires_exact_original_child_arity() {
    for name in ["basic"] {
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
fn composition_match_preserves_function_then_target_order() {
    for name in ["basic"] {
        for right in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,right) else{panic!()};
            child_matches.swap(0, 1);
            reject(&run, &c, "child_order");
        }
    }
}
#[test]
fn composition_match_preserves_bound_identity_and_subjects() {
    for change in 0..3 {
        let (mut run, c) = super::execute(source("basic"));
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
fn composition_match_preserves_rebound_identity_and_subjects() {
    for change in 0..4 {
        let (mut run, c) = super::execute(source("basic"));
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
fn composition_match_preserves_original_substitution() {
    for name in ["basic"] {
        let (mut run, c) = super::execute(source(name));
        original_application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::C);
        reject(&run, &c, "substitution");
    }
}
#[test]
fn composition_match_requires_all_original_instantiation_requirements() {
    for name in ["basic"] {
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
fn composition_match_preserves_original_membership_requirement_subject() {
    let (mut run, c) = super::execute(source("basic"));
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
fn composition_match_requires_original_prior_citation() {
    for missing in [false, true] {
        let (mut run, c) = super::execute(source("basic"));
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
fn composition_match_cannot_borrow_closed_sibling_theorem() {
    let private="forall fc41_private R:\n    forall fc41_private_A set:\n        set_minus(fc41_private_A,{})=fc41_private_A\n    =>:\n        fc41_private=fc41_private\n";
    let (mut run, c) = super::execute(&format!("{private}\n{}", source("basic")));
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
fn composition_match_preserves_both_endpoint_wd() {
    for name in ["basic"] {
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
fn composition_match_all_actual_profiles_deterministically() {
    let mut errors = Vec::new();
    for (name, code) in SOURCES {
        let (run, c) = super::execute(code);
        match super::compile_run(&run, &c, name) {
            Ok(text) => assert_eq!(text, super::compile_run(&run, &c, name).unwrap()),
            Err(e) => errors.push(format!("{name}: {e}")),
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}
#[test]
fn composition_match_preserves_original_operand_wd_order() {
    let (mut run, c) = super::execute(source("basic"));
    let p = composition_wd(&mut run);
    std::mem::swap(&mut p.outer_well_defined, &mut p.inner_well_defined);
    reject(&run, &c, "operand_wd_order");
}
#[test]
fn composition_match_preserves_original_complete_domain_owners() {
    let (mut run, c) = super::execute(source("basic"));
    let p = composition_wd(&mut run);
    std::mem::swap(&mut p.outer_domain, &mut p.inner_domain);
    reject(&run, &c, "complete_domain_owners");
}
#[test]
fn composition_match_preserves_each_complete_interface() {
    for outer in [false, true] {
        let (mut run, c) = super::execute(source("basic"));
        let p = composition_wd(&mut run);
        let domain = if outer {
            &mut p.outer_domain
        } else {
            &mut p.inner_domain
        };
        domain.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        reject(&run, &c, "complete_interface");
    }
}
#[test]
fn composition_match_preserves_expanded_compatibility_signature() {
    let (mut run, c) = super::execute(source("basic"));
    composition_wd(&mut run).function.body.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    reject(&run, &c, "expanded_signature");
}
#[test]
fn composition_match_preserves_expanded_outer_inner_application() {
    let (mut run, c) = super::execute(source("basic"));
    composition_wd(&mut run).function.equal_to = Box::new(Obj::StandardSet(StandardSet::R));
    reject(&run, &c, "expanded_application");
}
#[test]
fn composition_match_requires_original_expanded_lambda_wd() {
    let (mut run, c) = super::execute(source("basic"));
    let p = composition_wd(&mut run);
    std::mem::swap(&mut p.function_well_defined, &mut p.outer_well_defined);
    reject(&run, &c, "expanded_lambda_wd");
}
#[test]
fn composition_match_keeps_original_compatibility_call_stages() {
    let (mut run, c) = super::execute(source("basic"));
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::FunctionSpace(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(p)),..}=composition_wd(&mut run).function_well_defined.as_detailed_mut().unwrap() else{panic!()};
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::FnObj(call),..}=p.body_well_defined.as_detailed_mut().unwrap() else{panic!()};
    call.child_obj_well_defined.clear();
    reject(&run, &c, "compatibility_call_stages");
}
#[test]
fn composition_match_keeps_original_compatibility_binder_stages() {
    let (mut run, c) = super::execute(source("basic"));
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::FunctionSpace(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(p)),..}=composition_wd(&mut run).function_well_defined.as_detailed_mut().unwrap() else{panic!()};
    p.param_type_well_defined.clear();
    reject(&run, &c, "compatibility_binder_stages");
}
#[test]
fn composition_match_requires_original_nested_constructor_children() {
    let (mut run, c) = super::execute(source("nested_composition"));
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=constructor_match(&mut run,false) else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
    child_matches.clear();
    reject(&run, &c, "nested_children");
}
#[test]
fn composition_match_preserves_source_bodies_and_guards() {
    for code in [source("basic").replace("{replay42_w}","{replay42_w+2}"),source("guarded_inner").replace("comp42_gt>0","comp42_gt>1"),"$is_set(compose(fn(comp42_bad_x R:comp42_bad_x>0) R {comp42_bad_x},fn(comp42_bad_y R) R {0}))\n".to_string()]{let cmd=parse_launch_command(&["-strict".into(),"-e".into(),code.clone()]).unwrap();let mut rt=Runtime::new_with_result_detail(cmd,crate::result_detail::OutputDetail::Detailed);assert!(!rt.run_litex_code(&code).unwrap().success,"changed mathematical source accepted: {code}");}
}
#[test]
fn composition_match_original_equality_congruence_tree() {
    let (mut run, c) = super::execute(source("returned_both"));
    let p = composition_equality(&mut run);
    assert!(matches!(
        p.fact.left,
        Obj::FunctionSpace(FunctionSpace::Composition(_))
    ));
    assert!(matches!(
        p.fact.right,
        Obj::FunctionSpace(FunctionSpace::Composition(_))
    ));
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &p.searched_proof else {
        panic!("original equality constructor peel")
    };
    assert_eq!(p.corresponding_arg_equal_proofs.len(), 2);
    super::compile_run(&run, &c, "original_equality_peel").unwrap();
}
#[test]
fn composition_match_equality_requires_two_original_children() {
    for extra in [false, true] {
        let (mut run, c) = super::execute(source("returned_both"));
        let (mut donor, _) = super::execute(source("returned_both"));
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) =
            &mut composition_equality(&mut donor).searched_proof
        else {
            panic!()
        };
        let spare = p.corresponding_arg_equal_proofs.pop().unwrap();
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) =
            &mut composition_equality(&mut run).searched_proof
        else {
            panic!()
        };
        if extra {
            p.corresponding_arg_equal_proofs.push(spare)
        } else {
            p.corresponding_arg_equal_proofs.pop();
        }
        reject(&run, &c, "equality_arity");
    }
}
#[test]
fn composition_match_equality_preserves_outer_inner_order() {
    let (mut run, c) = super::execute(source("returned_both"));
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) =
        &mut composition_equality(&mut run).searched_proof
    else {
        panic!()
    };
    p.corresponding_arg_equal_proofs.swap(0, 1);
    reject(&run, &c, "equality_order");
}
#[test]
fn composition_match_equality_preserves_each_child_subject() {
    for index in 0..2 {
        let (mut run, c) = super::execute(source("returned_both"));
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) =
            &mut composition_equality(&mut run).searched_proof
        else {
            panic!()
        };
        super::equality_proof_mut(&mut p.corresponding_arg_equal_proofs[index])
            .fact
            .left = Obj::StandardSet(StandardSet::C);
        reject(&run, &c, "equality_child_subject");
    }
}
#[test]
fn composition_match_equality_preserves_both_endpoint_wd() {
    let (mut run, c) = super::execute(source("returned_both"));
    let p = composition_equality(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut p.left, &mut p.right);
    reject(&run, &c, "equality_endpoint_wd");
}
fn composition_equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    assert_eq!(p.proved_then_facts.len(), 8);
    super::equality_proof_mut(&mut p.proved_then_facts[6].verify_result)
}
fn source(name: &str) -> &'static str {
    SOURCES.iter().find(|(n, _)| *n == name).unwrap().1
}
fn composition_wd(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_fact_stmt::function_composition::CompositionObjWellDefinedProof {
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::FunctionSpace(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::Composition(p)),..}=last_equality(run).well_defined_proof.as_detailed_mut().unwrap().right.as_detailed_mut().unwrap() else{panic!()};
    p
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

const SOURCE:&str="forall replay42_f,replay42_g fn(replay42_x R) R:\n    set_minus(compose(replay42_f,replay42_g),{})=compose(replay42_f,replay42_g)\nset_minus(compose(fn(replay42_v R) R {replay42_v},fn(replay42_u R) R {replay42_u+1}),{})=compose(fn(replay42_w R) R {replay42_w},fn(replay42_t R) R {replay42_t+1})\n";
const SOURCES:&[(&str,&str)]=&[
("basic","# Empty subtraction preserves a composed function,including renamed formula functions.\n# Former source:the active statements below;strict source success,statement2 compiler rejection.\n# Former compiler result:CompoundKnown/StructureConstructor.\n# Replay retains outer-then-inner matches and original compatibility/WD.\nforall replay42_f,replay42_g fn(replay42_x R) R:\n    set_minus(compose(replay42_f,replay42_g),{})=compose(replay42_f,replay42_g)\nset_minus(compose(fn(replay42_v R) R {replay42_v},fn(replay42_u R) R {replay42_u+1}),{})=compose(fn(replay42_w R) R {replay42_w},fn(replay42_t R) R {replay42_t+1})\n# Check:litex -lean -strict -f lean/examples/composed_function_empty_subtraction/statement.lit\n"),
("complex","forall comp42_f,comp42_g fn(comp42_x C) C:\n    set_minus(compose(comp42_f,comp42_g),{})=compose(comp42_f,comp42_g)\nset_minus(compose(fn(comp42_v C) C {comp42_v},fn(comp42_u C) C {comp42_u+1}),{})=compose(fn(comp42_w C) C {comp42_w},fn(comp42_t C) C {comp42_t+1})\n"),
("positive_carrier","forall comp42_pf fn(comp42_px R+) R,comp42_pg fn(comp42_py R+) R+:\n    set_minus(compose(comp42_pf,comp42_pg),{})=compose(comp42_pf,comp42_pg)\nset_minus(compose(fn(comp42_pv R+) R {comp42_pv},fn(comp42_pu R+) R+ {comp42_pu}),{})=compose(fn(comp42_pw R+) R {comp42_pw},fn(comp42_pt R+) R+ {comp42_pt})\n"),
("guarded_inner","forall comp42_gf fn(comp42_gx R) R,comp42_gg fn(comp42_gy R:comp42_gy>0) R:\n    set_minus(compose(comp42_gf,comp42_gg),{})=compose(comp42_gf,comp42_gg)\nset_minus(compose(fn(comp42_gv R) R {comp42_gv},fn(comp42_gu R:comp42_gu>0) R {comp42_gu+1}),{})=compose(fn(comp42_gw R) R {comp42_gw},fn(comp42_gt R:comp42_gt>0) R {comp42_gt+1})\n"),
("grouped_inner","forall comp42_mf fn(comp42_mx R) R,comp42_mg fn(comp42_my,comp42_mz R) R:\n    set_minus(compose(comp42_mf,comp42_mg),{})=compose(comp42_mf,comp42_mg)\nset_minus(compose(fn(comp42_mv R) R {comp42_mv+1},fn(comp42_mu,comp42_ma R) R {comp42_mu+comp42_ma}),{})=compose(fn(comp42_mw R) R {comp42_mw+1},fn(comp42_mt,comp42_mb R) R {comp42_mt+comp42_mb})\n"),
("mixed_inner","forall comp42_cf fn(comp42_cx C) C,comp42_cg fn(comp42_cy R,comp42_cz C) C:\n    set_minus(compose(comp42_cf,comp42_cg),{})=compose(comp42_cf,comp42_cg)\nset_minus(compose(fn(comp42_cv C) C {comp42_cv},fn(comp42_cu R,comp42_ca C) C {comp42_cu+comp42_ca}),{})=compose(fn(comp42_cw C) C {comp42_cw},fn(comp42_ct R,comp42_cb C) C {comp42_ct+comp42_cb})\n"),
("repeated_function","forall comp42_rf fn(comp42_rx R) R:\n    set_minus(compose(comp42_rf,comp42_rf),{})=compose(comp42_rf,comp42_rf)\nset_minus(compose(fn(comp42_rv R) R {comp42_rv},fn(comp42_ru R) R {comp42_ru}),{})=compose(fn(comp42_rw R) R {comp42_rw},fn(comp42_rt R) R {comp42_rt})\n"),
("nested_range","forall comp42_nf,comp42_ng fn(comp42_nx R) R:\n    set_minus(fn_range(compose(comp42_nf,comp42_ng)),{})=fn_range(compose(comp42_nf,comp42_ng))\nset_minus(fn_range(compose(fn(comp42_nv R) R {comp42_nv},fn(comp42_nu R) R {comp42_nu+1})),{})=fn_range(compose(fn(comp42_nw R) R {comp42_nw},fn(comp42_nt R) R {comp42_nt+1}))\n"),
("nested_power","forall comp42_sf,comp42_sg fn(comp42_sx R) R:\n    set_minus(power_set(compose(comp42_sf,comp42_sg)),{})=power_set(compose(comp42_sf,comp42_sg))\nset_minus(power_set(compose(fn(comp42_sv R) R {comp42_sv},fn(comp42_su R) R {comp42_su+1})),{})=power_set(compose(fn(comp42_sw R) R {comp42_sw},fn(comp42_st R) R {comp42_st+1}))\n"),
("nested_composition","forall comp42_af,comp42_ag,comp42_ah fn(comp42_ax R) R:\n    set_minus(compose(compose(comp42_af,comp42_ag),comp42_ah),{})=compose(compose(comp42_af,comp42_ag),comp42_ah)\nset_minus(compose(compose(fn(comp42_av R) R {comp42_av},fn(comp42_au R) R {comp42_au+1}),fn(comp42_aa R) R {comp42_aa}),{})=compose(compose(fn(comp42_aw R) R {comp42_aw},fn(comp42_at R) R {comp42_at+1}),fn(comp42_ab R) R {comp42_ab})\n"),
("returned_outer","forall replay42_f,replay42_g fn(replay42_x R) R:\n    set_minus(compose(replay42_f,replay42_g),{})=compose(replay42_f,replay42_g)\nforall comp42_provider fn(comp42_provider_arg R) fn(comp42_provider_value R) R:\n    comp42_provider(0) $in fn(comp42_provider_x R) R\n    set_minus(compose(comp42_provider(0),fn(comp42_ro R) R {comp42_ro+1}),{})=compose(comp42_provider(0),fn(comp42_rw R) R {comp42_rw+1})\n"),
("returned_inner","forall replay42_f,replay42_g fn(replay42_x R) R:\n    set_minus(compose(replay42_f,replay42_g),{})=compose(replay42_f,replay42_g)\nforall comp42_provider fn(comp42_provider_arg R) fn(comp42_provider_value R) R:\n    comp42_provider(0) $in fn(comp42_provider_x R) R\n    set_minus(compose(fn(comp42_ri R) R {comp42_ri+1},comp42_provider(0)),{})=compose(fn(comp42_rj R) R {comp42_rj+1},comp42_provider(0))\n"),
("returned_both","forall replay42_f,replay42_g fn(replay42_x R) R:\n    set_minus(compose(replay42_f,replay42_g),{})=compose(replay42_f,replay42_g)\nforall comp42_P,comp42_Q fn(comp42_provider_arg R) fn(comp42_provider_value R) R:\n    comp42_P=comp42_Q\n    =>:\n        comp42_P(0) $in fn(comp42_provider_x R) R\n        comp42_Q(0) $in fn(comp42_provider_y R) R\n        comp42_P(1) $in fn(comp42_provider_z R) R\n        comp42_Q(1) $in fn(comp42_provider_w R) R\n        comp42_P(0)=comp42_Q(0)\n        comp42_P(1)=comp42_Q(1)\n        compose(comp42_P(0),comp42_P(1))=compose(comp42_Q(0),comp42_Q(1))\n        set_minus(compose(comp42_P(0),comp42_P(1)),{})=compose(comp42_Q(0),comp42_Q(1))\n"),
("captured_ambient","forall replay42_f,replay42_g fn(replay42_x R) R:\n    set_minus(compose(replay42_f,replay42_g),{})=compose(replay42_f,replay42_g)\nforall comp42_capture R:\n    set_minus(compose(fn(comp42_vv R) R {comp42_vv+comp42_capture},fn(comp42_vu R) R {comp42_vu}),{})=compose(fn(comp42_vw R) R {comp42_vw+comp42_capture},fn(comp42_vt R) R {comp42_vt})\n"),
("power_membership","forall comp42_bf,comp42_bg fn(comp42_bx R) R:\n    compose(comp42_bf,comp42_bg) $in power_set(compose(comp42_bf,comp42_bg))\ncompose(fn(comp42_bv R) R {comp42_bv},fn(comp42_bu R) R {comp42_bu+1}) $in power_set(compose(fn(comp42_bw R) R {comp42_bw},fn(comp42_bt R) R {comp42_bt+1}))\n"),
];
