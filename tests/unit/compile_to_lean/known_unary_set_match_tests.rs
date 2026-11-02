use crate::prelude::*;

#[test]
fn known_unary_set_original_power_family_literal_trees() {
    for (family, source) in [(false, POWER), (true, FAMILY)] {
        let (mut run, compiler) = super::execute(source);
        let proof = application(&mut run);
        let matches = &proof.detailed_ref().arg_match_proofs;
        assert_eq!(matches.len(), 2);
        if family {
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {pattern, goal_arg, child_matches} = matches[0].detailed_ref() else {panic!("original family union")};
            assert!(matches!(
                pattern,
                Obj::SetOperator(SetOperator::FamilyUnion(_))
            ));
            assert!(matches!(
                goal_arg,
                Obj::SetOperator(SetOperator::FamilyUnion(_))
            ));
            assert_eq!(child_matches.len(), 1);
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {pattern, goal_arg, child_matches} = child_matches[0].detailed_ref() else {panic!("original literal child")};
            assert!(matches!(pattern, Obj::SetFormer(SetFormer::ListSet(_))));
            assert!(matches!(goal_arg, Obj::SetFormer(SetFormer::ListSet(_))));
            assert_eq!(child_matches.len(), 1);
            assert!(matches!(child_matches[0].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam {..}));
            assert!(matches!(matches[1].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {..}));
        } else {
            assert!(matches!(matches[0].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam {..}));
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure {pattern, goal_arg, child_matches} = matches[1].detailed_ref() else {panic!("original powerset")};
            assert!(matches!(
                pattern,
                Obj::SetOperator(SetOperator::PowerSet(_))
            ));
            assert!(matches!(
                goal_arg,
                Obj::SetOperator(SetOperator::PowerSet(_))
            ));
            assert_eq!(child_matches.len(), 1);
            assert!(matches!(child_matches[0].detailed_ref(), crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual {..}));
        }
        let output = super::compile_run(&run, &compiler, "original_unary_tree").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "original_unary_tree").unwrap()
        );
    }
}

#[test]
fn known_unary_set_replays_all_source_profiles() {
    for source in ALL {
        let (run, compiler) = super::execute(source);
        let output = super::compile_run(&run, &compiler, "unary_profiles").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "unary_profiles").unwrap()
        );
    }
}
#[test]
fn known_unary_set_keeps_structure_captured_subjects() {
    for source in [POWER, FAMILY] {
        for pattern_side in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{pattern,goal_arg,..}=root_match(&mut run,source==FAMILY) else{panic!()};
            if pattern_side {
                *pattern = Obj::StandardSet(StandardSet::C)
            } else {
                *goal_arg = Obj::StandardSet(StandardSet::C)
            };
            reject(&run, &compiler, "structure_subject");
        }
    }
}
#[test]
fn known_unary_set_requires_one_original_unary_child() {
    for source in [POWER, FAMILY] {
        for count in [0, 2] {
            let (mut run, compiler) = super::execute(source);
            let (mut donor, _) = super::execute(source);
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut donor,source==FAMILY) else{panic!()};
            let extra = child_matches.pop().unwrap();
            let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut run,source==FAMILY) else{panic!()};
            if count == 0 {
                child_matches.clear()
            } else {
                child_matches.push(extra)
            };
            reject(&run, &compiler, "unary_arity");
        }
    }
}
#[test]
fn known_unary_set_keeps_literal_children() {
    let (mut run, compiler) = super::execute(FAMILY);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut run,true) else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
    child_matches.clear();
    reject(&run, &compiler, "literal_children");
}
#[test]
fn known_unary_set_keeps_bound_parameter_identity() {
    let (mut run, compiler) = super::execute(FAMILY);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut run,true) else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam{param_id,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
    *param_id = IdentifierId::new(u64::MAX);
    reject(&run, &compiler, "bound_identity");
}
#[test]
fn known_unary_set_keeps_original_rebound_subjects() {
    for previous_side in [false, true] {
        let (mut run, compiler) = super::execute(POWER);
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut run,false) else{panic!()};
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{previous,goal_arg,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
        if previous_side {
            *previous = Obj::StandardSet(StandardSet::C)
        } else {
            *goal_arg = Obj::StandardSet(StandardSet::C)
        };
        reject(&run, &compiler, "rebound_subject");
    }
}
#[test]
fn known_unary_set_requires_original_strict_equality() {
    let (mut run, compiler) = super::execute(POWER);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut run,false) else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ReboundParamEqual{equal,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
    equal.equal_fact.left = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "strict_subject");
}
#[test]
fn known_unary_set_preserves_substitution() {
    let (mut run, compiler) = super::execute(FAMILY);
    application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "substitution");
}
#[test]
fn known_unary_set_requires_all_set_requirements() {
    for source in [POWER, FAMILY] {
        let (mut run, compiler) = super::execute(source);
        application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap()
            .param_type_requirements
            .clear();
        reject(&run, &compiler, "requirements");
    }
}
#[test]
fn known_unary_set_keeps_requirement_subject() {
    let (mut run, compiler) = super::execute(FAMILY);
    let requirements = application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap();
    let AtomicFact::IsSetFact(f) =
        &mut super::atomic_proof_mut(&mut requirements.param_type_requirements[0].proof).fact
    else {
        panic!()
    };
    f.set = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "requirement_subject");
}
#[test]
fn known_unary_set_requires_original_prior_citation() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(FAMILY);
        let target = super::equality_proof_mut(last_verify(&mut run))
            .fact
            .fact_id;
        application(&mut run)
            .as_detailed_mut()
            .unwrap()
            .cite
            .fact_id = if missing {
            FactId::new(u64::MAX)
        } else {
            target
        };
        reject(&run, &compiler, "citation");
    }
}
#[test]
fn known_unary_set_cannot_borrow_closed_sibling_citation() {
    let private="forall unary38_private R:\n    forall unary38_private_U set:\n        family_union({unary38_private_U})=unary38_private_U\n    =>:\n        unary38_private=unary38_private\n";
    let (mut run, compiler) = super::execute(&format!("{private}\n{FAMILY}"));
    super::compile_run(&run, &compiler, "private_baseline").unwrap();
    let proof = super::forall_proof_mut(&mut run.statement_results[0]);
    let StoreFactResult::ForallFact(store) = &proof.assumed_dom_facts[0].store_and_infer.store
    else {
        panic!()
    };
    let foreign = store.fact_id;
    application(&mut run)
        .as_detailed_mut()
        .unwrap()
        .cite
        .fact_id = foreign;
    reject(&run, &compiler, "private_citation");
}
#[test]
fn known_unary_set_keeps_original_family_child_wd() {
    let (mut run, compiler) = super::execute(FAMILY);
    let proof = super::equality_proof_mut(last_verify(&mut run));
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetOperator(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::FamilyUnion(p)),..}=proof.well_defined_proof.as_detailed_mut().unwrap().left.as_detailed_mut().unwrap() else{panic!()};
    p.child_obj_well_defined.clear();
    reject(&run, &compiler, "family_child_wd");
}
#[test]
fn known_unary_set_keeps_endpoint_wd_subjects() {
    let (mut run, compiler) = super::execute(FAMILY);
    let wd = super::equality_proof_mut(last_verify(&mut run))
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut wd.left, &mut wd.right);
    reject(&run, &compiler, "endpoint_wd");
}
#[test]
fn known_unary_set_keeps_literal_pair_original_order() {
    let (mut run, compiler) = super::execute(PAIR);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut run,true) else{panic!()};
    assert_eq!(child_matches.len(), 2);
    child_matches.swap(0, 1);
    reject(&run, &compiler, "literal_order");
}
#[test]
fn known_unary_set_requires_literal_pair_distinctness() {
    let (mut run, compiler) = super::execute(PAIR);
    let proof = super::atomic_proof_mut(last_verify(&mut run));
    let wd = proof.well_defined_proof.as_detailed_mut().unwrap();
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetFormer(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef::ListSet(p)),..}=wd.well_defined_of_each_parameter[0].as_detailed_mut().unwrap() else{panic!()};
    assert_eq!(p.requirement_fact_verified.len(), 1);
    p.requirement_fact_verified.clear();
    reject(&run, &compiler, "literal_distinctness");
}
#[test]
fn known_unary_set_keeps_literal_pair_distinctness_subject() {
    let (mut run, compiler) = super::execute(PAIR);
    let proof = super::atomic_proof_mut(last_verify(&mut run));
    let wd = proof.well_defined_proof.as_detailed_mut().unwrap();
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{proof:crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProofByDef::SetFormer(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef::ListSet(p)),..}=wd.well_defined_of_each_parameter[0].as_detailed_mut().unwrap() else{panic!()};
    let AtomicFact::NotEqualFact(f) =
        &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[0]).fact
    else {
        panic!()
    };
    f.right = Obj::StandardSet(StandardSet::C);
    reject(&run, &compiler, "distinctness_subject");
}
#[test]
fn known_unary_set_requires_nested_literal_matches() {
    let (mut run, compiler) = super::execute(NESTED);
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=root_match(&mut run,true) else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::ByStructure{child_matches,..}=child_matches[0].as_detailed_mut().unwrap() else{panic!()};
    child_matches.clear();
    reject(&run, &compiler, "nested_literal");
}
#[test]
fn known_unary_set_does_not_change_carrier_guards() {
    for source in [
        GUARD.replace("replay38_pgw>0", "replay38_pgw>1"),
        FAMILY.replace("fn(replay38_uw R) R", "fn(replay38_uw C) R"),
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.clone()])
                .unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!runtime.run_litex_code(&source).unwrap().success);
    }
}

fn application(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact{
    match last_verify(run) {
        VerifyFactResult::Equality(result) => {
            let VerifyEqualityResult::Success(p) = result.as_mut() else {
                panic!()
            };
            let EqualFactSearchedProof::ByKnownForallFact(p) = &mut p.searched_proof else {
                panic!("original equality known forall")
            };
            p
        }
        VerifyFactResult::AtomicExceptEquality(result) => {
            let VerifyAtomicExceptEqualityFactResult::Success(p) = result.as_mut() else {
                panic!()
            };
            let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) = &mut p.searched_proof
            else {
                panic!("original membership known forall")
            };
            p
        }
        _ => panic!(),
    }
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
fn root_match(run:&mut RunLitexCodeResult,first:bool)->&mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof{
    application(run).as_detailed_mut().unwrap().arg_match_proofs[if first { 0 } else { 1 }]
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
        "altered evidence accepted: {name}"
    );
}
const POWER:&str="# Powerset self-membership reuses the structure of an ordinary mathematical statement.\n# Former source (strict source success, second statement compiler rejection):\n# forall replay38_Z set:\n#     replay38_Z $in power_set(replay38_Z)\n# fn(replay38_zv R) R $in power_set(fn(replay38_zw R) R)\n# Former compiler result: CompoundKnown/StructureConstructor.\n# Current path consumes the original rebound equality and constructor WD.\n# Instantiate powerset self-membership at alpha-renamed carriers.\nforall replay38_Z set:\n    replay38_Z $in power_set(replay38_Z)\nfn(replay38_zv R) R $in power_set(fn(replay38_zw R) R)\n# Check: litex -lean -strict -f lean/examples/known_unary_power/statement.lit\n";
const FAMILY:&str="# Reuse singleton-family union at alpha-renamed function-space carriers.\nforall replay38_U set:\n    family_union({replay38_U})=replay38_U\nfamily_union({fn(replay38_uv R) R})=fn(replay38_uw R) R\n";
const PAIR:&str="# Finite literal formation retains its original pairwise-distinctness premise.\nforall replay38_LA,replay38_LB set:\n    replay38_LA!=replay38_LB\n    =>:\n        {replay38_LA,replay38_LB} $in power_set({replay38_LA,replay38_LB})\nforall replay38_LS set:\n    fn(replay38_lpv R) R!=replay38_LS\n    =>:\n        {fn(replay38_lpv R) R,replay38_LS} $in power_set({fn(replay38_lpw R) R,replay38_LS})\n";
const NESTED:&str="# Replay nested nonempty literal constructors in a singleton family.\nforall replay38_FN set:\n    family_union({{replay38_FN}})={replay38_FN}\nfamily_union({{fn(replay38_fnv R) R}})={fn(replay38_fnw R) R}\n";
const GUARD:&str="# Retain the original positive-domain function-space guard.\nforall replay38_Z set:\n    replay38_Z $in power_set(replay38_Z)\nfn(replay38_pgv R:replay38_pgv>0) R $in power_set(fn(replay38_pgw R:replay38_pgw>0) R)\n";
const ALL:&[&str]=&[
"# Powerset self-membership reuses the structure of an ordinary mathematical statement.\n# Former source (strict source success, second statement compiler rejection):\n# forall replay38_Z set:\n#     replay38_Z $in power_set(replay38_Z)\n# fn(replay38_zv R) R $in power_set(fn(replay38_zw R) R)\n# Former compiler result: CompoundKnown/StructureConstructor.\n# Current path consumes the original rebound equality and constructor WD.\n# Instantiate powerset self-membership at alpha-renamed carriers.\nforall replay38_Z set:\n    replay38_Z $in power_set(replay38_Z)\nfn(replay38_zv R) R $in power_set(fn(replay38_zw R) R)\n# Check: litex -lean -strict -f lean/examples/known_unary_power/statement.lit\n",
"# Retain the original positive-domain function-space guard.\nforall replay38_Z set:\n    replay38_Z $in power_set(replay38_Z)\nfn(replay38_pgv R:replay38_pgv>0) R $in power_set(fn(replay38_pgw R:replay38_pgw>0) R)\n",
"# Preserve ordered mixed parameter groups in repeated carrier matches.\nforall replay38_Z set:\n    replay38_Z $in power_set(replay38_Z)\nfn(replay38_pmv R,replay38_pmu C) C $in power_set(fn(replay38_pmw R,replay38_pmt C) C)\n",
"# Compose original powerset matches at two constructor depths.\nforall replay38_N set:\n    power_set(replay38_N) $in power_set(power_set(replay38_N))\npower_set(fn(replay38_pnv R) R) $in power_set(power_set(fn(replay38_pnw R) R))\n",
"# Finite literal formation retains its original pairwise-distinctness premise.\nforall replay38_LA,replay38_LB set:\n    replay38_LA!=replay38_LB\n    =>:\n        {replay38_LA,replay38_LB} $in power_set({replay38_LA,replay38_LB})\nforall replay38_LS set:\n    fn(replay38_lpv R) R!=replay38_LS\n    =>:\n        {fn(replay38_lpv R) R,replay38_LS} $in power_set({fn(replay38_lpw R) R,replay38_LS})\n",
"# Reuse the original returned natural membership in a finite carrier bound.\nforall replay38_Z set:\n    replay38_Z $in power_set(replay38_Z)\nforall replay38_h fn(replay38_t R) N,replay38_a R:\n    replay38_h(replay38_a) $in N\n    fn(replay38_prv closed_range(1,replay38_h(replay38_a))) R $in power_set(fn(replay38_prw closed_range(1,replay38_h(replay38_a))) R)\n",
"# Reuse singleton-family union at alpha-renamed function-space carriers.\nforall replay38_U set:\n    family_union({replay38_U})=replay38_U\nfamily_union({fn(replay38_uv R) R})=fn(replay38_uw R) R\n",
"# Retain the original guarded singleton-family element.\nforall replay38_U set:\n    family_union({replay38_U})=replay38_U\nfamily_union({fn(replay38_fgv R:replay38_fgv>0) R})=fn(replay38_fgw R:replay38_fgw>0) R\n",
"# Preserve the mixed parameter groups inside a singleton-family element.\nforall replay38_U set:\n    family_union({replay38_U})=replay38_U\nfamily_union({fn(replay38_fmv R,replay38_fmu C) C})=fn(replay38_fmw R,replay38_fmt C) C\n",
"# Replay nested nonempty literal constructors in a singleton family.\nforall replay38_FN set:\n    family_union({{replay38_FN}})={replay38_FN}\nfamily_union({{fn(replay38_fnv R) R}})={fn(replay38_fnw R) R}\n",
"# Compose the powerset and family-union semantic constructors.\nforall replay38_FP set:\n    family_union(power_set(replay38_FP))=replay38_FP\nfamily_union(power_set(fn(replay38_fpv R) R))=fn(replay38_fpw R) R\n",
];
