use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef as FunctionWD;
use crate::prelude::*;

#[test]
fn function_constructor_equality_original_three_ordered_trees() {
    for (name, source) in &SOURCES[..3] {
        let (mut run, compiler) = super::execute(source);
        let theorem = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
        assert_eq!(theorem.proved_then_facts.len(), 1);
        let equality = super::equality_proof_mut(&mut theorem.proved_then_facts[0].verify_result);
        let pairs = crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs(&equality.fact.left, &equality.fact.right).unwrap();
        assert_eq!(
            equality.well_defined_proof.detailed_ref().left.obj().ir(),
            equality.fact.left.ir()
        );
        assert_eq!(
            equality.well_defined_proof.detailed_ref().right.obj().ir(),
            equality.fact.right.ir()
        );
        let EqualFactSearchedProof::ByMatchingOneArgByOne(proof) = &mut equality.searched_proof
        else {
            panic!("actual original constructor equality route")
        };
        assert_eq!(
            proof.corresponding_arg_equal_proofs.len(),
            if *name == "range" { 1 } else { 2 }
        );
        for (index, (child, (left, right))) in proof
            .corresponding_arg_equal_proofs
            .iter_mut()
            .zip(pairs)
            .enumerate()
        {
            let child = super::equality_proof_mut(child);
            assert_eq!(child.fact.left.ir(), left.ir());
            assert_eq!(child.fact.right.ir(), right.ir());
            assert_eq!(
                child.well_defined_proof.detailed_ref().left.obj().ir(),
                left.ir()
            );
            assert_eq!(
                child.well_defined_proof.detailed_ref().right.obj().ir(),
                right.ir()
            );
            if index == 0 {
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                ) = &child.searched_proof
                else {
                    panic!("original function equality citation")
                };
                assert_eq!(path.path.len(), 1);
                eprintln!(
                    "ORIGINAL43 {name} child{index}: {}={} path_fact={}",
                    left.display_string(),
                    right.display_string(),
                    path.path[0].2.value()
                );
            } else {
                assert!(matches!(
                    child.searched_proof,
                    EqualFactSearchedProof::ByTheyAreTheSame(_)
                ));
                eprintln!(
                    "ORIGINAL43 {name} child{index}: {}={} identity",
                    left.display_string(),
                    right.display_string()
                );
            }
        }
        let output = super::compile_run(&run, &compiler, name).unwrap();
        assert_eq!(output, super::compile_run(&run, &compiler, name).unwrap());
    }
}

#[test]
fn function_constructor_equality_all_actual_profiles_deterministically() {
    let mut errors = Vec::new();
    for (name, source) in SOURCES {
        eprintln!("PROFILE43 {name}");
        let (run, compiler) = super::execute(source);
        match super::compile_run(&run, &compiler, name) {
            Ok(output) => assert_eq!(output, super::compile_run(&run, &compiler, name).unwrap()),
            Err(error) => errors.push(format!("{name}: {error}")),
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

#[test]
fn function_constructor_equality_requires_exact_child_arity() {
    for name in ["range", "point", "set"] {
        for extra in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let (mut donor, _) = super::execute(source(name));
            let spare = children(&mut donor).pop().unwrap();
            if extra {
                children(&mut run).push(spare);
            } else {
                children(&mut run).pop();
            }
            reject(&run, &c, "child_arity");
        }
    }
}
#[test]
fn function_constructor_equality_preserves_function_target_order() {
    for name in ["point_both", "set_both"] {
        let (mut run, c) = super::execute(source(name));
        children(&mut run).swap(0, 1);
        reject(&run, &c, "child_order");
    }
}
#[test]
fn function_constructor_equality_preserves_each_child_subject() {
    for name in ["range", "point_both", "set_both"] {
        for index in 0..if name == "range" { 1 } else { 2 } {
            for right in [false, true] {
                let (mut run, c) = super::execute(source(name));
                let child = super::equality_proof_mut(&mut children(&mut run)[index]);
                if right {
                    child.fact.right = Obj::StandardSet(StandardSet::C)
                } else {
                    child.fact.left = Obj::StandardSet(StandardSet::C)
                };
                reject(&run, &c, "child_subject");
            }
        }
    }
}
#[test]
fn function_constructor_equality_preserves_original_child_wd() {
    for name in ["range", "point_both", "set_both"] {
        for index in 0..if name == "range" { 1 } else { 2 } {
            let (mut run, c) = super::execute(source(name));
            let wd = super::equality_proof_mut(&mut children(&mut run)[index])
                .well_defined_proof
                .as_detailed_mut()
                .unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
            reject(&run, &c, "child_wd");
        }
    }
}
#[test]
fn function_constructor_equality_preserves_both_parent_wd() {
    for name in ["range", "point", "set"] {
        let (mut run, c) = super::execute(source(name));
        let wd = last_equality(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject(&run, &c, "parent_wd");
    }
}
#[test]
fn function_constructor_equality_requires_constructor_wd_children() {
    for name in ["range", "point", "set"] {
        let (mut run, c) = super::execute(source(name));
        right_children(&mut run).clear();
        reject(&run, &c, "constructor_children");
    }
}
#[test]
fn function_constructor_equality_requires_original_range_interfaces() {
    for clear in [false, true] {
        let (mut run, c) = super::execute(source("range"));
        let FunctionWD::FnRange(p) = right_wd(&mut run) else {
            panic!()
        };
        assert!(!p.function_domains.is_empty());
        if clear {
            p.function_domains.clear()
        } else {
            p.function_domains[0].signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C))
        };
        reject(&run, &c, "range_interface");
    }
}
#[test]
fn function_constructor_equality_requires_preimage_signature_and_builder() {
    for name in ["point", "set"] {
        for signature in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let p = preimage_construction(&mut run);
            if signature {
                p.source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C))
            } else {
                p.builder.param_set = Box::new(Obj::StandardSet(StandardSet::C))
            };
            reject(&run, &c, "preimage_construction");
        }
    }
}
#[test]
fn function_constructor_equality_keeps_point_and_set_predicates_distinct() {
    for name in ["point", "set"] {
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
fn function_constructor_equality_requires_original_leaf_citation() {
    for name in ["range", "point_both", "set_both"] {
        for missing in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let future = last_equality(&mut run).fact.fact_id;
            path(&mut run, 0).path[0].2 = if missing {
                FactId::new(u64::MAX)
            } else {
                future
            };
            reject(&run, &c, "leaf_citation");
        }
    }
}
#[test]
fn function_constructor_equality_preserves_leaf_path_orientation() {
    let (mut run, c) = super::execute(source("range"));
    let edge = &mut path(&mut run, 0).path[0];
    std::mem::swap(&mut edge.0, &mut edge.1);
    reject(&run, &c, "leaf_orientation");
}
#[test]
fn function_constructor_equality_preserves_multi_edge_path_order() {
    for name in ["range_path", "point_path", "set_path"] {
        let (mut run, c) = super::execute(source(name));
        let path = path(&mut run, 0);
        assert_eq!(path.path.len(), 2);
        path.path.swap(0, 1);
        reject(&run, &c, "path_order");
    }
}
#[test]
fn function_constructor_equality_cannot_borrow_sibling_equality() {
    let private="forall eq43_private_f,eq43_private_g fn(eq43_private_x R) R:\n    eq43_private_f=eq43_private_g\n    =>:\n        eq43_private_f=eq43_private_g\n";
    let (mut run, c) = super::execute(&format!("{private}\n{}", source("range")));
    super::compile_run(&run, &c, "scope_baseline").unwrap();
    let first = super::forall_proof_mut(&mut run.statement_results[0]);
    let id = first.assumed_dom_facts[0]
        .store_and_infer
        .store
        .primary_fact_id();
    path(&mut run, 0).path[0].2 = id;
    reject(&run, &c, "sibling_equality");
}
#[test]
fn function_constructor_equality_requires_original_source_premise() {
    let (mut run, c) = super::execute(source("range"));
    super::forall_proof_mut(run.statement_results.last_mut().unwrap())
        .assumed_dom_facts
        .clear();
    reject(&run, &c, "source_premise");
}
#[test]
fn function_constructor_equality_preserves_returned_call_producer_order() {
    for name in ["range_returned", "point_returned", "set_returned"] {
        for future in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
            assert_eq!(p.proved_then_facts.len(), 4);
            if future {
                p.proved_then_facts.swap(2, 3)
            } else {
                p.proved_then_facts.remove(2);
            };
            reject(&run, &c, "returned_producer_order");
        }
    }
}
#[test]
fn function_constructor_equality_requires_original_target_equality_citation() {
    for name in ["point_both", "set_both"] {
        let (mut run, c) = super::execute(source(name));
        path(&mut run, 1).path[0].2 = FactId::new(u64::MAX);
        reject(&run, &c, "target_equality_citation");
    }
}
#[test]
fn function_constructor_equality_requires_set_target_sethood() {
    let (mut run, c) = super::execute(source("set"));
    let FunctionWD::PreimageSet(p) = right_wd(&mut run) else {
        panic!()
    };
    assert_eq!(p.requirement_fact_verified.len(), 1);
    p.requirement_fact_verified.clear();
    reject(&run, &c, "set_target_sethood");
}
#[test]
fn function_constructor_equality_preserves_original_wd_subject() {
    for name in ["range", "point", "set"] {
        let (mut run, c) = super::execute(source(name));
        let wd = &mut last_equality(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .right;
        match wd.as_detailed_mut().unwrap(){crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByDef{obj,..}|crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof::ByKnown{obj,..}=>*obj=Obj::StandardSet(StandardSet::C)};
        reject(&run, &c, "wd_subject");
    }
}
fn children(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut last_equality(run).searched_proof
    else {
        panic!("original constructor equality")
    };
    &mut p.corresponding_arg_equal_proofs
}
fn path(run: &mut RunLitexCodeResult, index: usize) -> &mut KnownEqualityPathProof {
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
    ) = &mut super::equality_proof_mut(&mut children(run)[index]).searched_proof
    else {
        panic!("original cited child path")
    };
    p
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

const SOURCES: &[(&str, &str)] = &[
    ("range", "# Equal function denotations preserve their image.\nforall replay43_f,replay43_g fn(replay43_x R) R:\n    replay43_f=replay43_g\n    =>:\n        fn_range(replay43_f)=fn_range(replay43_g)\n"),
    ("point", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall replay43_pf,replay43_pg fn(replay43_px R) R,replay43_y R:\n    replay43_pf=replay43_pg\n    =>:\n        preimage(replay43_pf,replay43_y)=preimage(replay43_pg,replay43_y)\n"),
    ("set", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall replay43_sf,replay43_sg fn(replay43_sx R) R,replay43_A set:\n    replay43_sf=replay43_sg\n    =>:\n        preimage_set(replay43_sf,replay43_A)=preimage_set(replay43_sg,replay43_A)\n"),
    ("range_guarded", "# Equal function denotations preserve their image.\nforall eq43_f,eq43_g fn(eq43_x R:eq43_x>0) R:\n    eq43_f=eq43_g\n    =>:\n        fn_range(eq43_f)=fn_range(eq43_g)\n"),
    ("range_grouped", "# Equal function denotations preserve their image.\nforall eq43_f,eq43_g fn(eq43_x,eq43_y R) R:\n    eq43_f=eq43_g\n    =>:\n        fn_range(eq43_f)=fn_range(eq43_g)\n"),
    ("range_complex", "# Equal function denotations preserve their image.\nforall eq43_f,eq43_g fn(eq43_x C) C:\n    eq43_f=eq43_g\n    =>:\n        fn_range(eq43_f)=fn_range(eq43_g)\n"),
    ("range_mixed", "# Equal function denotations preserve their image.\nforall eq43_f,eq43_g fn(eq43_x R,eq43_y C) C:\n    eq43_f=eq43_g\n    =>:\n        fn_range(eq43_f)=fn_range(eq43_g)\n"),
    ("range_path", "# Equal function denotations preserve their image.\nforall eq43_f,eq43_g,eq43_h fn(eq43_x R) R:\n    eq43_f=eq43_g\n    eq43_g=eq43_h\n    =>:\n        fn_range(eq43_h)=fn_range(eq43_f)\n"),
    ("range_composition", "# Equal function denotations preserve their image.\nforall eq43_f,eq43_g,eq43_h fn(eq43_x R) R:\n    eq43_f=eq43_g\n    =>:\n        compose(eq43_f,eq43_h)=compose(eq43_g,eq43_h)\n        fn_range(compose(eq43_f,eq43_h))=fn_range(compose(eq43_g,eq43_h))\n"),
    ("range_returned", "# Equal function denotations preserve their image.\nforall eq43_P,eq43_Q fn(eq43_t R) fn(eq43_x R) R:\n    eq43_P=eq43_Q\n    =>:\n        eq43_P(0) $in fn(eq43_u R) R\n        eq43_Q(0) $in fn(eq43_v R) R\n        eq43_P(0)=eq43_Q(0)\n        fn_range(eq43_P(0))=fn_range(eq43_Q(0))\n"),
    ("point_guarded", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f,eq43_g fn(eq43_x R:eq43_x>0) R,eq43_a R:\n    eq43_f=eq43_g\n    =>:\n        preimage(eq43_f,eq43_a)=preimage(eq43_g,eq43_a)\n"),
    ("point_grouped", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f,eq43_g fn(eq43_x,eq43_y R) R,eq43_a R:\n    eq43_f=eq43_g\n    =>:\n        preimage(eq43_f,eq43_a)=preimage(eq43_g,eq43_a)\n"),
    ("point_complex", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f,eq43_g fn(eq43_x C) C,eq43_a C:\n    eq43_f=eq43_g\n    =>:\n        preimage(eq43_f,eq43_a)=preimage(eq43_g,eq43_a)\n"),
    ("point_mixed", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f,eq43_g fn(eq43_x R,eq43_y C) C,eq43_a C:\n    eq43_f=eq43_g\n    =>:\n        preimage(eq43_f,eq43_a)=preimage(eq43_g,eq43_a)\n"),
    ("point_both", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f,eq43_g fn(eq43_x R) R,eq43_a,eq43_b R:\n    eq43_f=eq43_g\n    eq43_a=eq43_b\n    =>:\n        preimage(eq43_f,eq43_a)=preimage(eq43_g,eq43_b)\n"),
    ("point_target", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f fn(eq43_x R) R,eq43_a,eq43_b R:\n    eq43_a=eq43_b\n    =>:\n        preimage(eq43_f,eq43_a)=preimage(eq43_f,eq43_b)\n"),
    ("point_path", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f,eq43_g,eq43_h fn(eq43_x R) R,eq43_a R:\n    eq43_f=eq43_g\n    eq43_g=eq43_h\n    =>:\n        preimage(eq43_h,eq43_a)=preimage(eq43_f,eq43_a)\n"),
    ("point_composition", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_f,eq43_g,eq43_h fn(eq43_x R) R,eq43_a R:\n    eq43_f=eq43_g\n    =>:\n        compose(eq43_f,eq43_h)=compose(eq43_g,eq43_h)\n        preimage(compose(eq43_f,eq43_h),eq43_a)=preimage(compose(eq43_g,eq43_h),eq43_a)\n"),
    ("point_returned", "# Equal functions and the recorded point equalities preserve point inverse images.\nforall eq43_P,eq43_Q fn(eq43_t R) fn(eq43_x R) R,eq43_a R:\n    eq43_P=eq43_Q\n    =>:\n        eq43_P(0) $in fn(eq43_u R) R\n        eq43_Q(0) $in fn(eq43_v R) R\n        eq43_P(0)=eq43_Q(0)\n        preimage(eq43_P(0),eq43_a)=preimage(eq43_Q(0),eq43_a)\n"),
    ("set_guarded", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g fn(eq43_x R:eq43_x>0) R,eq43_a set:\n    eq43_f=eq43_g\n    =>:\n        preimage_set(eq43_f,eq43_a)=preimage_set(eq43_g,eq43_a)\n"),
    ("set_grouped", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g fn(eq43_x,eq43_y R) R,eq43_a set:\n    eq43_f=eq43_g\n    =>:\n        preimage_set(eq43_f,eq43_a)=preimage_set(eq43_g,eq43_a)\n"),
    ("set_complex", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g fn(eq43_x C) C,eq43_a set:\n    eq43_f=eq43_g\n    =>:\n        preimage_set(eq43_f,eq43_a)=preimage_set(eq43_g,eq43_a)\n"),
    ("set_mixed", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g fn(eq43_x R,eq43_y C) C,eq43_a set:\n    eq43_f=eq43_g\n    =>:\n        preimage_set(eq43_f,eq43_a)=preimage_set(eq43_g,eq43_a)\n"),
    ("set_both", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g fn(eq43_x R) R,eq43_a,eq43_b set:\n    eq43_f=eq43_g\n    eq43_a=eq43_b\n    =>:\n        preimage_set(eq43_f,eq43_a)=preimage_set(eq43_g,eq43_b)\n"),
    ("set_target", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f fn(eq43_x R) R,eq43_a,eq43_b set:\n    eq43_a=eq43_b\n    =>:\n        preimage_set(eq43_f,eq43_a)=preimage_set(eq43_f,eq43_b)\n"),
    ("set_path", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g,eq43_h fn(eq43_x R) R,eq43_a set:\n    eq43_f=eq43_g\n    eq43_g=eq43_h\n    =>:\n        preimage_set(eq43_h,eq43_a)=preimage_set(eq43_f,eq43_a)\n"),
    ("set_composition", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g,eq43_h fn(eq43_x R) R,eq43_a set:\n    eq43_f=eq43_g\n    =>:\n        compose(eq43_f,eq43_h)=compose(eq43_g,eq43_h)\n        preimage_set(compose(eq43_f,eq43_h),eq43_a)=preimage_set(compose(eq43_g,eq43_h),eq43_a)\n"),
    ("set_returned", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_P,eq43_Q fn(eq43_t R) fn(eq43_x R) R,eq43_a set:\n    eq43_P=eq43_Q\n    =>:\n        eq43_P(0) $in fn(eq43_u R) R\n        eq43_Q(0) $in fn(eq43_v R) R\n        eq43_P(0)=eq43_Q(0)\n        preimage_set(eq43_P(0),eq43_a)=preimage_set(eq43_Q(0),eq43_a)\n"),
    ("set_empty", "# Equal functions and the recorded target-set equalities preserve set inverse images.\nforall eq43_f,eq43_g fn(eq43_x R) R:\n    eq43_f=eq43_g\n    =>:\n        preimage_set(eq43_f,{})=preimage_set(eq43_g,{})\n"),
];
