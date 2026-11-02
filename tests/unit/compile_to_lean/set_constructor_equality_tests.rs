use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    DetailedObjWellDefinedProof, ObjWellDefinedProofByDef, SetOperatorObjWellDefinedProofByDef,
};
use crate::prelude::*;

#[test]
fn set_constructor_equality_original_seven_ordered_trees() {
    for (name, source) in &SOURCES[..7] {
        let (mut run, compiler) = super::execute(source);
        let theorem = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
        assert_eq!(theorem.proved_then_facts.len(), 1);
        let equality = super::equality_proof_mut(&mut theorem.proved_then_facts[0].verify_result);
        let pairs=crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs(&equality.fact.left,&equality.fact.right).unwrap();
        assert_eq!(
            equality.well_defined_proof.detailed_ref().left.obj().ir(),
            equality.fact.left.ir()
        );
        assert_eq!(
            equality.well_defined_proof.detailed_ref().right.obj().ir(),
            equality.fact.right.ir()
        );
        if *name == "family_intersection" {
            for wd in [
                &equality.well_defined_proof.detailed_ref().left,
                &equality.well_defined_proof.detailed_ref().right,
            ] {
                let DetailedObjWellDefinedProof::ByDef {
                    obj: Obj::SetOperator(SetOperator::FamilyIntersect(value)),
                    proof:
                        ObjWellDefinedProofByDef::SetOperator(
                            SetOperatorObjWellDefinedProofByDef::FamilyIntersect(p),
                        ),
                } = wd.detailed_ref()
                else {
                    panic!("original family intersection formation")
                };
                assert_eq!(p.child_obj_well_defined.len(), 1);
                assert_eq!(p.child_obj_well_defined[0].obj().ir(), value.left.ir());
                assert_eq!(p.requirement_fact_verified.len(), 1);
                assert!(
                    matches!(source_subject(&p.requirement_fact_verified[0]).unwrap(),Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir()==value.left.ir())
                );
                eprintln!(
                    "ORIGINAL44 nonempty:{}",
                    source_subject(&p.requirement_fact_verified[0])
                        .unwrap()
                        .display_string()
                );
            }
        }
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equality.searched_proof else {
            panic!("actual original constructor equality route")
        };
        assert_eq!(
            p.corresponding_arg_equal_proofs.len(),
            if matches!(
                *name,
                "union" | "intersection" | "difference" | "symmetric_difference"
            ) {
                2
            } else {
                1
            }
        );
        for (index, (child, (left, right))) in p
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
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &child.searched_proof
            else {
                panic!("original equality citation")
            };
            assert_eq!(path.path.len(), 1);
            eprintln!(
                "ORIGINAL44 {name} child{index}:{}={} fact={}",
                left.display_string(),
                right.display_string(),
                path.path[0].2.value()
            );
        }
        let output = super::compile_run(&run, &compiler, name).unwrap();
        assert_eq!(output, super::compile_run(&run, &compiler, name).unwrap());
    }
}

#[test]
fn set_constructor_equality_all_actual_profiles_deterministically() {
    let mut errors = Vec::new();
    for (name, source) in SOURCES {
        eprintln!("PROFILE44 {name}");
        let (run, c) = super::execute(source);
        match super::compile_run(&run, &c, name) {
            Ok(output) => assert_eq!(output, super::compile_run(&run, &c, name).unwrap()),
            Err(error) => errors.push(format!("{name}: {error}")),
        };
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

#[test]
fn set_constructor_equality_original_powerset_nonempty_requirement() {
    let (mut run, _) = super::execute(source("family_intersection_nested"));
    let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let e = super::equality_proof_mut(&mut p.proved_then_facts.last_mut().unwrap().verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::FamilyIntersect(
                p,
            )),
        ..
    } = e
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .right
        .as_detailed_mut()
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(p.requirement_fact_verified.len(), 1);
    let n = super::atomic_proof_mut(&mut p.requirement_fact_verified[0]);
    assert!(
        matches!(&n.fact,AtomicFact::IsNonemptySetFact(f) if matches!(&f.set,Obj::SetOperator(SetOperator::PowerSet(_))))
    );
    assert!(matches!(n.searched_proof,AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_nonempty_set::IsNonemptySetFactSearchProofByBuiltinRule::PowerSetNonempty(_)))));
    eprintln!("ORIGINAL44 nested requirement:PowerSetNonempty,zero payload");
}
fn source(name: &str) -> &'static str {
    SOURCES.iter().find(|(n, _)| *n == name).unwrap().1
}

#[test]
fn set_constructor_equality_requires_exact_child_arity() {
    for name in BASE {
        for extra in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let (mut donor, _) = super::execute(source(name));
            let spare = children(&mut donor).pop().unwrap();
            if extra {
                children(&mut run).push(spare)
            } else {
                children(&mut run).pop();
            };
            reject(&run, &c, "child_arity");
        }
    }
}
#[test]
fn set_constructor_equality_preserves_binary_operand_order() {
    for name in BINARY {
        let (mut run, c) = super::execute(source(name));
        children(&mut run).swap(0, 1);
        reject(&run, &c, "operand_order");
    }
}
#[test]
fn set_constructor_equality_preserves_each_child_subject() {
    for name in BASE {
        for index in 0..if BINARY.contains(name) { 2 } else { 1 } {
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
fn set_constructor_equality_preserves_original_child_wd() {
    for name in BASE {
        for index in 0..if BINARY.contains(name) { 2 } else { 1 } {
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
fn set_constructor_equality_preserves_both_parent_wd() {
    for name in BASE {
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
fn set_constructor_equality_requires_original_wd_children() {
    for name in BASE {
        for right in [false, true] {
            let (mut run, c) = super::execute(source(name));
            wd_children(&mut run, right).clear();
            reject(&run, &c, "wd_children");
        }
    }
}
#[test]
fn set_constructor_equality_preserves_wd_child_order() {
    for name in BINARY {
        let (mut run, c) = super::execute(source(name));
        wd_children(&mut run, true).swap(0, 1);
        reject(&run, &c, "wd_child_order");
    }
}
#[test]
fn set_constructor_equality_preserves_original_parent_wd_subject() {
    for name in BASE {
        for right in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let wd = last_equality(&mut run)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap();
            let wd = if right { &mut wd.right } else { &mut wd.left };
            match wd.as_detailed_mut().unwrap() {
                DetailedObjWellDefinedProof::ByKnown { obj, .. }
                | DetailedObjWellDefinedProof::ByDef { obj, .. } => {
                    *obj = Obj::StandardSet(StandardSet::C)
                }
            };
            reject(&run, &c, "parent_subject");
        }
    }
}
#[test]
fn set_constructor_equality_requires_both_original_nonempty_requirements() {
    for right in [false, true] {
        for extra in [false, true] {
            let (mut run, c) = super::execute(source("family_intersection"));
            let (mut donor, _) = super::execute(source("family_intersection"));
            let spare = requirements(&mut donor, right).pop().unwrap();
            if extra {
                requirements(&mut run, right).push(spare)
            } else {
                requirements(&mut run, right).clear()
            };
            reject(&run, &c, "nonempty_arity");
        }
    }
}
#[test]
fn set_constructor_equality_preserves_nonempty_requirement_subject() {
    for right in [false, true] {
        let (mut run, c) = super::execute(source("family_intersection"));
        let AtomicFact::IsNonemptySetFact(f) =
            &mut super::atomic_proof_mut(&mut requirements(&mut run, right)[0]).fact
        else {
            panic!()
        };
        f.set = Obj::StandardSet(StandardSet::C);
        reject(&run, &c, "nonempty_subject");
    }
}
#[test]
fn set_constructor_equality_requires_original_nonempty_citation() {
    for right in [false, true] {
        let (mut run, c) = super::execute(source("family_intersection"));
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
            &mut super::atomic_proof_mut(&mut requirements(&mut run, right)[0]).searched_proof
        else {
            panic!("original nonempty source citation")
        };
        p.cite_fact_id = FactId::new(u64::MAX);
        reject(&run, &c, "nonempty_citation");
    }
}
#[test]
fn set_constructor_equality_requires_original_leaf_citation() {
    for name in BASE {
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
fn set_constructor_equality_preserves_leaf_path_orientation() {
    for name in BASE {
        let (mut run, c) = super::execute(source(name));
        let edge = &mut path(&mut run, 0).path[0];
        std::mem::swap(&mut edge.0, &mut edge.1);
        reject(&run, &c, "leaf_orientation");
    }
}
#[test]
fn set_constructor_equality_preserves_multi_edge_path_order() {
    for name in BASE {
        let (mut run, c) = super::execute(source(&format!("{name}_path")));
        let p = path(&mut run, 0);
        assert_eq!(p.path.len(), 2);
        p.path.swap(0, 1);
        reject(&run, &c, "path_order");
    }
}
#[test]
fn set_constructor_equality_cannot_borrow_sibling_equality() {
    let private="forall sc44_private_A,sc44_private_B set:\n    sc44_private_A=sc44_private_B\n    =>:\n        sc44_private_A=sc44_private_B\n";
    let (mut run, c) = super::execute(&format!("{private}\n{}", source("union")));
    super::compile_run(&run, &c, "scope_baseline").unwrap();
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let id = p.assumed_dom_facts[0]
        .store_and_infer
        .store
        .primary_fact_id();
    path(&mut run, 0).path[0].2 = id;
    reject(&run, &c, "sibling_equality");
}
#[test]
fn set_constructor_equality_preserves_returned_call_producer_order() {
    for name in BASE {
        for future in [false, true] {
            let (mut run, c) = super::execute(source(&format!("{name}_returned")));
            let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
            let last = p.proved_then_facts.len() - 1;
            if future {
                p.proved_then_facts.swap(0, last)
            } else {
                p.proved_then_facts.remove(0);
            };
            reject(&run, &c, "returned_producer");
        }
    }
}
#[test]
fn set_constructor_equality_preserves_nested_producer_order() {
    for name in BASE {
        for future in [false, true] {
            let (mut run, c) = super::execute(source(&format!("{name}_nested")));
            let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
            assert_eq!(p.proved_then_facts.len(), 2);
            if future {
                p.proved_then_facts.swap(0, 1)
            } else {
                p.proved_then_facts.remove(0);
            };
            reject(&run, &c, "nested_producer");
        }
    }
}
#[test]
fn set_constructor_equality_requires_original_source_premises() {
    for name in BASE {
        let (mut run, c) = super::execute(source(name));
        super::forall_proof_mut(run.statement_results.last_mut().unwrap())
            .assumed_dom_facts
            .clear();
        reject(&run, &c, "source_premises");
    }
}
#[test]
fn set_constructor_equality_preserves_each_binary_equality_citation() {
    for name in BINARY {
        let (mut run, c) = super::execute(source(name));
        let first = path(&mut run, 0).path[0].2;
        let second = path(&mut run, 1).path[0].2;
        assert_ne!(first, second);
        path(&mut run, 0).path[0].2 = second;
        path(&mut run, 1).path[0].2 = first;
        reject(&run, &c, "binary_citation_order");
    }
}
#[test]
fn set_constructor_equality_nonempty_forall_original_tree() {
    let (mut run, c) = super::execute(source("nonempty_forall"));
    let p = nonempty_known(&mut run).detailed_ref();
    let r = p.instantiation_requirements.detailed_ref();
    assert_eq!(p.arg_match_proofs.len(), 1);
    assert_eq!(r.param_type_requirements.len(), 1);
    assert!(r.dom_facts.is_empty());
    assert!(r.proof_of_dom_facts.is_empty());
    assert!(matches!(
        r.param_type_requirements[0].type_fact,
        Fact::AtomicFact(AtomicFact::InFact(_))
    ));
    super::compile_run(&run, &c, "nonempty_original").unwrap();
}
#[test]
fn set_constructor_equality_nonempty_forall_requires_original_citation() {
    for missing in [false, true] {
        let (mut run, c) = super::execute(source("nonempty_forall"));
        let future = last_atomic(&mut run).fact.fact_id();
        nonempty_known(&mut run)
            .as_detailed_mut()
            .unwrap()
            .cite
            .fact_id = if missing {
            FactId::new(u64::MAX)
        } else {
            future
        };
        reject(&run, &c, "nonempty_forall_citation");
    }
}
#[test]
fn set_constructor_equality_nonempty_forall_requires_original_requirements() {
    let (mut run, c) = super::execute(source("nonempty_forall"));
    nonempty_known(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap()
        .param_type_requirements
        .clear();
    reject(&run, &c, "nonempty_forall_requirements");
}
#[test]
fn set_constructor_equality_nonempty_forall_preserves_requirement_subject() {
    let (mut run, c) = super::execute(source("nonempty_forall"));
    let p = &mut nonempty_known(&mut run)
        .as_detailed_mut()
        .unwrap()
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap()
        .param_type_requirements[0];
    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.type_fact else {
        panic!()
    };
    f.element = Obj::StandardSet(StandardSet::C);
    reject(&run, &c, "nonempty_forall_type_subject");
}
#[test]
fn set_constructor_equality_nonempty_forall_preserves_argument_binding() {
    let (mut run, c) = super::execute(source("nonempty_forall"));
    let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof::BoundParam{param_id,..}=nonempty_known(&mut run).as_detailed_mut().unwrap().arg_match_proofs[0].as_detailed_mut().unwrap() else{panic!()};
    *param_id = IdentifierId::new(u64::MAX);
    reject(&run, &c, "nonempty_forall_binding");
}
#[test]
fn set_constructor_equality_nonempty_forall_cannot_borrow_sibling_universal() {
    let private="forall sc44_private_N set:\n    forall sc44_private_X sc44_private_N:\n        $is_nonempty_set(sc44_private_X)\n    =>:\n        sc44_private_N=sc44_private_N\n";
    let (mut run, c) = super::execute(&format!("{private}\n{}", source("nonempty_forall")));
    super::compile_run(&run, &c, "nonempty_scope_baseline").unwrap();
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let id = p.assumed_dom_facts[0]
        .store_and_infer
        .store
        .primary_fact_id();
    nonempty_known(&mut run)
        .as_detailed_mut()
        .unwrap()
        .cite
        .fact_id = id;
    reject(&run, &c, "nonempty_sibling_universal");
}
#[test]
fn set_constructor_equality_nonempty_forall_preserves_goal_wd() {
    let (mut run, c) = super::execute(source("nonempty_forall"));
    let p = &mut last_atomic(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0];
    match p.as_detailed_mut().unwrap() {
        DetailedObjWellDefinedProof::ByKnown { obj, .. }
        | DetailedObjWellDefinedProof::ByDef { obj, .. } => *obj = Obj::StandardSet(StandardSet::C),
    };
    reject(&run, &c, "nonempty_goal_wd");
}
#[test]
fn set_constructor_equality_powerset_nonempty_rejects_retagged_rule() {
    let (mut run, c) = super::execute("$is_nonempty_set(R)\n");
    last_atomic(&mut run).searched_proof=AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_nonempty_set::IsNonemptySetFactSearchProofByBuiltinRule::PowerSetNonempty(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_nonempty_set::PowerSetNonemptyBuiltinRuleProof{})));
    reject(&run, &c, "retagged_power_nonempty");
}
fn last_verify(run: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    fn last(v: &mut VerifyFactResult) -> &mut VerifyFactResult {
        if let VerifyFactResult::ForallFact(p) = v {
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!()
            };
            last(&mut p.proved_then_facts.last_mut().unwrap().verify_result)
        } else {
            v
        }
    }
    last(&mut s.verify_result)
}
fn last_equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    super::equality_proof_mut(last_verify(run))
}
fn last_atomic(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    super::atomic_proof_mut(last_verify(run))
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
fn parent_wd(
    run: &mut RunLitexCodeResult,
    right: bool,
) -> &mut SetOperatorObjWellDefinedProofByDef {
    let wd = last_equality(run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    let wd = if right { &mut wd.right } else { &mut wd.left };
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetOperator(p),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("original set constructor WD")
    };
    p
}
fn wd_children(
    run: &mut RunLitexCodeResult,
    right: bool,
) -> &mut Vec<
    Box<crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProof>,
> {
    match parent_wd(run, right) {
        SetOperatorObjWellDefinedProofByDef::Union(p) => &mut p.child_obj_well_defined,
        SetOperatorObjWellDefinedProofByDef::Intersect(p) => &mut p.child_obj_well_defined,
        SetOperatorObjWellDefinedProofByDef::SetMinus(p) => &mut p.child_obj_well_defined,
        SetOperatorObjWellDefinedProofByDef::SymmetricDifference(p) => {
            &mut p.child_obj_well_defined
        }
        SetOperatorObjWellDefinedProofByDef::PowerSet(p) => &mut p.child_obj_well_defined,
        SetOperatorObjWellDefinedProofByDef::FamilyUnion(p) => &mut p.child_obj_well_defined,
        SetOperatorObjWellDefinedProofByDef::FamilyIntersect(p) => &mut p.child_obj_well_defined,
        _ => panic!(),
    }
}
fn requirements(run: &mut RunLitexCodeResult, right: bool) -> &mut Vec<VerifyFactResult> {
    let SetOperatorObjWellDefinedProofByDef::FamilyIntersect(p) = parent_wd(run, right) else {
        panic!()
    };
    &mut p.requirement_fact_verified
}
fn nonempty_known(run:&mut RunLitexCodeResult)->&mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact{
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) =
        &mut last_atomic(run).searched_proof
    else {
        panic!("original nonempty universal application")
    };
    p
}
fn reject(run: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, name: &str) {
    assert!(
        super::compile_run(run, c, name).is_err(),
        "altered original evidence accepted:{name}"
    );
}
const BASE: &[&str] = &[
    "union",
    "intersection",
    "difference",
    "symmetric_difference",
    "power",
    "family_union",
    "family_intersection",
];
const BINARY: &[&str] = &[
    "union",
    "intersection",
    "difference",
    "symmetric_difference",
];
const SOURCES:&[(&str,&str)]=&[
("union","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall eq44_A,eq44_B,eq44_C,eq44_D set:\n    eq44_A=eq44_B\n    eq44_C=eq44_D\n    =>:\n        union(eq44_A,eq44_C)=union(eq44_B,eq44_D)\n"),
("intersection","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall eq44_A,eq44_B,eq44_C,eq44_D set:\n    eq44_A=eq44_B\n    eq44_C=eq44_D\n    =>:\n        intersect(eq44_A,eq44_C)=intersect(eq44_B,eq44_D)\n"),
("difference","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall eq44_A,eq44_B,eq44_C,eq44_D set:\n    eq44_A=eq44_B\n    eq44_C=eq44_D\n    =>:\n        set_minus(eq44_A,eq44_C)=set_minus(eq44_B,eq44_D)\n"),
("symmetric_difference","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall eq44_A,eq44_B,eq44_C,eq44_D set:\n    eq44_A=eq44_B\n    eq44_C=eq44_D\n    =>:\n        set_diff(eq44_A,eq44_C)=set_diff(eq44_B,eq44_D)\n"),
("power","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall eq44_A,eq44_B set:\n    eq44_A=eq44_B\n    =>:\n        power_set(eq44_A)=power_set(eq44_B)\n"),
("family_union","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall eq44_A,eq44_B set:\n    eq44_A=eq44_B\n    =>:\n        family_union(eq44_A)=family_union(eq44_B)\n"),
("family_intersection","# Equal operands preserve a nonempty-family intersection;its original nonemptiness evidence remains required.\nforall eq44_A,eq44_B nonempty_set:\n    eq44_A=eq44_B\n    =>:\n        family_intersect(eq44_A)=family_intersect(eq44_B)\n"),
("union_path","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set,sc44_E set:\n    sc44_A=sc44_B\n    sc44_B=sc44_C\n    =>:\n        union(sc44_C,sc44_E)=union(sc44_A,sc44_E)\n"),
("union_left","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        union(sc44_A,sc44_C)=union(sc44_B,sc44_C)\n"),
("union_right","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        union(sc44_C,sc44_A)=union(sc44_C,sc44_B)\n"),
("union_repeated","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B set:\n    sc44_A=sc44_B\n    =>:\n        union(sc44_A,sc44_A)=union(sc44_B,sc44_B)\n"),
("union_nested","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C,sc44_D,sc44_E set:\n    sc44_A=sc44_B\n    sc44_C=sc44_D\n    =>:\n        union(sc44_A,sc44_C)=union(sc44_B,sc44_D)\n        union(union(sc44_A,sc44_C),sc44_E)=union(union(sc44_B,sc44_D),sc44_E)\n"),
("union_functions","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_f,sc44_g fn(sc44_x R) R,sc44_E set:\n    sc44_f=sc44_g\n    =>:\n        union(sc44_f,sc44_E)=union(sc44_g,sc44_E)\n"),
("union_returned","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_P,sc44_Q fn(sc44_t R) power_set(R),sc44_E set:\n    sc44_P=sc44_Q\n    =>:\n        sc44_P(0)=sc44_Q(0)\n        union(sc44_P(0),sc44_E)=union(sc44_Q(0),sc44_E)\n"),
("intersection_path","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set,sc44_E set:\n    sc44_A=sc44_B\n    sc44_B=sc44_C\n    =>:\n        intersect(sc44_C,sc44_E)=intersect(sc44_A,sc44_E)\n"),
("intersection_left","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        intersect(sc44_A,sc44_C)=intersect(sc44_B,sc44_C)\n"),
("intersection_right","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        intersect(sc44_C,sc44_A)=intersect(sc44_C,sc44_B)\n"),
("intersection_repeated","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B set:\n    sc44_A=sc44_B\n    =>:\n        intersect(sc44_A,sc44_A)=intersect(sc44_B,sc44_B)\n"),
("intersection_nested","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C,sc44_D,sc44_E set:\n    sc44_A=sc44_B\n    sc44_C=sc44_D\n    =>:\n        intersect(sc44_A,sc44_C)=intersect(sc44_B,sc44_D)\n        intersect(intersect(sc44_A,sc44_C),sc44_E)=intersect(intersect(sc44_B,sc44_D),sc44_E)\n"),
("intersection_functions","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_f,sc44_g fn(sc44_x R) R,sc44_E set:\n    sc44_f=sc44_g\n    =>:\n        intersect(sc44_f,sc44_E)=intersect(sc44_g,sc44_E)\n"),
("intersection_returned","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_P,sc44_Q fn(sc44_t R) power_set(R),sc44_E set:\n    sc44_P=sc44_Q\n    =>:\n        sc44_P(0)=sc44_Q(0)\n        intersect(sc44_P(0),sc44_E)=intersect(sc44_Q(0),sc44_E)\n"),
("difference_path","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set,sc44_E set:\n    sc44_A=sc44_B\n    sc44_B=sc44_C\n    =>:\n        set_minus(sc44_C,sc44_E)=set_minus(sc44_A,sc44_E)\n"),
("difference_left","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        set_minus(sc44_A,sc44_C)=set_minus(sc44_B,sc44_C)\n"),
("difference_right","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        set_minus(sc44_C,sc44_A)=set_minus(sc44_C,sc44_B)\n"),
("difference_repeated","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B set:\n    sc44_A=sc44_B\n    =>:\n        set_minus(sc44_A,sc44_A)=set_minus(sc44_B,sc44_B)\n"),
("difference_nested","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C,sc44_D,sc44_E set:\n    sc44_A=sc44_B\n    sc44_C=sc44_D\n    =>:\n        set_minus(sc44_A,sc44_C)=set_minus(sc44_B,sc44_D)\n        set_minus(set_minus(sc44_A,sc44_C),sc44_E)=set_minus(set_minus(sc44_B,sc44_D),sc44_E)\n"),
("difference_functions","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_f,sc44_g fn(sc44_x R) R,sc44_E set:\n    sc44_f=sc44_g\n    =>:\n        set_minus(sc44_f,sc44_E)=set_minus(sc44_g,sc44_E)\n"),
("difference_returned","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_P,sc44_Q fn(sc44_t R) power_set(R),sc44_E set:\n    sc44_P=sc44_Q\n    =>:\n        sc44_P(0)=sc44_Q(0)\n        set_minus(sc44_P(0),sc44_E)=set_minus(sc44_Q(0),sc44_E)\n"),
("symmetric_difference_path","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set,sc44_E set:\n    sc44_A=sc44_B\n    sc44_B=sc44_C\n    =>:\n        set_diff(sc44_C,sc44_E)=set_diff(sc44_A,sc44_E)\n"),
("symmetric_difference_left","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        set_diff(sc44_A,sc44_C)=set_diff(sc44_B,sc44_C)\n"),
("symmetric_difference_right","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    =>:\n        set_diff(sc44_C,sc44_A)=set_diff(sc44_C,sc44_B)\n"),
("symmetric_difference_repeated","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B set:\n    sc44_A=sc44_B\n    =>:\n        set_diff(sc44_A,sc44_A)=set_diff(sc44_B,sc44_B)\n"),
("symmetric_difference_nested","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C,sc44_D,sc44_E set:\n    sc44_A=sc44_B\n    sc44_C=sc44_D\n    =>:\n        set_diff(sc44_A,sc44_C)=set_diff(sc44_B,sc44_D)\n        set_diff(set_diff(sc44_A,sc44_C),sc44_E)=set_diff(set_diff(sc44_B,sc44_D),sc44_E)\n"),
("symmetric_difference_functions","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_f,sc44_g fn(sc44_x R) R,sc44_E set:\n    sc44_f=sc44_g\n    =>:\n        set_diff(sc44_f,sc44_E)=set_diff(sc44_g,sc44_E)\n"),
("symmetric_difference_returned","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_P,sc44_Q fn(sc44_t R) power_set(R),sc44_E set:\n    sc44_P=sc44_Q\n    =>:\n        sc44_P(0)=sc44_Q(0)\n        set_diff(sc44_P(0),sc44_E)=set_diff(sc44_Q(0),sc44_E)\n"),
("power_path","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    sc44_B=sc44_C\n    =>:\n        power_set(sc44_C)=power_set(sc44_A)\n"),
("power_nested","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B set:\n    sc44_A=sc44_B\n    =>:\n        power_set(sc44_A)=power_set(sc44_B)\n        power_set(power_set(sc44_A))=power_set(power_set(sc44_B))\n"),
("power_functions","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_f,sc44_g fn(sc44_x R) R:\n    sc44_f=sc44_g\n    =>:\n        power_set(sc44_f)=power_set(sc44_g)\n"),
("power_returned","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_P,sc44_Q fn(sc44_t R) power_set(R):\n    sc44_P=sc44_Q\n    =>:\n        sc44_P(0)=sc44_Q(0)\n        power_set(sc44_P(0))=power_set(sc44_Q(0))\n"),
("family_union_path","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B,sc44_C set:\n    sc44_A=sc44_B\n    sc44_B=sc44_C\n    =>:\n        family_union(sc44_C)=family_union(sc44_A)\n"),
("family_union_nested","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_A,sc44_B set:\n    sc44_A=sc44_B\n    =>:\n        power_set(sc44_A)=power_set(sc44_B)\n        family_union(power_set(sc44_A))=family_union(power_set(sc44_B))\n"),
("family_union_functions","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_f,sc44_g fn(sc44_x R) R:\n    sc44_f=sc44_g\n    =>:\n        family_union(sc44_f)=family_union(sc44_g)\n"),
("family_union_returned","# Equal set denotations preserve this set construction,using the recorded operand equalities.\nforall sc44_P,sc44_Q fn(sc44_t R) power_set(R):\n    sc44_P=sc44_Q\n    =>:\n        sc44_P(0)=sc44_Q(0)\n        family_union(sc44_P(0))=family_union(sc44_Q(0))\n"),
("family_intersection_path","# Equal operands preserve a nonempty-family intersection;its original nonemptiness evidence remains required.\nforall sc44_A,sc44_B,sc44_C nonempty_set:\n    sc44_A=sc44_B\n    sc44_B=sc44_C\n    =>:\n        family_intersect(sc44_C)=family_intersect(sc44_A)\n"),
("family_intersection_nested","# Equal operands preserve a nonempty-family intersection;its original nonemptiness evidence remains required.\nforall sc44_A,sc44_B set:\n    sc44_A=sc44_B\n    =>:\n        power_set(sc44_A)=power_set(sc44_B)\n        family_intersect(power_set(sc44_A))=family_intersect(power_set(sc44_B))\n"),
("family_intersection_functions","# Equal operands preserve a nonempty-family intersection;its original nonemptiness evidence remains required.\nforall sc44_f,sc44_g fn(sc44_x R) R:\n    sc44_f=sc44_g\n    =>:\n        family_intersect(sc44_f)=family_intersect(sc44_g)\n"),
("family_intersection_returned","# Equal operands preserve a nonempty-family intersection;its original nonemptiness evidence remains required.\nforall sc44_N set,sc44_P,sc44_Q fn(sc44_t R) sc44_N:\n    forall sc44_X sc44_N:\n        $is_nonempty_set(sc44_X)\n    sc44_P=sc44_Q\n    =>:\n        sc44_P(0)=sc44_Q(0)\n        $is_nonempty_set(sc44_P(0))\n        $is_nonempty_set(sc44_Q(0))\n        family_intersect(sc44_P(0))=family_intersect(sc44_Q(0))\n"),
("nonempty_forall","# A recorded universal nonemptiness fact applies to each member of its carrier.\nforall replay44_N set,replay44_y replay44_N:\n    forall replay44_x replay44_N:\n        $is_nonempty_set(replay44_x)\n    =>:\n        $is_nonempty_set(replay44_y)\n"),
("powerset_nonempty","# Every power set contains the empty set,including the power set of the empty set.\nforall replay44_S set:\n    $is_nonempty_set(power_set(replay44_S))\n$is_nonempty_set(power_set({}))\n"),
];
