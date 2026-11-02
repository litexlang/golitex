use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    DetailedObjWellDefinedProof, ObjWellDefinedProof, ObjWellDefinedProofByDef,
    SetFormerObjWellDefinedProofByDef,
};
use crate::prelude::*;
#[test]
fn interval_constructor_equality_original_ten_ordered_trees() {
    for (name, source) in SOURCES {
        let (mut run, c) = super::execute(source);
        let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
        let eq =
            super::equality_proof_mut(&mut p.proved_then_facts.last_mut().unwrap().verify_result);
        let pairs=crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs(&eq.fact.left,&eq.fact.right).unwrap();
        let n = if name.starts_with("lower_") || name.starts_with("upper_") {
            1
        } else {
            2
        };
        assert_eq!(pairs.len(), n);
        for (right, wd) in [
            (false, &eq.well_defined_proof.detailed_ref().left),
            (true, &eq.well_defined_proof.detailed_ref().right),
        ] {
            assert_eq!(
                wd.obj().ir(),
                if right {
                    eq.fact.right.ir()
                } else {
                    eq.fact.left.ir()
                }
            );
            let (children, req) = stages(wd);
            assert_eq!(children.len(), n);
            assert_eq!(req.len(), n);
            eprintln!(
                "ORIGINAL46 {name} parent:{} children:{} requirements:{}",
                wd.obj().display_string(),
                children.len(),
                req.len()
            );
            for (i, ((left, right_obj), wd)) in pairs.iter().zip(children).enumerate() {
                let endpoint = if right { right_obj } else { left };
                assert_eq!(wd.obj().ir(), endpoint.ir());
                let f = source_subject(&req[i]).unwrap();
                assert!(
                    matches!(&f,Fact::AtomicFact(AtomicFact::InFact(p))if p.element.ir()==endpoint.ir()&&p.set==Obj::StandardSet(if matches!(*name,"range"|"closed_range"){StandardSet::Z}else{StandardSet::R}))
                );
                eprintln!("WD requirement{i}:{}", f.display_string());
            }
        }
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut eq.searched_proof else {
            panic!("original selected route")
        };
        assert_eq!(p.corresponding_arg_equal_proofs.len(), n);
        for (index, (child, (left, right))) in p
            .corresponding_arg_equal_proofs
            .iter_mut()
            .zip(pairs)
            .enumerate()
        {
            assert!(
                matches!(source_subject(child).unwrap(),Fact::AtomicFact(AtomicFact::EqualFact(eq))if eq.left.ir()==left.ir()&&eq.right.ir()==right.ir())
            );
            let child = super::equality_proof_mut(child);
            assert_eq!(
                child.well_defined_proof.detailed_ref().left.obj().ir(),
                left.ir()
            );
            assert_eq!(
                child.well_defined_proof.detailed_ref().right.obj().ir(),
                right.ir()
            );
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
            ) = &child.searched_proof
            else {
                panic!("original endpoint citation")
            };
            assert_eq!(p.path.len(), 1);
            eprintln!(
                "ORIGINAL46 {name} child{index}:{}={} cite:{}",
                left.display_string(),
                right.display_string(),
                p.path[0].2.value()
            );
        }
        super::compile_run(&run, &c, name).unwrap();
    }
}
fn stages(wd: &ObjWellDefinedProof) -> (&Vec<Box<ObjWellDefinedProof>>, &Vec<VerifyFactResult>) {
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetFormer(p),
        ..
    } = wd.detailed_ref()
    else {
        panic!("original set formation")
    };
    match p {
        SetFormerObjWellDefinedProofByDef::Range(p) => {
            (&p.child_obj_well_defined, &p.requirement_fact_verified)
        }
        SetFormerObjWellDefinedProofByDef::ClosedRange(p) => {
            (&p.child_obj_well_defined, &p.requirement_fact_verified)
        }
        SetFormerObjWellDefinedProofByDef::IntervalObj(p) => {
            (&p.child_obj_well_defined, &p.requirement_fact_verified)
        }
        SetFormerObjWellDefinedProofByDef::OneSideInfinityIntervalObj(p) => {
            (&p.child_obj_well_defined, &p.requirement_fact_verified)
        }
        _ => panic!(),
    }
}

#[test]
fn interval_constructor_equality_all_actual_profiles() {
    for (name, source) in PROFILES {
        let (run, c) = super::execute(source);
        super::compile_run(&run, &c, name).unwrap();
    }
}
#[test]
fn interval_constructor_equality_requires_exact_child_arity() {
    for name in BASE {
        for extra in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let (mut donor, _) = super::execute(source(name));
            let spare = children(&mut donor).pop().unwrap();
            if extra {
                children(&mut r).push(spare)
            } else {
                children(&mut r).pop();
            };
            reject(&r, &c, "arity");
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_operand_order() {
    for name in MULTI {
        let (mut r, c) = super::execute(source(name));
        children(&mut r).swap(0, 1);
        reject(&r, &c, "order");
    }
}
#[test]
fn interval_constructor_equality_preserves_each_child_subject() {
    for name in BASE {
        let (mut r, _) = super::execute(source(name));
        let n = children(&mut r).len();
        for index in 0..n {
            for right in [false, true] {
                let (mut r, c) = super::execute(source(name));
                let eq = super::equality_proof_mut(&mut children(&mut r)[index]);
                if right {
                    eq.fact.right = Obj::StandardSet(StandardSet::C)
                } else {
                    eq.fact.left = Obj::StandardSet(StandardSet::C)
                };
                reject(&r, &c, "subject");
            }
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_original_child_wd() {
    for name in BASE {
        let (mut r, _) = super::execute(source(name));
        let n = children(&mut r).len();
        for index in 0..n {
            let (mut r, c) = super::execute(source(name));
            let eq = super::equality_proof_mut(&mut children(&mut r)[index]);
            if eq.fact.left.ir() == eq.fact.right.ir() {
                continue;
            }
            let wd = eq.well_defined_proof.as_detailed_mut().unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
            reject(&r, &c, "child_wd");
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_both_parent_wd() {
    for name in BASE {
        let (mut r, c) = super::execute(source(name));
        let wd = last_equality(&mut r)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap();
        std::mem::swap(&mut wd.left, &mut wd.right);
        reject(&r, &c, "parent_wd");
    }
}
#[test]
fn interval_constructor_equality_preserves_parent_wd_subject() {
    for name in BASE {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let wd = parent_wd(&mut r, right);
            match wd.as_detailed_mut().unwrap() {
                DetailedObjWellDefinedProof::ByDef { obj, .. }
                | DetailedObjWellDefinedProof::ByKnown { obj, .. } => {
                    *obj = Obj::StandardSet(StandardSet::C)
                }
            };
            reject(&r, &c, "parent_subject");
        }
    }
}
#[test]
fn interval_constructor_equality_requires_original_parent_children() {
    for name in BASE {
        for right in [false, true] {
            for extra in [false, true] {
                let (mut r, c) = super::execute(source(name));
                let (mut donor, _) = super::execute(source(name));
                let spare = stages_mut(parent_wd(&mut donor, right)).0.pop().unwrap();
                let children = stages_mut(parent_wd(&mut r, right)).0;
                if extra {
                    children.push(spare)
                } else {
                    children.pop();
                };
                reject(&r, &c, "parent_children");
            }
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_parent_child_order() {
    for name in MULTI {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            stages_mut(parent_wd(&mut r, right)).0.swap(0, 1);
            reject(&r, &c, "parent_child_order");
        }
    }
}
#[test]
fn interval_constructor_equality_requires_original_formation_requirements() {
    for name in BASE {
        for right in [false, true] {
            for extra in [false, true] {
                let (mut r, c) = super::execute(source(name));
                let (mut donor, _) = super::execute(source(name));
                let spare = stages_mut(parent_wd(&mut donor, right)).1.pop().unwrap();
                let req = stages_mut(parent_wd(&mut r, right)).1;
                if extra {
                    req.push(spare)
                } else {
                    req.pop();
                };
                reject(&r, &c, "requirements");
            }
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_formation_requirement_subject() {
    for name in BASE {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let p = super::atomic_proof_mut(&mut stages_mut(parent_wd(&mut r, right)).1[0]);
            let AtomicFact::InFact(p) = &mut p.fact else {
                panic!()
            };
            p.element = Obj::StandardSet(StandardSet::C);
            reject(&r, &c, "requirement_subject");
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_exact_endpoint_domain() {
    for name in BASE {
        for right in [false, true] {
            let (mut run, c) = super::execute(source(name));
            for req in stages_mut(parent_wd(&mut run, right)).1 {
                let AtomicFact::InFact(p) = &mut super::atomic_proof_mut(req).fact else {
                    panic!()
                };
                p.set = Obj::StandardSet(StandardSet::Q);
            }
            reject(&run, &c, "endpoint_domain");
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_requirement_order() {
    for name in MULTI {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            stages_mut(parent_wd(&mut r, right)).1.swap(0, 1);
            reject(&r, &c, "requirement_order");
        }
    }
}
#[test]
fn interval_constructor_equality_requires_original_leaf_citation() {
    for name in BASE {
        for future in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let id = last_equality(&mut r).fact.fact_id;
            path(&mut r, 0).path[0].2 = if future { id } else { FactId::new(u64::MAX) };
            reject(&r, &c, "citation");
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_leaf_path_orientation() {
    for name in BASE {
        let (mut r, c) = super::execute(source(name));
        let edge = &mut path(&mut r, 0).path[0];
        std::mem::swap(&mut edge.0, &mut edge.1);
        reject(&r, &c, "orientation");
    }
}
#[test]
fn interval_constructor_equality_preserves_multi_edge_path_order() {
    for name in BASE {
        let (mut run, c) = super::execute(source(&format!("{name}_path")));
        let p = path(&mut run, 0);
        assert_eq!(p.path.len(), 2);
        p.path.swap(0, 1);
        reject(&run, &c, "path_order");
    }
}
#[test]
fn interval_constructor_equality_cannot_borrow_sibling_equality() {
    let private="forall sc46_private_A,sc46_private_B set:\n    sc46_private_A=sc46_private_B\n    =>:\n        sc46_private_A=sc46_private_B\n";
    let (mut r, c) = super::execute(&format!("{private}\n{}", source("open_open")));
    super::compile_run(&r, &c, "scope_baseline").unwrap();
    let p = super::forall_proof_mut(&mut r.statement_results[0]);
    let id = p.assumed_dom_facts[0]
        .store_and_infer
        .store
        .primary_fact_id();
    path(&mut r, 0).path[0].2 = id;
    reject(&r, &c, "sibling");
}
#[test]
fn interval_constructor_equality_preserves_returned_producer_order() {
    for name in BASE {
        for future in [false, true] {
            let (mut run, c) = super::execute(source(&format!("{name}_returned")));
            let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
            assert_eq!(p.proved_then_facts.len(), 2);
            if future {
                p.proved_then_facts.swap(0, 1)
            } else {
                p.proved_then_facts.remove(0);
            };
            reject(&run, &c, "returned_producer");
        }
    }
}
#[test]
fn interval_constructor_equality_requires_original_source_premises() {
    for name in BASE {
        let (mut r, c) = super::execute(source(name));
        super::forall_proof_mut(r.statement_results.last_mut().unwrap())
            .assumed_dom_facts
            .clear();
        reject(&r, &c, "premises");
    }
}
#[test]
fn interval_constructor_equality_requires_original_endpoint_citation() {
    for name in BASE {
        for right in [false, true] {
            for future in [false, true] {
                let (mut run, c) = super::execute(source(name));
                let id = last_equality(&mut run).fact.fact_id;
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
                    &mut super::atomic_proof_mut(&mut stages_mut(parent_wd(&mut run, right)).1[0])
                        .searched_proof
                else {
                    panic!("original membership citation")
                };
                p.cite_fact_id = if future { id } else { FactId::new(u64::MAX) };
                reject(&run, &c, "membership_citation");
            }
        }
    }
}
#[test]
fn interval_constructor_equality_preserves_endpoint_citation_subject() {
    for name in MULTI {
        for right in [false, true] {
            let (mut run, c) = super::execute(source(name));
            let req = stages_mut(parent_wd(&mut run, right)).1;
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
                &super::atomic_proof_mut(&mut req[1]).searched_proof
            else {
                panic!()
            };
            let id = p.cite_fact_id;
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
                &mut super::atomic_proof_mut(&mut req[0]).searched_proof
            else {
                panic!()
            };
            p.cite_fact_id = id;
            reject(&run, &c, "endpoint_citation_subject");
        }
    }
}
#[test]
fn interval_constructor_equality_cannot_borrow_sibling_membership() {
    let private="forall sc46_private_a set:\n    sc46_private_a $in R\n    =>:\n        sc46_private_a=sc46_private_a\n";
    let (mut run, c) = super::execute(&format!("{private}\n{}", source("lower_open")));
    super::compile_run(&run, &c, "membership_scope_baseline").unwrap();
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let id = p.assumed_dom_facts[0]
        .store_and_infer
        .store
        .primary_fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
        &mut super::atomic_proof_mut(&mut stages_mut(parent_wd(&mut run, true)).1[0])
            .searched_proof
    else {
        panic!()
    };
    p.cite_fact_id = id;
    reject(&run, &c, "sibling_membership");
}
#[test]
fn interval_constructor_equality_rejects_different_bounded_kinds() {
    for name in ["open_open", "open_closed", "closed_open", "closed_closed"] {
        let (mut run, c) = super::execute(source(name));
        retag_bounded(&mut last_equality(&mut run).fact.right);
        let DetailedObjWellDefinedProof::ByDef { obj, .. } =
            parent_wd(&mut run, true).as_detailed_mut().unwrap()
        else {
            panic!()
        };
        retag_bounded(obj);
        reject(&run, &c, "bounded_kind");
    }
}
#[test]
fn interval_constructor_equality_rejects_different_ray_openness() {
    for name in RAYS {
        let (mut run, c) = super::execute(source(name));
        retag_ray(&mut last_equality(&mut run).fact.right, false);
        let DetailedObjWellDefinedProof::ByDef { obj, .. } =
            parent_wd(&mut run, true).as_detailed_mut().unwrap()
        else {
            panic!()
        };
        retag_ray(obj, false);
        reject(&run, &c, "ray_openness");
    }
}
#[test]
fn interval_constructor_equality_rejects_different_ray_direction() {
    for name in RAYS {
        let (mut run, c) = super::execute(source(name));
        retag_ray(&mut last_equality(&mut run).fact.right, true);
        let DetailedObjWellDefinedProof::ByDef { obj, .. } =
            parent_wd(&mut run, true).as_detailed_mut().unwrap()
        else {
            panic!()
        };
        retag_ray(obj, true);
        reject(&run, &c, "ray_direction");
    }
}
#[test]
fn interval_constructor_equality_rejects_half_open_closed_retag() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        ClosedRangeObjWellDefinedProof, RangeObjWellDefinedProof,
    };
    for name in ["range", "closed_range"] {
        let (mut run, c) = super::execute(source(name));
        retag_integer(&mut last_equality(&mut run).fact.right);
        let DetailedObjWellDefinedProof::ByDef {
            obj,
            proof: ObjWellDefinedProofByDef::SetFormer(p),
        } = parent_wd(&mut run, true).as_detailed_mut().unwrap()
        else {
            panic!()
        };
        retag_integer(obj);
        let original = std::mem::replace(
            p,
            SetFormerObjWellDefinedProofByDef::Range(RangeObjWellDefinedProof {
                child_obj_well_defined: vec![],
                requirement_fact_verified: vec![],
            }),
        );
        *p = match original {
            SetFormerObjWellDefinedProofByDef::Range(p) => {
                SetFormerObjWellDefinedProofByDef::ClosedRange(ClosedRangeObjWellDefinedProof {
                    child_obj_well_defined: p.child_obj_well_defined,
                    requirement_fact_verified: p.requirement_fact_verified,
                })
            }
            SetFormerObjWellDefinedProofByDef::ClosedRange(p) => {
                SetFormerObjWellDefinedProofByDef::Range(RangeObjWellDefinedProof {
                    child_obj_well_defined: p.child_obj_well_defined,
                    requirement_fact_verified: p.requirement_fact_verified,
                })
            }
            _ => panic!(),
        };
        reject(&run, &c, "integer_kind");
    }
}
fn retag_integer(obj: &mut Obj) {
    let Obj::SetFormer(p) = obj else { panic!() };
    *p = match p {
        SetFormer::Range(p) => SetFormer::ClosedRange(ClosedRange {
            start: p.start.clone(),
            end: p.end.clone(),
        }),
        SetFormer::ClosedRange(p) => SetFormer::Range(Range {
            start: p.start.clone(),
            end: p.end.clone(),
        }),
        _ => panic!(),
    };
}
fn retag_bounded(obj: &mut Obj) {
    let Obj::SetFormer(SetFormer::IntervalObj(p)) = obj else {
        panic!()
    };
    *p = match p {
        IntervalObj::LeftOpenRightOpen(v) => IntervalObj::LeftClosedRightOpen(v.clone()),
        IntervalObj::LeftOpenRightClosed(v) => IntervalObj::LeftClosedRightClosed(v.clone()),
        IntervalObj::LeftClosedRightOpen(v) => IntervalObj::LeftOpenRightOpen(v.clone()),
        IntervalObj::LeftClosedRightClosed(v) => IntervalObj::LeftOpenRightClosed(v.clone()),
    };
}
fn retag_ray(obj: &mut Obj, direction: bool) {
    let Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) = obj else {
        panic!()
    };
    *p = match (p.clone(), direction) {
        (OneSideInfinityIntervalObj::LowerOpen(v), false) => {
            OneSideInfinityIntervalObj::LowerClosed(v)
        }
        (OneSideInfinityIntervalObj::LowerClosed(v), false) => {
            OneSideInfinityIntervalObj::LowerOpen(v)
        }
        (OneSideInfinityIntervalObj::UpperOpen(v), false) => {
            OneSideInfinityIntervalObj::UpperClosed(v)
        }
        (OneSideInfinityIntervalObj::UpperClosed(v), false) => {
            OneSideInfinityIntervalObj::UpperOpen(v)
        }
        (OneSideInfinityIntervalObj::LowerOpen(v), true) => {
            OneSideInfinityIntervalObj::UpperOpen(v)
        }
        (OneSideInfinityIntervalObj::LowerClosed(v), true) => {
            OneSideInfinityIntervalObj::UpperClosed(v)
        }
        (OneSideInfinityIntervalObj::UpperOpen(v), true) => {
            OneSideInfinityIntervalObj::LowerOpen(v)
        }
        (OneSideInfinityIntervalObj::UpperClosed(v), true) => {
            OneSideInfinityIntervalObj::LowerClosed(v)
        }
    };
}

fn last_verify(r: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) =
        r.statement_results.last_mut().unwrap()
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
fn last_equality(r: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    super::equality_proof_mut(last_verify(r))
}
fn children(r: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut last_equality(r).searched_proof
    else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn path(r: &mut RunLitexCodeResult, i: usize) -> &mut KnownEqualityPathProof {
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
    ) = &mut super::equality_proof_mut(&mut children(r)[i]).searched_proof
    else {
        panic!()
    };
    p
}
fn parent_wd(r: &mut RunLitexCodeResult, right: bool) -> &mut ObjWellDefinedProof {
    let p = last_equality(r)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    if right {
        &mut p.right
    } else {
        &mut p.left
    }
}
fn stages_mut(
    wd: &mut ObjWellDefinedProof,
) -> (
    &mut Vec<Box<ObjWellDefinedProof>>,
    &mut Vec<VerifyFactResult>,
) {
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetFormer(p),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!()
    };
    match p {
        SetFormerObjWellDefinedProofByDef::Range(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        SetFormerObjWellDefinedProofByDef::ClosedRange(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        SetFormerObjWellDefinedProofByDef::IntervalObj(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        SetFormerObjWellDefinedProofByDef::OneSideInfinityIntervalObj(p) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        _ => panic!(),
    }
}
fn reject(r: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, n: &str) {
    let e = super::compile_run(r, c, n).expect_err("altered evidence accepted");
    if matches!(
        n,
        "bounded_kind" | "ray_openness" | "ray_direction" | "integer_kind"
    ) {
        // Whole-run subject validation rejects the altered source conclusion first.
        // Separately exercise the leaf's shape guard without fabricating a matching
        // source wrapper or stores. A kind mismatch must reject before any citation.
        assert!(e.to_string().contains("Forall/Then"), "{n}:{e}");
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) =
            r.statement_results.last().unwrap()
        else {
            panic!()
        };
        let VerifyFactResult::ForallFact(p) = &p.verify_result else {
            panic!()
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
            p.as_ref()
        else {
            panic!()
        };
        let VerifyFactResult::Equality(p) = &p.proved_then_facts.last().unwrap().verify_result
        else {
            panic!()
        };
        let VerifyEqualityResult::Success(p) = p.as_ref() else {
            panic!()
        };
        let EqualFactSearchedProof::ByMatchingOneArgByOne(children) = &p.searched_proof else {
            panic!()
        };
        let position = crate::compile_to_lean::source_position::SourcePosition::new(
            None,
            crate::compile_to_lean::source_position::SourceOwner::Term,
            0,
        );
        let leaf = c
            .compile_matching_one_arg_by_one(
                &p.fact,
                &children.corresponding_arg_equal_proofs,
                &position,
            )
            .expect_err("different kinds cannot be congruent constructors");
        assert!(
            leaf.to_string().contains(if n == "integer_kind" {
                "Equality/MatchingOneArgByOne/Constructor"
            } else {
                "IntervalCongruence/Kind"
            }),
            "{n}:{leaf}"
        );
    }
}

fn source(name: &str) -> &str {
    PROFILES.iter().find(|p| p.0 == name).unwrap().1
}
const BASE: &[&str] = &[
    "range",
    "closed_range",
    "open_open",
    "open_closed",
    "closed_open",
    "closed_closed",
    "lower_open",
    "lower_closed",
    "upper_open",
    "upper_closed",
];
const MULTI: &[&str] = &[
    "range",
    "closed_range",
    "open_open",
    "open_closed",
    "closed_open",
    "closed_closed",
];
const RAYS: &[&str] = &["lower_open", "lower_closed", "upper_open", "upper_closed"];

const SOURCES:&[(&str,&str)]=&[
("range","forall eq46_a,eq46_b,eq46_c,eq46_d Z:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        range(eq46_a,eq46_c)=range(eq46_b,eq46_d)\n"),
("closed_range","forall eq46_a,eq46_b,eq46_c,eq46_d Z:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        closed_range(eq46_a,eq46_c)=closed_range(eq46_b,eq46_d)\n"),
("open_open","forall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '(eq46_a,eq46_c)='(eq46_b,eq46_d)\n"),
("open_closed","forall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '(eq46_a,eq46_c]='(eq46_b,eq46_d]\n"),
("closed_open","forall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '[eq46_a,eq46_c)='[eq46_b,eq46_d)\n"),
("closed_closed","forall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '[eq46_a,eq46_c]='[eq46_b,eq46_d]\n"),
("lower_open","forall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '(eq46_a,)='(eq46_b,)\n"),
("lower_closed","forall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '[eq46_a,)='[eq46_b,)\n"),
("upper_open","forall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '(,eq46_a)='(,eq46_b)\n"),
("upper_closed","forall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '(,eq46_a]='(,eq46_b]\n"),
];

const PROFILES:&[(&str,&str)]=&[
("range","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b,eq46_c,eq46_d Z:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        range(eq46_a,eq46_c)=range(eq46_b,eq46_d)\n"),
("closed_range","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b,eq46_c,eq46_d Z:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        closed_range(eq46_a,eq46_c)=closed_range(eq46_b,eq46_d)\n"),
("open_open","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '(eq46_a,eq46_c)='(eq46_b,eq46_d)\n"),
("open_closed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '(eq46_a,eq46_c]='(eq46_b,eq46_d]\n"),
("closed_open","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '[eq46_a,eq46_c)='[eq46_b,eq46_d)\n"),
("closed_closed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b,eq46_c,eq46_d R:\n    eq46_a=eq46_b\n    eq46_c=eq46_d\n    =>:\n        '[eq46_a,eq46_c]='[eq46_b,eq46_d]\n"),
("lower_open","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '(eq46_a,)='(eq46_b,)\n"),
("lower_closed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '[eq46_a,)='[eq46_b,)\n"),
("upper_open","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '(,eq46_a)='(,eq46_b)\n"),
("upper_closed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall eq46_a,eq46_b R:\n    eq46_a=eq46_b\n    =>:\n        '(,eq46_a]='(,eq46_b]\n"),
("range_left","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c Z:\n    sc46_a=sc46_b\n    =>:\n        range(sc46_a,sc46_c)=range(sc46_b,sc46_c)\n"),
("range_right","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c Z:\n    sc46_a=sc46_b\n    =>:\n        range(sc46_c,sc46_a)=range(sc46_c,sc46_b)\n"),
("range_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_E Z:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        range(sc46_c,sc46_E)=range(sc46_a,sc46_E)\n"),
("range_repeated","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b Z:\n    sc46_a=sc46_b\n    =>:\n        range(sc46_a,sc46_a)=range(sc46_b,sc46_b)\n"),
("range_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) Z,sc46_E Z:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        range(sc46_f(0),sc46_E)=range(sc46_g(0),sc46_E)\n"),
("range_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a Z:\n    sc46_a=0\n    =>:\n        range(sc46_a,2)=range(0,2)\n"),
("closed_range_left","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c Z:\n    sc46_a=sc46_b\n    =>:\n        closed_range(sc46_a,sc46_c)=closed_range(sc46_b,sc46_c)\n"),
("closed_range_right","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c Z:\n    sc46_a=sc46_b\n    =>:\n        closed_range(sc46_c,sc46_a)=closed_range(sc46_c,sc46_b)\n"),
("closed_range_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_E Z:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        closed_range(sc46_c,sc46_E)=closed_range(sc46_a,sc46_E)\n"),
("closed_range_repeated","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b Z:\n    sc46_a=sc46_b\n    =>:\n        closed_range(sc46_a,sc46_a)=closed_range(sc46_b,sc46_b)\n"),
("closed_range_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) Z,sc46_E Z:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        closed_range(sc46_f(0),sc46_E)=closed_range(sc46_g(0),sc46_E)\n"),
("closed_range_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a Z:\n    sc46_a=0\n    =>:\n        closed_range(sc46_a,2)=closed_range(0,2)\n"),
("open_open_left","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '(sc46_a,sc46_c)='(sc46_b,sc46_c)\n"),
("open_open_right","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '(sc46_c,sc46_a)='(sc46_c,sc46_b)\n"),
("open_open_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_E R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '(sc46_c,sc46_E)='(sc46_a,sc46_E)\n"),
("open_open_repeated","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b R:\n    sc46_a=sc46_b\n    =>:\n        '(sc46_a,sc46_a)='(sc46_b,sc46_b)\n"),
("open_open_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R,sc46_E R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '(sc46_f(0),sc46_E)='(sc46_g(0),sc46_E)\n"),
("open_open_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '(sc46_a,2)='(0,2)\n"),
("open_closed_left","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '(sc46_a,sc46_c]='(sc46_b,sc46_c]\n"),
("open_closed_right","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '(sc46_c,sc46_a]='(sc46_c,sc46_b]\n"),
("open_closed_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_E R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '(sc46_c,sc46_E]='(sc46_a,sc46_E]\n"),
("open_closed_repeated","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b R:\n    sc46_a=sc46_b\n    =>:\n        '(sc46_a,sc46_a]='(sc46_b,sc46_b]\n"),
("open_closed_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R,sc46_E R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '(sc46_f(0),sc46_E]='(sc46_g(0),sc46_E]\n"),
("open_closed_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '(sc46_a,2]='(0,2]\n"),
("closed_open_left","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '[sc46_a,sc46_c)='[sc46_b,sc46_c)\n"),
("closed_open_right","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '[sc46_c,sc46_a)='[sc46_c,sc46_b)\n"),
("closed_open_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_E R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '[sc46_c,sc46_E)='[sc46_a,sc46_E)\n"),
("closed_open_repeated","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b R:\n    sc46_a=sc46_b\n    =>:\n        '[sc46_a,sc46_a)='[sc46_b,sc46_b)\n"),
("closed_open_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R,sc46_E R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '[sc46_f(0),sc46_E)='[sc46_g(0),sc46_E)\n"),
("closed_open_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '[sc46_a,2)='[0,2)\n"),
("closed_closed_left","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '[sc46_a,sc46_c]='[sc46_b,sc46_c]\n"),
("closed_closed_right","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    =>:\n        '[sc46_c,sc46_a]='[sc46_c,sc46_b]\n"),
("closed_closed_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_E R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '[sc46_c,sc46_E]='[sc46_a,sc46_E]\n"),
("closed_closed_repeated","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b R:\n    sc46_a=sc46_b\n    =>:\n        '[sc46_a,sc46_a]='[sc46_b,sc46_b]\n"),
("closed_closed_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R,sc46_E R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '[sc46_f(0),sc46_E]='[sc46_g(0),sc46_E]\n"),
("closed_closed_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '[sc46_a,2]='[0,2]\n"),
("lower_open_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '(sc46_c,)='(sc46_a,)\n"),
("lower_open_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '(sc46_f(0),)='(sc46_g(0),)\n"),
("lower_open_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '(sc46_a,)='(0,)\n"),
("lower_closed_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '[sc46_c,)='[sc46_a,)\n"),
("lower_closed_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '[sc46_f(0),)='[sc46_g(0),)\n"),
("lower_closed_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '[sc46_a,)='[0,)\n"),
("upper_open_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '(,sc46_c)='(,sc46_a)\n"),
("upper_open_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '(,sc46_f(0))='(,sc46_g(0))\n"),
("upper_open_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '(,sc46_a)='(,0)\n"),
("upper_closed_path","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c R:\n    sc46_a=sc46_b\n    sc46_b=sc46_c\n    =>:\n        '(,sc46_c]='(,sc46_a]\n"),
("upper_closed_returned","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_f,sc46_g fn(sc46_x R) R:\n    sc46_f=sc46_g\n    =>:\n        sc46_f(0)=sc46_g(0)\n        '(,sc46_f(0)]='(,sc46_g(0)]\n"),
("upper_closed_mixed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a R:\n    sc46_a=0\n    =>:\n        '(,sc46_a]='(,0]\n"),
("range_reversed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_d Z:\n    sc46_a=sc46_b\n    sc46_c=sc46_d\n    sc46_c<sc46_a\n    sc46_d<sc46_b\n    =>:\n        range(sc46_a,sc46_c)=range(sc46_b,sc46_d)\n"),
("closed_range_reversed","# Equal endpoints preserve this exact range or interval kind with original endpoint membership.\nforall sc46_a,sc46_b,sc46_c,sc46_d Z:\n    sc46_a=sc46_b\n    sc46_c=sc46_d\n    sc46_c<sc46_a\n    sc46_d<sc46_b\n    =>:\n        closed_range(sc46_a,sc46_c)=closed_range(sc46_b,sc46_d)\n"),
];
