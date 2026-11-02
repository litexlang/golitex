use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ObjWellDefinedProof;
use crate::prelude::*;
#[test]
fn finite_constructor_equality_original_six_ordered_trees() {
    for (name, source) in SOURCES {
        let (mut run, c) = super::execute(source);
        let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
        let eq =
            super::equality_proof_mut(&mut p.proved_then_facts.last_mut().unwrap().verify_result);
        let pairs=crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs(&eq.fact.left,&eq.fact.right).unwrap();
        assert_eq!(
            eq.well_defined_proof.detailed_ref().left.obj().ir(),
            eq.fact.left.ir()
        );
        assert_eq!(
            eq.well_defined_proof.detailed_ref().right.obj().ir(),
            eq.fact.right.ir()
        );
        for wd in [
            &eq.well_defined_proof.detailed_ref().left,
            &eq.well_defined_proof.detailed_ref().right,
        ] {
            let (children, req) = stages(wd);
            eprintln!(
                "ORIGINAL45 {name} parent:{} child_count:{} requirement_count:{}",
                wd.obj().display_string(),
                children.len(),
                req.len()
            );
            for child in children {
                eprintln!("WD child:{}", child.obj().display_string());
            }
            for r in req {
                eprintln!(
                    "WD requirement:{}",
                    source_subject(r).unwrap().display_string()
                );
            }
        }
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut eq.searched_proof else {
            panic!("original selected route")
        };
        assert_eq!(p.corresponding_arg_equal_proofs.len(), pairs.len());
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
            let method = match &child.searched_proof {
                EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
                ) => {
                    assert_eq!(p.path.len(), 1);
                    format!("cited path {}", p.path[0].2.value())
                }
                EqualFactSearchedProof::ByTheyAreTheSame(_) => "same".to_owned(),
                _ => panic!("unexpected original route"),
            };
            eprintln!(
                "ORIGINAL45 {name} child{index}:{}={} via {method}",
                left.display_string(),
                right.display_string()
            );
        }
        super::compile_run(&run, &c, name).unwrap();
    }
}

#[test]
fn finite_constructor_equality_all_actual_profiles() {
    for (name, source) in PROFILES {
        let (run, c) = super::execute(source);
        super::compile_run(&run, &c, name).unwrap();
    }
}
#[test]
fn finite_constructor_equality_requires_exact_child_arity() {
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
fn finite_constructor_equality_preserves_operand_order() {
    for name in MULTI {
        let (mut r, c) = super::execute(source(name));
        children(&mut r).swap(0, 1);
        reject(&r, &c, "order");
    }
}
#[test]
fn finite_constructor_equality_preserves_each_child_subject() {
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
fn finite_constructor_equality_preserves_original_child_wd() {
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
fn finite_constructor_equality_preserves_both_parent_wd() {
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
fn finite_constructor_equality_preserves_parent_wd_subject() {
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
fn finite_constructor_equality_requires_original_parent_children() {
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
fn finite_constructor_equality_preserves_parent_child_order() {
    for name in MULTI {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            stages_mut(parent_wd(&mut r, right)).0.swap(0, 1);
            reject(&r, &c, "parent_child_order");
        }
    }
}
#[test]
fn finite_constructor_equality_requires_original_formation_requirements() {
    for name in ["literal_pair", "sequence", "finite_sequence_both"] {
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
fn finite_constructor_equality_preserves_formation_requirement_subject() {
    for name in ["literal_pair", "sequence", "finite_sequence_both"] {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let p = super::atomic_proof_mut(&mut stages_mut(parent_wd(&mut r, right)).1[0]);
            match &mut p.fact {
                AtomicFact::NotEqualFact(p) => p.left = Obj::StandardSet(StandardSet::C),
                AtomicFact::IsSetFact(p) => p.set = Obj::StandardSet(StandardSet::C),
                _ => panic!(),
            };
            reject(&r, &c, "requirement_subject");
        }
    }
}
#[test]
fn finite_constructor_equality_preserves_natural_length_requirement() {
    for name in ["finite_sequence_both", "finite_sequence_returned_length"] {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let AtomicFact::InFact(p) =
                &mut super::atomic_proof_mut(&mut stages_mut(parent_wd(&mut r, right)).1[1]).fact
            else {
                panic!()
            };
            p.set = Obj::StandardSet(StandardSet::R);
            reject(&r, &c, "length_carrier");
        }
    }
}
#[test]
fn finite_constructor_equality_preserves_requirement_order() {
    for name in ["finite_sequence_both", "literal_triple"] {
        for right in [false, true] {
            let (mut r, c) = super::execute(source(name));
            stages_mut(parent_wd(&mut r, right)).1.swap(0, 1);
            reject(&r, &c, "requirement_order");
        }
    }
}
#[test]
fn finite_constructor_equality_preserves_literal_distinctness_orientation() {
    for right in [false, true] {
        let (mut r, c) = super::execute(source("literal_pair"));
        let AtomicFact::NotEqualFact(p) =
            &mut super::atomic_proof_mut(&mut stages_mut(parent_wd(&mut r, right)).1[0]).fact
        else {
            panic!()
        };
        std::mem::swap(&mut p.left, &mut p.right);
        reject(&r, &c, "distinctness_orientation");
    }
}
#[test]
fn finite_constructor_equality_requires_original_distinctness_citation() {
    for right in [false, true] {
        let (mut r, c) = super::execute(source("literal_pair"));
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
            &mut super::atomic_proof_mut(&mut stages_mut(parent_wd(&mut r, right)).1[0])
                .searched_proof
        else {
            panic!("original distinctness citation")
        };
        p.cite_fact_id = FactId::new(u64::MAX);
        reject(&r, &c, "distinctness_citation");
    }
}
#[test]
fn finite_constructor_equality_requires_original_leaf_citation() {
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
fn finite_constructor_equality_preserves_leaf_path_orientation() {
    for name in BASE {
        let (mut r, c) = super::execute(source(name));
        let edge = &mut path(&mut r, 0).path[0];
        std::mem::swap(&mut edge.0, &mut edge.1);
        reject(&r, &c, "orientation");
    }
}
#[test]
fn finite_constructor_equality_preserves_multi_edge_path_order() {
    for name in [
        "singleton_path",
        "sequence_path",
        "finite_sequence_path",
        "cartesian_path",
    ] {
        let (mut r, c) = super::execute(source(name));
        let p = path(&mut r, 0);
        assert_eq!(p.path.len(), 2);
        p.path.swap(0, 1);
        reject(&r, &c, "path_order");
    }
}
#[test]
fn finite_constructor_equality_cannot_borrow_sibling_equality() {
    let private="forall sc45_private_A,sc45_private_B set:\n    sc45_private_A=sc45_private_B\n    =>:\n        sc45_private_A=sc45_private_B\n";
    let (mut r, c) = super::execute(&format!("{private}\n{}", source("sequence")));
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
fn finite_constructor_equality_preserves_returned_producer_order() {
    for name in [
        "singleton_returned",
        "sequence_returned",
        "finite_sequence_returned",
        "finite_sequence_returned_length",
        "cartesian_returned",
    ] {
        for future in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let p = super::forall_proof_mut(r.statement_results.last_mut().unwrap());
            let last = p.proved_then_facts.len() - 1;
            if future {
                p.proved_then_facts.swap(0, last)
            } else {
                p.proved_then_facts.remove(0);
            };
            reject(&r, &c, "returned_producer");
        }
    }
}
#[test]
fn finite_constructor_equality_preserves_nested_producer_order() {
    for name in [
        "singleton_nested",
        "sequence_nested",
        "finite_sequence_nested",
        "cartesian_nested",
    ] {
        for future in [false, true] {
            let (mut r, c) = super::execute(source(name));
            let p = super::forall_proof_mut(r.statement_results.last_mut().unwrap());
            assert_eq!(p.proved_then_facts.len(), 2);
            if future {
                p.proved_then_facts.swap(0, 1)
            } else {
                p.proved_then_facts.remove(0);
            };
            reject(&r, &c, "nested_producer");
        }
    }
}
#[test]
fn finite_constructor_equality_requires_original_source_premises() {
    for name in BASE {
        let (mut r, c) = super::execute(source(name));
        super::forall_proof_mut(r.statement_results.last_mut().unwrap())
            .assumed_dom_facts
            .clear();
        reject(&r, &c, "premises");
    }
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
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        ObjWellDefinedProofByDef as B, ProductShapeObjWellDefinedProofByDef as P,
        SetFormerObjWellDefinedProofByDef as S,
    };
    let DetailedObjWellDefinedProof::ByDef { proof, .. } = wd.as_detailed_mut().unwrap() else {
        panic!()
    };
    match proof {
        B::SetFormer(S::ListSet(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        B::SetFormer(S::SeqSet(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        B::SetFormer(S::FiniteSeqSet(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        B::ProductShape(P::Cart(p)) => (
            &mut p.child_obj_well_defined,
            &mut p.requirement_fact_verified,
        ),
        _ => panic!(),
    }
}
fn reject(r: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, n: &str) {
    assert!(
        super::compile_run(r, c, n).is_err(),
        "altered evidence accepted:{n}"
    );
}
fn source(name: &str) -> &str {
    PROFILES.iter().find(|p| p.0 == name).unwrap().1
}
const BASE: &[&str] = &[
    "singleton",
    "literal_pair",
    "sequence",
    "finite_sequence",
    "finite_sequence_both",
    "cartesian",
];
const MULTI: &[&str] = &["literal_pair", "finite_sequence_both", "cartesian"];
const SOURCES:&[(&str,&str)]=&[
("singleton","forall eq45_a,eq45_b R:\n    eq45_a=eq45_b\n    =>:\n        {eq45_a}={eq45_b}\n"),
("literal_pair","forall eq45_a,eq45_b,eq45_c,eq45_d R:\n    eq45_a=eq45_b\n    eq45_c=eq45_d\n    eq45_a!=eq45_c\n    eq45_b!=eq45_d\n    =>:\n        {eq45_a,eq45_c}={eq45_b,eq45_d}\n"),
("sequence","forall eq45_A,eq45_B set:\n    eq45_A=eq45_B\n    =>:\n        seq(eq45_A)=seq(eq45_B)\n"),
("finite_sequence","forall eq45_A,eq45_B set:\n    eq45_A=eq45_B\n    =>:\n        finite_seq(eq45_A,2)=finite_seq(eq45_B,2)\n"),
("finite_sequence_both","forall eq45_A,eq45_B set,eq45_n,eq45_m N:\n    eq45_A=eq45_B\n    eq45_n=eq45_m\n    =>:\n        finite_seq(eq45_A,eq45_n)=finite_seq(eq45_B,eq45_m)\n"),
("cartesian","forall eq45_A,eq45_B,eq45_C,eq45_D set:\n    eq45_A=eq45_B\n    eq45_C=eq45_D\n    =>:\n        cart(eq45_A,eq45_C)=cart(eq45_B,eq45_D)\n"),
];

fn stages(wd: &ObjWellDefinedProof) -> (&Vec<Box<ObjWellDefinedProof>>, &Vec<VerifyFactResult>) {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof as D, ObjWellDefinedProofByDef as B,
        ProductShapeObjWellDefinedProofByDef as P, SetFormerObjWellDefinedProofByDef as S,
    };
    let D::ByDef { proof, .. } = wd.detailed_ref() else {
        panic!("original constructor WD")
    };
    match proof {
        B::SetFormer(S::ListSet(p)) => (&p.child_obj_well_defined, &p.requirement_fact_verified),
        B::SetFormer(S::SeqSet(p)) => (&p.child_obj_well_defined, &p.requirement_fact_verified),
        B::SetFormer(S::FiniteSeqSet(p)) => {
            (&p.child_obj_well_defined, &p.requirement_fact_verified)
        }
        B::ProductShape(P::Cart(p)) => (&p.child_obj_well_defined, &p.requirement_fact_verified),
        _ => panic!(),
    }
}

const PROFILES:&[(&str,&str)]=&[
("singleton","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall eq45_a,eq45_b R:\n    eq45_a=eq45_b\n    =>:\n        {eq45_a}={eq45_b}\n"),
("literal_pair","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall eq45_a,eq45_b,eq45_c,eq45_d R:\n    eq45_a=eq45_b\n    eq45_c=eq45_d\n    eq45_a!=eq45_c\n    eq45_b!=eq45_d\n    =>:\n        {eq45_a,eq45_c}={eq45_b,eq45_d}\n"),
("sequence","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall eq45_A,eq45_B set:\n    eq45_A=eq45_B\n    =>:\n        seq(eq45_A)=seq(eq45_B)\n"),
("finite_sequence","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall eq45_A,eq45_B set:\n    eq45_A=eq45_B\n    =>:\n        finite_seq(eq45_A,2)=finite_seq(eq45_B,2)\n"),
("finite_sequence_both","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall eq45_A,eq45_B set,eq45_n,eq45_m N:\n    eq45_A=eq45_B\n    eq45_n=eq45_m\n    =>:\n        finite_seq(eq45_A,eq45_n)=finite_seq(eq45_B,eq45_m)\n"),
("cartesian","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall eq45_A,eq45_B,eq45_C,eq45_D set:\n    eq45_A=eq45_B\n    eq45_C=eq45_D\n    =>:\n        cart(eq45_A,eq45_C)=cart(eq45_B,eq45_D)\n"),
("singleton_path","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_a,sc45_b,sc45_c R:\n    sc45_a=sc45_b\n    sc45_b=sc45_c\n    =>:\n        {sc45_c}={sc45_a}\n"),
("singleton_functions","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) R:\n    sc45_f=sc45_g\n    =>:\n        {sc45_f}={sc45_g}\n"),
("singleton_returned","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) R:\n    sc45_f=sc45_g\n    =>:\n        sc45_f(0)=sc45_g(0)\n        {sc45_f(0)}={sc45_g(0)}\n"),
("singleton_nested","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_a,sc45_b R:\n    sc45_a=sc45_b\n    =>:\n        {sc45_a}={sc45_b}\n        {{sc45_a}}={{sc45_b}}\n"),
("literal_pair_left","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_a,sc45_b,sc45_c R:\n    sc45_a=sc45_b\n    sc45_a!=sc45_c\n    sc45_b!=sc45_c\n    sc45_c!=sc45_a\n    sc45_c!=sc45_b\n    =>:\n        {sc45_a,sc45_c}={sc45_b,sc45_c}\n"),
("literal_pair_right","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_a,sc45_b,sc45_c R:\n    sc45_a=sc45_b\n    sc45_a!=sc45_c\n    sc45_b!=sc45_c\n    sc45_c!=sc45_a\n    sc45_c!=sc45_b\n    =>:\n        {sc45_c,sc45_a}={sc45_c,sc45_b}\n"),
("literal_triple","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_a,sc45_b,sc45_c,sc45_d,sc45_e,sc45_f R:\n    sc45_a=sc45_b\n    sc45_c=sc45_d\n    sc45_e=sc45_f\n    sc45_a!=sc45_c\n    sc45_a!=sc45_e\n    sc45_c!=sc45_e\n    sc45_b!=sc45_d\n    sc45_b!=sc45_f\n    sc45_d!=sc45_f\n    =>:\n        {sc45_a,sc45_c,sc45_e}={sc45_b,sc45_d,sc45_f}\n"),
("sequence_path","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B,sc45_C set:\n    sc45_A=sc45_B\n    sc45_B=sc45_C\n    =>:\n        seq(sc45_C)=seq(sc45_A)\n"),
("sequence_functions","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) R:\n    sc45_f=sc45_g\n    =>:\n        seq(sc45_f)=seq(sc45_g)\n"),
("sequence_returned","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) power_set(R):\n    sc45_f=sc45_g\n    =>:\n        sc45_f(0)=sc45_g(0)\n        seq(sc45_f(0))=seq(sc45_g(0))\n"),
("sequence_nested","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set:\n    sc45_A=sc45_B\n    =>:\n        seq(sc45_A)=seq(sc45_B)\n        seq(seq(sc45_A))=seq(seq(sc45_B))\n"),
("finite_sequence_path","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B,sc45_C set:\n    sc45_A=sc45_B\n    sc45_B=sc45_C\n    =>:\n        finite_seq(sc45_C,2)=finite_seq(sc45_A,2)\n"),
("finite_sequence_functions","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) R:\n    sc45_f=sc45_g\n    =>:\n        finite_seq(sc45_f,2)=finite_seq(sc45_g,2)\n"),
("finite_sequence_returned","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) power_set(R):\n    sc45_f=sc45_g\n    =>:\n        sc45_f(0)=sc45_g(0)\n        finite_seq(sc45_f(0),2)=finite_seq(sc45_g(0),2)\n"),
("finite_sequence_nested","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set:\n    sc45_A=sc45_B\n    =>:\n        finite_seq(sc45_A,2)=finite_seq(sc45_B,2)\n        finite_seq(finite_seq(sc45_A,2),2)=finite_seq(finite_seq(sc45_B,2),2)\n"),
("cartesian_path","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B,sc45_C set,sc45_E set:\n    sc45_A=sc45_B\n    sc45_B=sc45_C\n    =>:\n        cart(sc45_C,sc45_E)=cart(sc45_A,sc45_E)\n"),
("cartesian_functions","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) R,sc45_E set:\n    sc45_f=sc45_g\n    =>:\n        cart(sc45_f,sc45_E)=cart(sc45_g,sc45_E)\n"),
("cartesian_returned","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_f,sc45_g fn(sc45_x R) power_set(R),sc45_E set:\n    sc45_f=sc45_g\n    =>:\n        sc45_f(0)=sc45_g(0)\n        cart(sc45_f(0),sc45_E)=cart(sc45_g(0),sc45_E)\n"),
("cartesian_nested","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set,sc45_E set:\n    sc45_A=sc45_B\n    =>:\n        cart(sc45_A,sc45_E)=cart(sc45_B,sc45_E)\n        cart(cart(sc45_A,sc45_E),sc45_E)=cart(cart(sc45_B,sc45_E),sc45_E)\n"),
("finite_sequence_length","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A set,sc45_n,sc45_m N:\n    sc45_n=sc45_m\n    =>:\n        finite_seq(sc45_A,sc45_n)=finite_seq(sc45_A,sc45_m)\n"),
("finite_sequence_zero","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set:\n    sc45_A=sc45_B\n    =>:\n        finite_seq(sc45_A,0)=finite_seq(sc45_B,0)\n"),
("finite_sequence_length_path","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set,sc45_n,sc45_m,sc45_k N:\n    sc45_A=sc45_B\n    sc45_n=sc45_m\n    sc45_m=sc45_k\n    =>:\n        finite_seq(sc45_B,sc45_k)=finite_seq(sc45_A,sc45_n)\n"),
("finite_sequence_returned_length","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set,sc45_f,sc45_g fn(sc45_x R) N:\n    sc45_A=sc45_B\n    sc45_f=sc45_g\n    =>:\n        sc45_f(0)=sc45_g(0)\n        finite_seq(sc45_A,sc45_f(0))=finite_seq(sc45_B,sc45_g(0))\n"),
("cartesian_left","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B,sc45_C set:\n    sc45_A=sc45_B\n    =>:\n        cart(sc45_A,sc45_C)=cart(sc45_B,sc45_C)\n"),
("cartesian_right","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B,sc45_C set:\n    sc45_A=sc45_B\n    =>:\n        cart(sc45_C,sc45_A)=cart(sc45_C,sc45_B)\n"),
("cartesian_repeated","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set:\n    sc45_A=sc45_B\n    =>:\n        cart(sc45_A,sc45_A)=cart(sc45_B,sc45_B)\n"),
("cartesian_unary","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B set:\n    sc45_A=sc45_B\n    =>:\n        cart(sc45_A)=cart(sc45_B)\n"),
("cartesian_ternary","# Replay the recorded ordered constructor equalities with original formation evidence.\nforall sc45_A,sc45_B,sc45_C,sc45_D,sc45_E,sc45_F set:\n    sc45_A=sc45_B\n    sc45_C=sc45_D\n    sc45_E=sc45_F\n    =>:\n        cart(sc45_A,sc45_C,sc45_E)=cart(sc45_B,sc45_D,sc45_F)\n"),
];
