use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof as Match;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    DetailedObjWellDefinedProof, ObjWellDefinedProof, ObjWellDefinedProofByDef,
    ProductShapeObjWellDefinedProofByDef,
};
use crate::prelude::*;
#[test]
fn known_cartesian_original_binary_match_and_formation() {
    let (mut run, c) = super::execute(SOURCE);
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let FactWellDefinedProof::ForallFact(source_wd) = &outer.assumed_dom_facts[0].well_defined
    else {
        panic!("original assumed universal formation")
    };
    let FactWellDefinedProof::AtomicExceptEquality(source_wd) = &source_wd.detailed_ref().then[0]
    else {
        panic!("original selected source membership")
    };
    let source_wd = &source_wd.detailed_ref().well_defined_of_each_parameter[0];
    let p = super::atomic_proof_mut(&mut outer.proved_then_facts.last_mut().unwrap().verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(known) = &p.searched_proof else {
        panic!("original selected known universal")
    };
    let k = known.detailed_ref();
    assert_eq!(k.arg_match_proofs.len(), 2);
    let Match::ByStructure {
        pattern,
        goal_arg,
        child_matches,
    } = k.arg_match_proofs[0].detailed_ref()
    else {
        panic!("original Cart structure")
    };
    let (
        Obj::ProductShape(ProductShape::Cart(pattern)),
        Obj::ProductShape(ProductShape::Cart(goal)),
    ) = (pattern, goal_arg)
    else {
        panic!()
    };
    assert_eq!(pattern.args.len(), 2);
    assert_eq!(goal.args.len(), 2);
    assert_eq!(child_matches.len(), 2);
    let req = k.instantiation_requirements.detailed_ref();
    assert_eq!(req.param_type_requirements.len(), 2);
    assert!(req.dom_facts.is_empty() && req.proof_of_dom_facts.is_empty());
    let ForallConclusionLocation::DirectThenFact(location) = &k.cite.location else {
        panic!()
    };
    assert_eq!(location.then_fact_index, 0);
    eprintln!(
        "ORIGINAL48 cite:{} children:{} bindings:{} type_requirements:{}",
        k.cite.fact_id.value(),
        child_matches.len(),
        k.forall_parameters_match_what_args.len(),
        req.param_type_requirements.len()
    );
    for (i, (((a, b), matched), ty)) in pattern
        .args
        .iter()
        .zip(&goal.args)
        .zip(child_matches)
        .zip(&req.param_type_requirements)
        .enumerate()
    {
        let Match::BoundParam {
            param_id,
            pattern,
            goal_arg,
        } = matched.detailed_ref()
        else {
            panic!("original first carrier binding")
        };
        assert_eq!(pattern.ir(), a.ir());
        assert_eq!(goal_arg.ir(), b.ir());
        assert_eq!(*param_id, ty.param_id);
        assert_eq!(ty.arg.ir(), b.ir());
        assert_eq!(k.forall_parameters_match_what_args[i].ir(), b.ir());
        assert_eq!(source_subject(&ty.proof).unwrap(), ty.type_fact);
        assert!(
            matches!(&ty.type_fact,Fact::AtomicFact(AtomicFact::IsSetFact(f))if f.set.ir()==b.ir())
        );
        eprintln!(
            "carrier{i}:{} -> {} param:{} requirement:{}",
            a.display_string(),
            b.display_string(),
            param_id.value(),
            ty.type_fact.display_string()
        );
    }
    for (side, w) in [
        ("source", source_wd),
        (
            "target",
            &p.well_defined_proof
                .detailed_ref()
                .well_defined_of_each_parameter[0],
        ),
    ] {
        print_cart_wd(side, w);
    }
    super::compile_run(&run, &c, "original_cartesian").unwrap();
}
fn print_cart_wd(side: &str, w: &ObjWellDefinedProof) {
    let DetailedObjWellDefinedProof::ByDef {
        obj,
        proof: ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::Cart(p)),
    } = w.detailed_ref()
    else {
        panic!("actual Cart original WD")
    };
    let Obj::ProductShape(ProductShape::Cart(cart)) = obj else {
        panic!()
    };
    assert_eq!(cart.args.len(), p.child_obj_well_defined.len());
    eprintln!(
        "{side} original WD:{} children:{} requirements:{}",
        obj.display_string(),
        p.child_obj_well_defined.len(),
        p.requirement_fact_verified.len()
    );
    for (a, w) in cart.args.iter().zip(&p.child_obj_well_defined) {
        assert_eq!(a.ir(), w.obj().ir());
        eprintln!("{side} child:{}", w.obj().display_string());
    }
    for q in &p.requirement_fact_verified {
        eprintln!(
            "{side} requirement:{}",
            source_subject(q).unwrap().display_string()
        );
    }
}

const SOURCE:&str="# A collection containing every Cartesian product contains this specified product.\nforall sc48_K set:\n    forall sc48_A,sc48_B set:\n        cart(sc48_A,sc48_B) $in sc48_K\n    =>:\n        cart(R,Z) $in sc48_K\n\n";

#[test]
fn known_cartesian_profiles_preserve_original_matching_stages() {
    for (name, source) in PROFILES {
        let (mut run, c) = super::execute(source);
        let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
        let source_wd = outer
            .assumed_dom_facts
            .iter()
            .find_map(|x| {
                if let FactWellDefinedProof::ForallFact(p) = &x.well_defined {
                    Some(p)
                } else {
                    None
                }
            })
            .expect("source universal formation");
        let FactWellDefinedProof::AtomicExceptEquality(source_wd) =
            &source_wd.detailed_ref().then[0]
        else {
            panic!()
        };
        let source_wd = &source_wd.detailed_ref().well_defined_of_each_parameter[0];
        let target =
            super::atomic_proof_mut(&mut outer.proved_then_facts.last_mut().unwrap().verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(known) =
            &target.searched_proof
        else {
            panic!("original universal proof")
        };
        let p = known.detailed_ref();
        let mut stats = [0; 4];
        for arg in &p.arg_match_proofs {
            walk_cart48(arg, &mut stats)
        }
        let req = p.instantiation_requirements.detailed_ref();
        assert_eq!(
            p.forall_parameters_match_what_args.len(),
            req.param_type_requirements.len()
        );
        for q in &req.param_type_requirements {
            assert_eq!(source_subject(&q.proof).unwrap(), q.type_fact);
            if *name == "bounded_carriers" {
                assert!(
                    matches!(&q.type_fact,Fact::AtomicFact(AtomicFact::InFact(f))if f.element.ir()==q.arg.ir() && matches!(f.set,Obj::SetOperator(SetOperator::PowerSet(_))))
                );
            } else {
                assert!(
                    matches!(&q.type_fact,Fact::AtomicFact(AtomicFact::IsSetFact(f))if f.set.ir()==q.arg.ir())
                );
            }
        }
        assert_eq!(req.dom_facts.len(), req.proof_of_dom_facts.len());
        for (a, b) in req.dom_facts.iter().zip(&req.proof_of_dom_facts) {
            assert_eq!(*a, source_subject(b).unwrap());
        }
        if *name == "guarded" {
            assert_eq!(req.dom_facts.len(), 1);
        }
        if matches!(*name, "repeated" | "rebound_equality" | "nested") {
            assert!(stats[1] > 0);
        }
        if *name == "nested" {
            assert_eq!(stats[3], 3);
        }
        let ForallConclusionLocation::DirectThenFact(loc) = &p.cite.location else {
            panic!()
        };
        assert_eq!(
            loc.then_fact_index,
            if *name == "second_conclusion" { 1 } else { 0 }
        );
        eprintln!("ORIGINAL48 {name} bound:{} rebound:{} nonparam:{} structures:{} type_requirements:{} domains:{}",stats[0],stats[1],stats[2],stats[3],req.param_type_requirements.len(),req.dom_facts.len());
        print_cart_wd("source", source_wd);
        print_cart_wd(
            "target",
            &target
                .well_defined_proof
                .detailed_ref()
                .well_defined_of_each_parameter[0],
        );
        let one = super::compile_run(&run, &c, name).unwrap();
        assert_eq!(one, super::compile_run(&run, &c, name).unwrap());
    }
}
fn walk_cart48(
    p:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::ForallConclusionArgMatchProof,
    stats: &mut [usize; 4],
) {
    match p.detailed_ref() {
        Match::BoundParam {
            param_id,
            pattern,
            goal_arg,
        } => {
            stats[0] += 1;
            eprintln!(
                "bound {}:{} -> {}",
                param_id.value(),
                pattern.display_string(),
                goal_arg.display_string()
            );
        }
        Match::ReboundParamEqual {
            previous,
            goal_arg,
            equal,
            ..
        } => {
            stats[1] += 1;
            assert_eq!(previous.ir(), equal.equal_fact.left.ir());
            assert_eq!(goal_arg.ir(), equal.equal_fact.right.ir());
            let route=match &equal.equal_proof{crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::StrictEqualArgProof::ByEquivalenceClass(_)=>"equivalence class",crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::StrictEqualArgProof::ByTheyAreTheSame(_)=>"identity",_=>"other retained strict route"};
            eprintln!(
                "rebound {}={} route:{route}",
                previous.display_string(),
                goal_arg.display_string()
            );
        }
        Match::NonParamEqual {
            pattern_after_subst,
            goal_arg,
            equal,
            ..
        } => {
            stats[2] += 1;
            assert_eq!(pattern_after_subst.ir(), equal.equal_fact.left.ir());
            assert_eq!(goal_arg.ir(), equal.equal_fact.right.ir());
        }
        Match::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } => {
            stats[3] += 1;
            eprintln!(
                "structure {} -> {} children:{}",
                pattern.display_string(),
                goal_arg.display_string(),
                child_matches.len()
            );
            for child in child_matches {
                walk_cart48(child, stats)
            }
        }
    }
}

const PROFILES:&[(&str,&str)]=&[
("binary","# A collection containing every Cartesian product contains this specified product.\nforall sc48_K set:\n    forall sc48_A,sc48_B set:\n        cart(sc48_A,sc48_B) $in sc48_K\n    =>:\n        cart(R,Z) $in sc48_K\n\n"),
("unary","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A set:\n        cart(sc48_A) $in sc48_K\n    =>:\n        cart(R) $in sc48_K\n"),
("ternary","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A,sc48_B,sc48_C set:\n        cart(sc48_A,sc48_B,sc48_C) $in sc48_K\n    =>:\n        cart(R,Z,C) $in sc48_K\n"),
("repeated","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A set:\n        cart(sc48_A,sc48_A) $in sc48_K\n    =>:\n        cart(R,R) $in sc48_K\n"),
("fixed","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A set:\n        cart(R,sc48_A) $in sc48_K\n    =>:\n        cart(R,Z) $in sc48_K\n"),
("generic","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K,sc48_X,sc48_Y set:\n    forall sc48_A,sc48_B set:\n        cart(sc48_A,sc48_B) $in sc48_K\n    =>:\n        cart(sc48_X,sc48_Y) $in sc48_K\n"),
("guarded","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K,sc48_X,sc48_Y set:\n    sc48_X $in power_set(sc48_Y)\n    forall sc48_A,sc48_B set:\n        sc48_A $in power_set(sc48_B)\n        =>:\n            cart(sc48_A,sc48_B) $in sc48_K\n    =>:\n        cart(sc48_X,sc48_Y) $in sc48_K\n"),
("second_conclusion","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K,sc48_L set:\n    forall sc48_A,sc48_B set:\n        cart(sc48_A,sc48_B) $in sc48_K\n        cart(sc48_A,sc48_B) $in sc48_L\n    =>:\n        cart(R,Z) $in sc48_L\n"),
("nested","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A,sc48_B set:\n        cart(cart(sc48_A,sc48_B),cart(sc48_B,sc48_A)) $in sc48_K\n    =>:\n        cart(cart(R,Z),cart(Z,R)) $in sc48_K\n"),
("rebound_equality","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K,sc48_X,sc48_Y set:\n    sc48_X=sc48_Y\n    forall sc48_A set:\n        cart(sc48_A,sc48_A) $in sc48_K\n    =>:\n        cart(sc48_X,sc48_Y) $in sc48_K\n"),
("returned","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set,sc48_f fn(sc48_t R) power_set(R):\n    forall sc48_A,sc48_B set:\n        cart(sc48_A,sc48_B) $in sc48_K\n    =>:\n        sc48_f(0) $in power_set(R)\n        sc48_f(1) $in power_set(R)\n        cart(sc48_f(0),sc48_f(1)) $in sc48_K\n"),
("fixed_simplified","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A set:\n        cart(R,sc48_A) $in sc48_K\n    =>:\n        union(R,{})=R\n        cart(union(R,{}),Z) $in sc48_K\n"),
("rebound_simplified","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A set:\n        cart(sc48_A,sc48_A) $in sc48_K\n    =>:\n        union(R,{})=R\n        cart(R,union(R,{})) $in sc48_K\n"),
("nested_rebound_equality","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K,sc48_X,sc48_Y set:\n    sc48_X=sc48_Y\n    forall sc48_A set:\n        cart(cart(sc48_A,sc48_A),cart(sc48_A,sc48_A)) $in sc48_K\n    =>:\n        cart(cart(sc48_X,sc48_Y),cart(sc48_Y,sc48_X)) $in sc48_K\n"),
("quaternary","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K set:\n    forall sc48_A,sc48_B,sc48_C,sc48_D set:\n        cart(sc48_A,sc48_B,sc48_C,sc48_D) $in sc48_K\n    =>:\n        cart(R,Z,C,N) $in sc48_K\n"),
("bounded_carriers","# A collection containing the given Cartesian products contains this specified instance.\nforall sc48_K,sc48_S set,sc48_X,sc48_Y power_set(sc48_S):\n    forall sc48_A,sc48_B power_set(sc48_S):\n        cart(sc48_A,sc48_B) $in sc48_K\n    =>:\n        cart(sc48_X,sc48_Y) $in sc48_K\n"),
];

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedProveForallInstantiationRequirementsProof, DetailedSearchProofByKnownForallFact,
    ForallConclusionArgMatchProof, StrictEqualArgProof,
};
fn profile48(name: &str) -> &str {
    PROFILES.iter().find(|x| x.0 == name).unwrap().1
}
fn outer48(r: &mut RunLitexCodeResult) -> &mut VerifyForallFactSuccess {
    super::forall_proof_mut(r.statement_results.last_mut().unwrap())
}
fn target48(r: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    for step in outer48(r).proved_then_facts.iter_mut().rev() {
        if let VerifyFactResult::AtomicExceptEquality(p) = &mut step.verify_result {
            if let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() {
                if matches!(&p.fact,AtomicFact::InFact(f)if matches!(f.element,Obj::ProductShape(ProductShape::Cart(_))))
                {
                    return p;
                }
            }
        }
    }
    panic!("original Cartesian membership goal")
}
fn app48(r: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) =
        &mut target48(r).searched_proof
    else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn children48(r: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let Match::ByStructure { child_matches, .. } =
        app48(r).arg_match_proofs[0].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches
}
fn req48(r: &mut RunLitexCodeResult) -> &mut DetailedProveForallInstantiationRequirementsProof {
    app48(r)
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap()
}
fn wd48(r: &mut RunLitexCodeResult) -> &mut ObjWellDefinedProof {
    &mut target48(r)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0]
}
fn cart_wd48(
    w: &mut ObjWellDefinedProof,
) -> &mut crate::execute::execute_fact_stmt::well_defined_results::verify_obj::CartObjWellDefinedProof
{
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::ProductShape(ProductShapeObjWellDefinedProofByDef::Cart(p)),
        ..
    } = w.as_detailed_mut().unwrap()
    else {
        panic!()
    };
    p
}
fn dead48(w: &mut ObjWellDefinedProof) {
    *w = ObjWellDefinedProof::Detailed(Box::new(DetailedObjWellDefinedProof::ByKnown {
        obj: w.obj().clone(),
        wd_id: WellDefinednessId::new(u64::MAX),
    }));
}
fn reject48(r: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, n: &str) {
    super::compile_run(r, c, n).expect_err("corrupted original Cartesian evidence must reject");
}
const SHAPES48: &[&str] = &["unary", "binary", "ternary", "quaternary"];
#[test]
fn known_cartesian_requires_exact_captured_pattern_and_goal() {
    for n in SHAPES48 {
        for p in [false, true] {
            let (mut r, c) = super::execute(profile48(n));
            let Match::ByStructure {
                pattern, goal_arg, ..
            } = app48(&mut r).arg_match_proofs[0].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            if p {
                *pattern = Obj::StandardSet(StandardSet::R)
            } else {
                *goal_arg = Obj::StandardSet(StandardSet::R)
            };
            reject48(&r, &c, n)
        }
    }
}
#[test]
fn known_cartesian_requires_exact_child_arity() {
    for n in SHAPES48 {
        for extra in [false, true] {
            let (mut r, c) = super::execute(profile48(n));
            let (mut d, _) = super::execute(profile48(n));
            let spare = children48(&mut d).pop().unwrap();
            if extra {
                children48(&mut r).push(spare)
            } else {
                children48(&mut r).pop();
            };
            reject48(&r, &c, n)
        }
    }
}
#[test]
fn known_cartesian_preserves_ordered_carrier_matches() {
    for n in ["binary", "ternary", "quaternary"] {
        let (mut r, c) = super::execute(profile48(n));
        children48(&mut r).swap(0, 1);
        reject48(&r, &c, n)
    }
}
#[test]
fn known_cartesian_checks_leaf_arity_and_constructor_before_replay() {
    use std::collections::{HashMap, HashSet};
    for tuple in [false, true] {
        let (mut r, c) = super::execute(profile48("binary"));
        let p = app48(&mut r);
        let subst: HashMap<_, _> = p
            .instantiation_requirements
            .detailed_ref()
            .param_type_requirements
            .iter()
            .zip(&p.forall_parameters_match_what_args)
            .map(|(q, a)| (q.param_id, a.clone()))
            .collect();
        let m = &mut p.arg_match_proofs[0];
        let Match::ByStructure {
            pattern, goal_arg, ..
        } = m.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        let pattern = pattern.clone();
        let Obj::ProductShape(ProductShape::Cart(cart)) = goal_arg else {
            panic!()
        };
        if tuple {
            *goal_arg = Obj::ProductShape(ProductShape::Tuple(Tuple {
                args: cart.args.clone(),
            }))
        } else {
            cart.args.pop();
        }
        let goal = goal_arg.clone();
        let e = c
            .compile_forall_argument_match(&pattern, &goal, m, &subst, &mut HashSet::new(), None)
            .unwrap_err();
        assert_eq!(
            e.route,
            if tuple {
                "CompoundKnown/StructureConstructor"
            } else {
                "CompoundKnown/CartesianArity"
            }
        );
    }
}
#[test]
fn known_cartesian_keeps_original_bound_identity_and_subject() {
    for side in 0..3 {
        let (mut r, c) = super::execute(profile48("binary"));
        let Match::BoundParam {
            param_id,
            pattern,
            goal_arg,
        } = children48(&mut r)[0].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        match side {
            0 => *param_id = IdentifierId::new(u64::MAX),
            1 => *pattern = Obj::StandardSet(StandardSet::N),
            _ => *goal_arg = Obj::StandardSet(StandardSet::N),
        };
        reject48(&r, &c, "bound")
    }
}
#[test]
fn known_cartesian_does_not_replace_original_substitution() {
    let (mut r, c) = super::execute(profile48("generic"));
    app48(&mut r).forall_parameters_match_what_args[0] = Obj::StandardSet(StandardSet::N);
    reject48(&r, &c, "substitution")
}
#[test]
fn known_cartesian_requires_all_parameter_type_records() {
    for n in SHAPES48 {
        let (mut r, c) = super::execute(profile48(n));
        req48(&mut r).param_type_requirements.pop();
        reject48(&r, &c, n)
    }
}
#[test]
fn known_cartesian_preserves_type_record_order() {
    let (mut r, c) = super::execute(profile48("generic"));
    req48(&mut r).param_type_requirements.swap(0, 1);
    reject48(&r, &c, "type_order")
}
#[test]
fn known_cartesian_preserves_type_record_parameter_and_argument() {
    for param in [false, true] {
        let (mut r, c) = super::execute(profile48("generic"));
        let q = &mut req48(&mut r).param_type_requirements[0];
        if param {
            q.param_id = IdentifierId::new(u64::MAX)
        } else {
            q.arg = Obj::StandardSet(StandardSet::N)
        };
        reject48(&r, &c, "type_identity")
    }
}
#[test]
fn known_cartesian_requires_exact_sethood_subject() {
    let (mut r, c) = super::execute(profile48("generic"));
    let q = &mut req48(&mut r).param_type_requirements[0];
    let Fact::AtomicFact(AtomicFact::IsSetFact(f)) = &mut q.type_fact else {
        panic!()
    };
    f.set = Obj::StandardSet(StandardSet::N);
    let AtomicFact::IsSetFact(f) = &mut super::atomic_proof_mut(&mut q.proof).fact else {
        panic!()
    };
    f.set = Obj::StandardSet(StandardSet::N);
    reject48(&r, &c, "sethood_subject")
}
#[test]
fn known_cartesian_requires_parameter_proof_subject_and_original_wd() {
    for wd in [false, true] {
        let (mut r, c) = super::execute(profile48("generic"));
        let q = super::atomic_proof_mut(&mut req48(&mut r).param_type_requirements[0].proof);
        if wd {
            dead48(
                &mut q
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter[0],
            )
        } else {
            let AtomicFact::IsSetFact(f) = &mut q.fact else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::N)
        };
        reject48(&r, &c, "type_proof")
    }
}
#[test]
fn known_cartesian_requires_bounded_carrier_membership() {
    for element in [false, true] {
        let (mut r, c) = super::execute(profile48("bounded_carriers"));
        let q = &mut req48(&mut r).param_type_requirements[0];
        let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut q.type_fact else {
            panic!()
        };
        if element {
            f.element = Obj::StandardSet(StandardSet::N)
        } else {
            f.set = Obj::StandardSet(StandardSet::R)
        };
        reject48(&r, &c, "bounded_carrier")
    }
}
#[test]
fn known_cartesian_requires_all_domain_records() {
    for proof in [false, true] {
        let (mut r, c) = super::execute(profile48("guarded"));
        if proof {
            req48(&mut r).proof_of_dom_facts.clear()
        } else {
            req48(&mut r).dom_facts.clear()
        };
        reject48(&r, &c, "domain_count")
    }
}
#[test]
fn known_cartesian_preserves_domain_subject_and_citation() {
    for cite in [false, true] {
        let (mut r, c) = super::execute(profile48("guarded"));
        if cite {
            let q = super::atomic_proof_mut(&mut req48(&mut r).proof_of_dom_facts[0]);
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(q) = &mut q.searched_proof
            else {
                panic!("original domain citation")
            };
            q.cite_fact_id = FactId::new(u64::MAX)
        } else {
            let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut req48(&mut r).dom_facts[0] else {
                panic!()
            };
            f.element = Obj::StandardSet(StandardSet::N)
        };
        reject48(&r, &c, "domain")
    }
}
#[test]
fn known_cartesian_requires_exact_prior_universal() {
    for missing in [false, true] {
        let (mut r, c) = super::execute(profile48("binary"));
        let target = target48(&mut r).fact.fact_id();
        app48(&mut r).cite.fact_id = if missing {
            FactId::new(u64::MAX)
        } else {
            target
        };
        reject48(&r, &c, "citation")
    }
}
#[test]
fn known_cartesian_preserves_original_conclusion_index() {
    for index in [0, usize::MAX] {
        let (mut r, c) = super::execute(profile48("second_conclusion"));
        let ForallConclusionLocation::DirectThenFact(q) = &mut app48(&mut r).cite.location else {
            panic!()
        };
        q.then_fact_index = index;
        reject48(&r, &c, "conclusion")
    }
}
#[test]
fn known_cartesian_requires_original_rebound_identity_and_previous() {
    for identity in [false, true] {
        let (mut r, c) = super::execute(profile48("rebound_equality"));
        let Match::ReboundParamEqual {
            param_id, previous, ..
        } = children48(&mut r)[1].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        if identity {
            *param_id = IdentifierId::new(u64::MAX)
        } else {
            *previous = Obj::StandardSet(StandardSet::N)
        };
        reject48(&r, &c, "rebound")
    }
}
#[test]
fn known_cartesian_requires_rebound_strict_subjects() {
    for left in [false, true] {
        let (mut r, c) = super::execute(profile48("rebound_equality"));
        let Match::ReboundParamEqual { equal, .. } =
            children48(&mut r)[1].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        if left {
            equal.equal_fact.left = Obj::StandardSet(StandardSet::N)
        } else {
            equal.equal_fact.right = Obj::StandardSet(StandardSet::N)
        };
        reject48(&r, &c, "strict_subject")
    }
}
#[test]
fn known_cartesian_does_not_replace_known_rebound_equality_with_identity() {
    let (mut r, c) = super::execute(profile48("rebound_equality"));
    let (mut d, _) = super::execute(profile48("rebound_equality"));
    let ForallConclusionArgMatchProof::Detailed(p) = app48(&mut d).arg_match_proofs.pop().unwrap()
    else {
        panic!()
    };
    let Match::NonParamEqual { equal: donor, .. } = *p else {
        panic!()
    };
    let Match::ReboundParamEqual { equal, .. } = children48(&mut r)[1].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    assert!(matches!(
        equal.equal_proof,
        StrictEqualArgProof::ByEquivalenceClass(_)
    ));
    equal.equal_proof = donor.equal_proof;
    reject48(&r, &c, "strict_route")
}
#[test]
fn known_cartesian_requires_original_rebound_equality_citation() {
    let (mut r, c) = super::execute(profile48("rebound_equality"));
    let Match::ReboundParamEqual { equal, .. } = children48(&mut r)[1].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    let StrictEqualArgProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
    ) = &mut equal.equal_proof
    else {
        panic!()
    };
    assert_eq!(p.path.len(), 1);
    p.path[0].2 = FactId::new(u64::MAX);
    reject48(&r, &c, "strict_citation")
}
#[test]
fn known_cartesian_preserves_fixed_substitution_and_equality() {
    for subject in [false, true] {
        let (mut r, c) = super::execute(profile48("fixed_simplified"));
        let Match::NonParamEqual {
            pattern_after_subst,
            equal,
            ..
        } = children48(&mut r)[0].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        if subject {
            equal.equal_fact.left = Obj::StandardSet(StandardSet::N)
        } else {
            *pattern_after_subst = Obj::StandardSet(StandardSet::N)
        };
        reject48(&r, &c, "fixed")
    }
}
#[test]
fn known_cartesian_requires_actual_parent_and_child_wd() {
    for parent in [false, true] {
        let (mut r, c) = super::execute(profile48("binary"));
        if parent {
            dead48(wd48(&mut r))
        } else {
            dead48(&mut cart_wd48(wd48(&mut r)).child_obj_well_defined[0])
        };
        reject48(&r, &c, "actual_wd")
    }
}
#[test]
fn known_cartesian_preserves_ordered_wd_and_forbids_added_constructor_requirements() {
    for extra in [false, true] {
        let (mut r, c) = super::execute(profile48("binary"));
        if extra {
            let (mut d, _) = super::execute(profile48("binary"));
            let q = req48(&mut d).param_type_requirements.pop().unwrap().proof;
            cart_wd48(wd48(&mut r)).requirement_fact_verified.push(q)
        } else {
            cart_wd48(wd48(&mut r)).child_obj_well_defined.swap(0, 1)
        };
        reject48(&r, &c, "wd_stages")
    }
}
#[test]
fn known_cartesian_keeps_returned_call_producers_before_target() {
    let (mut r, c) = super::execute(profile48("returned"));
    outer48(&mut r).proved_then_facts.rotate_left(1);
    reject48(&r, &c, "producer_order")
}
