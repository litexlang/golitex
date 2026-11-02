use crate::compile_to_lean::helper::{real_interval_parts, real_ray_parts, source_subject};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof as Match, SearchProofByKnownForallFact,
    StrictEqualArgProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    DetailedObjWellDefinedProof, ObjWellDefinedProof, ObjWellDefinedProofByDef,
    SetFormerObjWellDefinedProofByDef,
};
use crate::prelude::*;
#[test]
fn known_interval_original_ten_structural_match_trees() {
    for (name, source) in SOURCES {
        let (mut run, c) = super::execute(source);
        let proof = application(&mut run).detailed_ref();
        let n = if name.starts_with("lower_") || name.starts_with("upper_") {
            1
        } else {
            2
        };
        assert_eq!(proof.arg_match_proofs.len(), 2);
        assert_eq!(proof.forall_parameters_match_what_args.len(), n);
        let req = proof.instantiation_requirements.detailed_ref();
        assert_eq!(req.param_type_requirements.len(), n);
        assert!(req.dom_facts.is_empty() && req.proof_of_dom_facts.is_empty());
        let Match::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } = proof.arg_match_proofs[0].detailed_ref()
        else {
            panic!("original interval structure")
        };
        let ps = endpoints(pattern);
        let gs = endpoints(goal_arg);
        assert_eq!(ps.len(), n);
        assert_eq!(gs.len(), n);
        assert_eq!(child_matches.len(), n);
        eprintln!(
            "ORIGINAL47 {name} citation:{} {} -> {}",
            proof.cite.fact_id.value(),
            pattern.display_string(),
            goal_arg.display_string()
        );
        for (i, (((p, g), child), ty)) in ps
            .iter()
            .zip(&gs)
            .zip(child_matches)
            .zip(&req.param_type_requirements)
            .enumerate()
        {
            let Match::BoundParam {
                param_id,
                pattern,
                goal_arg,
            } = child.detailed_ref()
            else {
                panic!("original first endpoint binding")
            };
            assert_eq!(pattern.ir(), p.ir());
            assert_eq!(goal_arg.ir(), g.ir());
            assert_eq!(*param_id, ty.param_id);
            assert_eq!(ty.arg.ir(), g.ir());
            assert_eq!(proof.forall_parameters_match_what_args[i].ir(), g.ir());
            assert_eq!(source_subject(&ty.proof).unwrap(), ty.type_fact);
            assert!(
                matches!(&ty.type_fact,Fact::AtomicFact(AtomicFact::InFact(f))if f.element.ir()==g.ir()&&f.set==Obj::StandardSet(if matches!(*name,"range"|"closed_range"){StandardSet::Z}else{StandardSet::R}))
            );
            eprintln!(
                "endpoint{i}:{} -> {} param:{} type:{}",
                p.display_string(),
                g.display_string(),
                param_id.value(),
                ty.type_fact.display_string()
            );
        }
        let Match::NonParamEqual {
            pattern,
            pattern_after_subst,
            goal_arg,
            equal,
        } = proof.arg_match_proofs[1].detailed_ref()
        else {
            panic!("original outer collection identity")
        };
        assert_eq!(pattern.ir(), pattern_after_subst.ir());
        assert_eq!(pattern_after_subst.ir(), goal_arg.ir());
        assert_eq!(equal.equal_fact.left.ir(), pattern_after_subst.ir());
        assert_eq!(equal.equal_fact.right.ir(), goal_arg.ir());
        assert!(matches!(
            equal.equal_proof,
            StrictEqualArgProof::ByTheyAreTheSame(_)
        ));
        let target = &last_atomic(&mut run)
            .well_defined_proof
            .detailed_ref()
            .well_defined_of_each_parameter[0];
        let (children, req) = wd_stages(target);
        assert_eq!(children.len(), n);
        assert_eq!(req.len(), n);
        for (i, (child, req)) in children.iter().zip(req).enumerate() {
            eprintln!(
                "target WD{i}:{} requirement:{}",
                child.obj().display_string(),
                source_subject(req).unwrap().display_string()
            );
        }
        super::compile_run(&run, &c, name).unwrap();
    }
}
fn endpoints(obj: &Obj) -> Vec<&Obj> {
    match obj {
        Obj::SetFormer(SetFormer::Range(p)) => vec![&p.start, &p.end],
        Obj::SetFormer(SetFormer::ClosedRange(p)) => vec![&p.start, &p.end],
        Obj::SetFormer(SetFormer::IntervalObj(p)) => {
            let (a, b, _, _) = real_interval_parts(p);
            vec![a, b]
        }
        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) => vec![real_ray_parts(p).0],
        _ => panic!(),
    }
}
fn wd_stages(wd: &ObjWellDefinedProof) -> (&Vec<Box<ObjWellDefinedProof>>, &Vec<VerifyFactResult>) {
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetFormer(p),
        ..
    } = wd.detailed_ref()
    else {
        panic!()
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
fn last_verify(run: &mut RunLitexCodeResult) -> &mut VerifyFactResult {
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
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) =
        run.statement_results.last_mut().unwrap()
    else {
        panic!()
    };
    last(&mut s.verify_result)
}
fn last_atomic(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    super::atomic_proof_mut(last_verify(run))
}
fn application(run: &mut RunLitexCodeResult) -> &mut SearchProofByKnownForallFact {
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) =
        &mut last_atomic(run).searched_proof
    else {
        panic!("original cited universal")
    };
    p
}

const SOURCES:&[(&str,&str)]=&[
("range","forall eq47_K set:\n    forall eq47_a,eq47_b Z:\n        range(eq47_a,eq47_b) $in eq47_K\n    =>:\n        range(0,2) $in eq47_K\n"),
("closed_range","forall eq47_K set:\n    forall eq47_a,eq47_b Z:\n        closed_range(eq47_a,eq47_b) $in eq47_K\n    =>:\n        closed_range(0,2) $in eq47_K\n"),
("open_open","forall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '(eq47_a,eq47_b) $in eq47_K\n    =>:\n        '(0,2) $in eq47_K\n"),
("open_closed","forall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '(eq47_a,eq47_b] $in eq47_K\n    =>:\n        '(0,2] $in eq47_K\n"),
("closed_open","forall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '[eq47_a,eq47_b) $in eq47_K\n    =>:\n        '[0,2) $in eq47_K\n"),
("closed_closed","forall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '[eq47_a,eq47_b] $in eq47_K\n    =>:\n        '[0,2] $in eq47_K\n"),
("lower_open","forall eq47_K set:\n    forall eq47_a R:\n        '(eq47_a,) $in eq47_K\n    =>:\n        '(0,) $in eq47_K\n"),
("lower_closed","forall eq47_K set:\n    forall eq47_a R:\n        '[eq47_a,) $in eq47_K\n    =>:\n        '[0,) $in eq47_K\n"),
("upper_open","forall eq47_K set:\n    forall eq47_a R:\n        '(,eq47_a) $in eq47_K\n    =>:\n        '(,0) $in eq47_K\n"),
("upper_closed","forall eq47_K set:\n    forall eq47_a R:\n        '(,eq47_a] $in eq47_K\n    =>:\n        '(,0] $in eq47_K\n"),
];

#[test]
fn known_interval_original_bound_rebound_fixed_nested_and_guarded_trees() {
    for name in [
        "range_rebound_calc",
        "range_fixed_left",
        "range_nested",
        "lower_open_fixed_nested",
        "lower_open_rebound_nested",
        "range_guarded",
        "range_second_conclusion",
        "upper_closed_second_conclusion",
    ] {
        let (mut run, c) = super::execute(profile(name));
        let p = application(&mut run).detailed_ref();
        let mut stats = [0; 4];
        for m in &p.arg_match_proofs {
            walk(m, &mut stats)
        }
        eprintln!("ORIGINAL47 {name} bound:{} rebound:{} nonparam:{} structures:{} type_requirements:{} doms:{}",stats[0],stats[1],stats[2],stats[3],p.instantiation_requirements.detailed_ref().param_type_requirements.len(),p.instantiation_requirements.detailed_ref().dom_facts.len());
        if name.contains("rebound") || name == "range_nested" {
            assert!(stats[1] > 0);
        }
        if name == "range_fixed_left" || name == "lower_open_fixed_nested" {
            assert!(stats[2] >= 2);
        }
        if name == "range_guarded" {
            let req = p.instantiation_requirements.detailed_ref();
            assert_eq!(req.dom_facts.len(), 1);
            assert_eq!(req.proof_of_dom_facts.len(), 1);
            assert_eq!(
                source_subject(&req.proof_of_dom_facts[0]).unwrap(),
                req.dom_facts[0]
            );
        }
        if name.ends_with("second_conclusion") {
            let ForallConclusionLocation::DirectThenFact(q) = &p.cite.location else {
                panic!()
            };
            assert_eq!(q.then_fact_index, 1);
        }
        super::compile_run(&run, &c, name).unwrap();
    }
}
fn walk(
    p:&crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::ForallConclusionArgMatchProof,
    stats: &mut [usize; 4],
) {
    match p.detailed_ref() {
        Match::BoundParam { .. } => stats[0] += 1,
        Match::ReboundParamEqual {
            previous,
            goal_arg,
            equal,
            ..
        } => {
            stats[1] += 1;
            assert_eq!(previous.ir(), equal.equal_fact.left.ir());
            assert_eq!(goal_arg.ir(), equal.equal_fact.right.ir());
            eprintln!(
                "strict rebound:{}={} route:{}",
                previous.display_string(),
                goal_arg.display_string(),
                strict_name(&equal.equal_proof)
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
            eprintln!(
                "strict fixed:{}={} route:{}",
                pattern_after_subst.display_string(),
                goal_arg.display_string(),
                strict_name(&equal.equal_proof)
            );
        }
        Match::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } => {
            stats[3] += 1;
            eprintln!(
                "structure:{} -> {} children:{}",
                pattern.display_string(),
                goal_arg.display_string(),
                child_matches.len()
            );
            for c in child_matches {
                walk(c, stats)
            }
        }
    }
}
fn strict_name(p: &StrictEqualArgProof) -> &'static str {
    match p {
        StrictEqualArgProof::ByClosedCalculation(_) => "closed calculation",
        StrictEqualArgProof::ByTheyAreTheSame(_) => "same",
        StrictEqualArgProof::ByBuiltinRule(_) => "builtin",
        StrictEqualArgProof::ByEquivalenceClass(_) => "equivalence",
        StrictEqualArgProof::ByKnownSpecialProperty(_) => "special",
        StrictEqualArgProof::ByObjectDefinition(_) => "definition",
        StrictEqualArgProof::ByBuiltinStrategy(_) => "strategy",
        StrictEqualArgProof::ByMatchingOneArgByOne(_) => "matching",
    }
}
fn profile(n: &str) -> &str {
    PROFILES.iter().find(|p| p.0 == n).unwrap().1
}

const PROFILES:&[(&str,&str)]=&[
("range","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a,eq47_b Z:\n        range(eq47_a,eq47_b) $in eq47_K\n    =>:\n        range(0,2) $in eq47_K\n"),
("closed_range","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a,eq47_b Z:\n        closed_range(eq47_a,eq47_b) $in eq47_K\n    =>:\n        closed_range(0,2) $in eq47_K\n"),
("open_open","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '(eq47_a,eq47_b) $in eq47_K\n    =>:\n        '(0,2) $in eq47_K\n"),
("open_closed","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '(eq47_a,eq47_b] $in eq47_K\n    =>:\n        '(0,2] $in eq47_K\n"),
("closed_open","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '[eq47_a,eq47_b) $in eq47_K\n    =>:\n        '[0,2) $in eq47_K\n"),
("closed_closed","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a,eq47_b R:\n        '[eq47_a,eq47_b] $in eq47_K\n    =>:\n        '[0,2] $in eq47_K\n"),
("lower_open","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a R:\n        '(eq47_a,) $in eq47_K\n    =>:\n        '(0,) $in eq47_K\n"),
("lower_closed","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a R:\n        '[eq47_a,) $in eq47_K\n    =>:\n        '[0,) $in eq47_K\n"),
("upper_open","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a R:\n        '(,eq47_a) $in eq47_K\n    =>:\n        '(,0) $in eq47_K\n"),
("upper_closed","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall eq47_K set:\n    forall eq47_a R:\n        '(,eq47_a] $in eq47_K\n    =>:\n        '(,0] $in eq47_K\n"),
("range_rebound_calc","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a Z:\n        range(sc47_a,sc47_a) $in sc47_K\n    =>:\n        range(0,1-1) $in sc47_K\n"),
("range_fixed_left","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_b Z:\n        range(0,sc47_b) $in sc47_K\n    =>:\n        range(2-2,2) $in sc47_K\n"),
("range_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x,sc47_y Z:\n    forall sc47_a,sc47_b Z:\n        range(sc47_a,sc47_b) $in sc47_K\n    =>:\n        range(sc47_x,sc47_y) $in sc47_K\n"),
("range_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) Z:\n    forall sc47_a,sc47_b Z:\n        range(sc47_a,sc47_b) $in sc47_K\n    =>:\n        sc47_f(0) $in Z\n        sc47_f(1) $in Z\n        range(sc47_f(0),sc47_f(1)) $in sc47_K\n"),
("range_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b Z:\n        union(range(sc47_a,sc47_b),range(sc47_a,sc47_b)) $in sc47_K\n    =>:\n        union(range(0,2),range(2-2,1+1)) $in sc47_K\n"),
("range_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b Z:\n        sc47_a<sc47_b\n        =>:\n            range(sc47_a,sc47_b) $in sc47_K\n    =>:\n        range(0,2) $in sc47_K\n"),
("closed_range_rebound_calc","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a Z:\n        closed_range(sc47_a,sc47_a) $in sc47_K\n    =>:\n        closed_range(0,1-1) $in sc47_K\n"),
("closed_range_fixed_left","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_b Z:\n        closed_range(0,sc47_b) $in sc47_K\n    =>:\n        closed_range(2-2,2) $in sc47_K\n"),
("closed_range_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x,sc47_y Z:\n    forall sc47_a,sc47_b Z:\n        closed_range(sc47_a,sc47_b) $in sc47_K\n    =>:\n        closed_range(sc47_x,sc47_y) $in sc47_K\n"),
("closed_range_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) Z:\n    forall sc47_a,sc47_b Z:\n        closed_range(sc47_a,sc47_b) $in sc47_K\n    =>:\n        sc47_f(0) $in Z\n        sc47_f(1) $in Z\n        closed_range(sc47_f(0),sc47_f(1)) $in sc47_K\n"),
("closed_range_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b Z:\n        union(closed_range(sc47_a,sc47_b),closed_range(sc47_a,sc47_b)) $in sc47_K\n    =>:\n        union(closed_range(0,2),closed_range(2-2,1+1)) $in sc47_K\n"),
("closed_range_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b Z:\n        sc47_a<sc47_b\n        =>:\n            closed_range(sc47_a,sc47_b) $in sc47_K\n    =>:\n        closed_range(0,2) $in sc47_K\n"),
("open_open_rebound_calc","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        '(sc47_a,sc47_a) $in sc47_K\n    =>:\n        '(0,1-1) $in sc47_K\n"),
("open_open_fixed_left","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_b R:\n        '(0,sc47_b) $in sc47_K\n    =>:\n        '(2-2,2) $in sc47_K\n"),
("open_open_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x,sc47_y R:\n    forall sc47_a,sc47_b R:\n        '(sc47_a,sc47_b) $in sc47_K\n    =>:\n        '(sc47_x,sc47_y) $in sc47_K\n"),
("open_open_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a,sc47_b R:\n        '(sc47_a,sc47_b) $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        sc47_f(1) $in R\n        '(sc47_f(0),sc47_f(1)) $in sc47_K\n"),
("open_open_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        union('(sc47_a,sc47_b),'(sc47_a,sc47_b)) $in sc47_K\n    =>:\n        union('(0,2),'(2-2,1+1)) $in sc47_K\n"),
("open_open_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        sc47_a<sc47_b\n        =>:\n            '(sc47_a,sc47_b) $in sc47_K\n    =>:\n        '(0,2) $in sc47_K\n"),
("open_closed_rebound_calc","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        '(sc47_a,sc47_a] $in sc47_K\n    =>:\n        '(0,1-1] $in sc47_K\n"),
("open_closed_fixed_left","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_b R:\n        '(0,sc47_b] $in sc47_K\n    =>:\n        '(2-2,2] $in sc47_K\n"),
("open_closed_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x,sc47_y R:\n    forall sc47_a,sc47_b R:\n        '(sc47_a,sc47_b] $in sc47_K\n    =>:\n        '(sc47_x,sc47_y] $in sc47_K\n"),
("open_closed_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a,sc47_b R:\n        '(sc47_a,sc47_b] $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        sc47_f(1) $in R\n        '(sc47_f(0),sc47_f(1)] $in sc47_K\n"),
("open_closed_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        union('(sc47_a,sc47_b],'(sc47_a,sc47_b]) $in sc47_K\n    =>:\n        union('(0,2],'(2-2,1+1]) $in sc47_K\n"),
("open_closed_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        sc47_a<sc47_b\n        =>:\n            '(sc47_a,sc47_b] $in sc47_K\n    =>:\n        '(0,2] $in sc47_K\n"),
("closed_open_rebound_calc","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        '[sc47_a,sc47_a) $in sc47_K\n    =>:\n        '[0,1-1) $in sc47_K\n"),
("closed_open_fixed_left","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_b R:\n        '[0,sc47_b) $in sc47_K\n    =>:\n        '[2-2,2) $in sc47_K\n"),
("closed_open_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x,sc47_y R:\n    forall sc47_a,sc47_b R:\n        '[sc47_a,sc47_b) $in sc47_K\n    =>:\n        '[sc47_x,sc47_y) $in sc47_K\n"),
("closed_open_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a,sc47_b R:\n        '[sc47_a,sc47_b) $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        sc47_f(1) $in R\n        '[sc47_f(0),sc47_f(1)) $in sc47_K\n"),
("closed_open_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        union('[sc47_a,sc47_b),'[sc47_a,sc47_b)) $in sc47_K\n    =>:\n        union('[0,2),'[2-2,1+1)) $in sc47_K\n"),
("closed_open_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        sc47_a<sc47_b\n        =>:\n            '[sc47_a,sc47_b) $in sc47_K\n    =>:\n        '[0,2) $in sc47_K\n"),
("closed_closed_rebound_calc","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        '[sc47_a,sc47_a] $in sc47_K\n    =>:\n        '[0,1-1] $in sc47_K\n"),
("closed_closed_fixed_left","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_b R:\n        '[0,sc47_b] $in sc47_K\n    =>:\n        '[2-2,2] $in sc47_K\n"),
("closed_closed_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x,sc47_y R:\n    forall sc47_a,sc47_b R:\n        '[sc47_a,sc47_b] $in sc47_K\n    =>:\n        '[sc47_x,sc47_y] $in sc47_K\n"),
("closed_closed_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a,sc47_b R:\n        '[sc47_a,sc47_b] $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        sc47_f(1) $in R\n        '[sc47_f(0),sc47_f(1)] $in sc47_K\n"),
("closed_closed_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        union('[sc47_a,sc47_b],'[sc47_a,sc47_b]) $in sc47_K\n    =>:\n        union('[0,2],'[2-2,1+1]) $in sc47_K\n"),
("closed_closed_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a,sc47_b R:\n        sc47_a<sc47_b\n        =>:\n            '[sc47_a,sc47_b] $in sc47_K\n    =>:\n        '[0,2] $in sc47_K\n"),
("lower_open_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x R:\n    forall sc47_a R:\n        '(sc47_a,) $in sc47_K\n    =>:\n        '(sc47_x,) $in sc47_K\n"),
("lower_open_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a R:\n        '(sc47_a,) $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        '(sc47_f(0),) $in sc47_K\n"),
("lower_open_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        0<=sc47_a\n        =>:\n            '(sc47_a,) $in sc47_K\n    =>:\n        '(0,) $in sc47_K\n"),
("lower_open_fixed_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('(sc47_a,),'(0,)) $in sc47_K\n    =>:\n        union('(0,),'(1-1,)) $in sc47_K\n"),
("lower_open_rebound_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('(sc47_a,),'(sc47_a,)) $in sc47_K\n    =>:\n        union('(0,),'(1-1,)) $in sc47_K\n"),
("lower_closed_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x R:\n    forall sc47_a R:\n        '[sc47_a,) $in sc47_K\n    =>:\n        '[sc47_x,) $in sc47_K\n"),
("lower_closed_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a R:\n        '[sc47_a,) $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        '[sc47_f(0),) $in sc47_K\n"),
("lower_closed_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        0<=sc47_a\n        =>:\n            '[sc47_a,) $in sc47_K\n    =>:\n        '[0,) $in sc47_K\n"),
("lower_closed_fixed_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('[sc47_a,),'[0,)) $in sc47_K\n    =>:\n        union('[0,),'[1-1,)) $in sc47_K\n"),
("lower_closed_rebound_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('[sc47_a,),'[sc47_a,)) $in sc47_K\n    =>:\n        union('[0,),'[1-1,)) $in sc47_K\n"),
("upper_open_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x R:\n    forall sc47_a R:\n        '(,sc47_a) $in sc47_K\n    =>:\n        '(,sc47_x) $in sc47_K\n"),
("upper_open_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a R:\n        '(,sc47_a) $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        '(,sc47_f(0)) $in sc47_K\n"),
("upper_open_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        0<=sc47_a\n        =>:\n            '(,sc47_a) $in sc47_K\n    =>:\n        '(,0) $in sc47_K\n"),
("upper_open_fixed_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('(,sc47_a),'(,0)) $in sc47_K\n    =>:\n        union('(,0),'(,1-1)) $in sc47_K\n"),
("upper_open_rebound_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('(,sc47_a),'(,sc47_a)) $in sc47_K\n    =>:\n        union('(,0),'(,1-1)) $in sc47_K\n"),
("upper_closed_generic","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_x R:\n    forall sc47_a R:\n        '(,sc47_a] $in sc47_K\n    =>:\n        '(,sc47_x] $in sc47_K\n"),
("upper_closed_returned","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set,sc47_f fn(sc47_t R) R:\n    forall sc47_a R:\n        '(,sc47_a] $in sc47_K\n    =>:\n        sc47_f(0) $in R\n        '(,sc47_f(0)] $in sc47_K\n"),
("upper_closed_guarded","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        0<=sc47_a\n        =>:\n            '(,sc47_a] $in sc47_K\n    =>:\n        '(,0] $in sc47_K\n"),
("upper_closed_fixed_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('(,sc47_a],'(,0]) $in sc47_K\n    =>:\n        union('(,0],'(,1-1]) $in sc47_K\n"),
("upper_closed_rebound_nested","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K set:\n    forall sc47_a R:\n        union('(,sc47_a],'(,sc47_a]) $in sc47_K\n    =>:\n        union('(,0],'(,1-1]) $in sc47_K\n"),
("range_second_conclusion","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K,sc47_L set:\n    forall sc47_a,sc47_b Z:\n        range(sc47_a,sc47_b) $in sc47_K\n        range(sc47_a,sc47_b) $in sc47_L\n    =>:\n        range(0,2) $in sc47_L\n"),
("upper_closed_second_conclusion","# A collection containing all ranges or intervals of this kind contains the specified instance.\nforall sc47_K,sc47_L set:\n    forall sc47_a R:\n        '(,sc47_a] $in sc47_K\n        '(,sc47_a] $in sc47_L\n    =>:\n        '(,0] $in sc47_L\n"),
("range_generic_guarded","# A collection containing all guarded ranges or rays contains the specified guarded instance.\nforall sc47_K set,sc47_x,sc47_y Z:\n    sc47_x<sc47_y\n    forall sc47_a,sc47_b Z:\n        sc47_a<sc47_b\n        =>:\n            range(sc47_a,sc47_b) $in sc47_K\n    =>:\n        range(sc47_x,sc47_y) $in sc47_K\n"),
("upper_closed_generic_guarded","# A collection containing all guarded ranges or rays contains the specified guarded instance.\nforall sc47_K set,sc47_x R:\n    0<=sc47_x\n    forall sc47_a R:\n        0<=sc47_a\n        =>:\n            '(,sc47_a] $in sc47_K\n    =>:\n        '(,sc47_x] $in sc47_K\n"),
];

#[test]
fn known_interval_replays_all_actual_profiles() {
    for (name, source) in PROFILES {
        let (run, c) = super::execute(source);
        let one = super::compile_run(&run, &c, name).unwrap();
        assert_eq!(one, super::compile_run(&run, &c, name).unwrap());
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedProveForallInstantiationRequirementsProof, DetailedSearchProofByKnownForallFact,
    ForallConclusionArgMatchProof,
};
fn capture(r: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    application(r).as_detailed_mut().unwrap()
}
fn structure(r: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let Match::ByStructure { child_matches, .. } =
        capture(r).arg_match_proofs[0].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches
}
fn requirements(
    r: &mut RunLitexCodeResult,
) -> &mut DetailedProveForallInstantiationRequirementsProof {
    capture(r)
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap()
}
fn target_wd(r: &mut RunLitexCodeResult) -> &mut ObjWellDefinedProof {
    &mut last_atomic(r)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0]
}
fn wd_stages_mut(
    w: &mut ObjWellDefinedProof,
) -> (
    &mut Vec<Box<ObjWellDefinedProof>>,
    &mut Vec<VerifyFactResult>,
) {
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetFormer(p),
        ..
    } = w.as_detailed_mut().unwrap()
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
fn reject47(r: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, n: &str) {
    let e = super::compile_run(r, c, n).expect_err("corrupt original proof must fail closed");
    assert!(!e.route.is_empty());
}
fn generic(n: &str) -> String {
    format!("{n}_generic")
}
fn dead_wd(w: &mut ObjWellDefinedProof) {
    *w = ObjWellDefinedProof::Detailed(Box::new(DetailedObjWellDefinedProof::ByKnown {
        obj: w.obj().clone(),
        wd_id: WellDefinednessId::new(u64::MAX),
    }));
}
#[test]
fn known_interval_requires_captured_structure_subjects() {
    for (n, s) in SOURCES {
        for p in [false, true] {
            let (mut r, c) = super::execute(s);
            let Match::ByStructure {
                pattern, goal_arg, ..
            } = capture(&mut r).arg_match_proofs[0]
                .as_detailed_mut()
                .unwrap()
            else {
                panic!()
            };
            if p {
                *pattern = Obj::StandardSet(StandardSet::C)
            } else {
                *goal_arg = Obj::StandardSet(StandardSet::C)
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_requires_exact_child_count() {
    for (n, s) in SOURCES {
        for extra in [false, true] {
            let (mut r, c) = super::execute(s);
            let (mut d, _) = super::execute(s);
            let donor = structure(&mut d).pop().unwrap();
            if extra {
                structure(&mut r).push(donor)
            } else {
                structure(&mut r).pop();
            }
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_preserves_ordered_endpoint_matches() {
    for (n, s) in SOURCES.iter().take(6) {
        let (mut r, c) = super::execute(s);
        structure(&mut r).swap(0, 1);
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_preserves_original_bound_identity_and_subjects() {
    for (n, s) in SOURCES {
        for side in 0..3 {
            let (mut r, c) = super::execute(s);
            let Match::BoundParam {
                param_id,
                pattern,
                goal_arg,
            } = structure(&mut r)[0].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            match side {
                0 => *param_id = IdentifierId::new(u64::MAX),
                1 => *pattern = super::number_object("7"),
                _ => *goal_arg = super::number_object("7"),
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_requires_original_substitution() {
    for (n, s) in SOURCES {
        let (mut r, c) = super::execute(s);
        capture(&mut r).forall_parameters_match_what_args[0] = super::number_object("7");
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_every_original_type_requirement() {
    for (n, _) in SOURCES {
        let (mut r, c) = super::execute(profile(&generic(n)));
        requirements(&mut r).param_type_requirements.pop();
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_preserves_type_requirement_order() {
    for (n, _) in SOURCES.iter().take(6) {
        let (mut r, c) = super::execute(profile(&generic(n)));
        requirements(&mut r).param_type_requirements.swap(0, 1);
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_preserves_type_requirement_parameter_and_argument() {
    for (n, _) in SOURCES {
        for p in [false, true] {
            let (mut r, c) = super::execute(profile(&generic(n)));
            let q = &mut requirements(&mut r).param_type_requirements[0];
            if p {
                q.param_id = IdentifierId::new(u64::MAX)
            } else {
                q.arg = super::number_object("7")
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_preserves_integer_or_real_requirement_carrier() {
    for (n, _) in SOURCES {
        let (mut r, c) = super::execute(profile(&generic(n)));
        let q = &mut requirements(&mut r).param_type_requirements[0];
        let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut q.type_fact else {
            panic!()
        };
        f.set = Obj::StandardSet(StandardSet::C);
        let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(&mut q.proof).fact else {
            panic!()
        };
        f.set = Obj::StandardSet(StandardSet::C);
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_type_proof_subject() {
    for (n, _) in SOURCES {
        let (mut r, c) = super::execute(profile(&generic(n)));
        let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(
            &mut requirements(&mut r).param_type_requirements[0].proof,
        )
        .fact
        else {
            panic!()
        };
        f.element = super::number_object("7");
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_actual_generic_membership_citation() {
    for (n, _) in SOURCES {
        let (mut r, c) = super::execute(profile(&generic(n)));
        let p = super::atomic_proof_mut(&mut requirements(&mut r).param_type_requirements[0].proof);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &mut p.searched_proof
        else {
            panic!("actual generic membership citation")
        };
        p.cite_fact_id = FactId::new(u64::MAX);
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_all_original_domain_records() {
    for n in ["range_generic_guarded", "upper_closed_generic_guarded"] {
        for p in [false, true] {
            let (mut r, c) = super::execute(profile(n));
            if p {
                requirements(&mut r).dom_facts.clear()
            } else {
                requirements(&mut r).proof_of_dom_facts.clear()
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_preserves_original_domain_subject() {
    for n in ["range_generic_guarded", "upper_closed_generic_guarded"] {
        let (mut r, c) = super::execute(profile(n));
        match &mut requirements(&mut r).dom_facts[0] {
            Fact::AtomicFact(AtomicFact::LessFact(p)) => p.left = super::number_object("7"),
            Fact::AtomicFact(AtomicFact::LessEqualFact(p)) => p.right = super::number_object("7"),
            _ => panic!(),
        };
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_original_generic_domain_citation() {
    for n in ["range_generic_guarded", "upper_closed_generic_guarded"] {
        let (mut r, c) = super::execute(profile(n));
        let p = super::atomic_proof_mut(&mut requirements(&mut r).proof_of_dom_facts[0]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &mut p.searched_proof
        else {
            panic!("actual original domain citation")
        };
        p.cite_fact_id = FactId::new(u64::MAX);
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_exact_prior_universal_citation() {
    for (n, s) in SOURCES {
        for missing in [false, true] {
            let (mut r, c) = super::execute(s);
            let target = last_atomic(&mut r).fact.fact_id();
            capture(&mut r).cite.fact_id = if missing {
                FactId::new(u64::MAX)
            } else {
                target
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_preserves_selected_conclusion_location() {
    for n in ["range_second_conclusion", "upper_closed_second_conclusion"] {
        for index in [0, usize::MAX] {
            let (mut r, c) = super::execute(profile(n));
            let ForallConclusionLocation::DirectThenFact(q) = &mut capture(&mut r).cite.location
            else {
                panic!()
            };
            q.then_fact_index = index;
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_cannot_borrow_a_closed_sibling_universal() {
    let private="forall sc47_private R:\n    forall sc47_A,sc47_B Z:\n        range(sc47_A,sc47_B) $in R\n    =>:\n        sc47_private=sc47_private\n";
    let (mut r, c) = super::execute(&format!("{private}\n{}", profile("range")));
    super::compile_run(&r, &c, "sibling_baseline").unwrap();
    let first = super::forall_proof_mut(&mut r.statement_results[0]);
    let StoreFactResult::ForallFact(q) = &first.assumed_dom_facts[0].store_and_infer.store else {
        panic!()
    };
    let id = q.fact_id;
    capture(&mut r).cite.fact_id = id;
    reject47(&r, &c, "sibling")
}
#[test]
fn known_interval_requires_rebound_identity_and_previous_binding() {
    for n in ["range_rebound_calc", "open_closed_rebound_calc"] {
        for p in [false, true] {
            let (mut r, c) = super::execute(profile(n));
            let Match::ReboundParamEqual {
                param_id, previous, ..
            } = structure(&mut r)[1].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            if p {
                *param_id = IdentifierId::new(u64::MAX)
            } else {
                *previous = super::number_object("7")
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_requires_exact_rebound_strict_subjects() {
    for n in ["range_rebound_calc", "closed_closed_rebound_calc"] {
        for p in [false, true] {
            let (mut r, c) = super::execute(profile(n));
            let Match::ReboundParamEqual { equal, .. } =
                structure(&mut r)[1].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            if p {
                equal.equal_fact.left = super::number_object("7")
            } else {
                equal.equal_fact.right = super::number_object("7")
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_replays_actual_strict_calculation_instead_of_identity() {
    for n in [
        "range_rebound_calc",
        "open_open_rebound_calc",
        "range_fixed_left",
    ] {
        let (mut r, c) = super::execute(profile(n));
        let (mut d, _) = super::execute(profile(n));
        let ForallConclusionArgMatchProof::Detailed(donor) =
            capture(&mut d).arg_match_proofs.pop().unwrap()
        else {
            panic!()
        };
        let Match::NonParamEqual { equal: donor, .. } = *donor else {
            panic!()
        };
        let old = donor.equal_proof;
        let child = if n.ends_with("fixed_left") { 0 } else { 1 };
        let equal = match structure(&mut r)[child].as_detailed_mut().unwrap() {
            Match::NonParamEqual { equal, .. } | Match::ReboundParamEqual { equal, .. } => equal,
            _ => panic!(),
        };
        assert!(matches!(
            equal.equal_proof,
            StrictEqualArgProof::ByClosedCalculation(_)
        ));
        equal.equal_proof = old;
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_fixed_pattern_substitution_and_strict_subject() {
    for n in ["range_fixed_left", "closed_open_fixed_left"] {
        for side in 0..3 {
            let (mut r, c) = super::execute(profile(n));
            let Match::NonParamEqual {
                pattern_after_subst,
                goal_arg,
                equal,
                ..
            } = structure(&mut r)[0].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            match side {
                0 => *pattern_after_subst = super::number_object("7"),
                1 => *goal_arg = super::number_object("7"),
                _ => equal.equal_fact.left = super::number_object("7"),
            };
            reject47(&r, &c, n)
        }
    }
}
#[test]
fn known_interval_requires_actual_parent_wd() {
    for (n, s) in SOURCES {
        let (mut r, c) = super::execute(s);
        dead_wd(target_wd(&mut r));
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_actual_endpoint_wd() {
    for (n, s) in SOURCES {
        let (mut r, c) = super::execute(s);
        dead_wd(&mut wd_stages_mut(target_wd(&mut r)).0[0]);
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_requires_every_formation_membership() {
    for (n, s) in SOURCES {
        let (mut r, c) = super::execute(s);
        wd_stages_mut(target_wd(&mut r)).1.pop();
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_preserves_formation_membership_order() {
    for (n, s) in SOURCES.iter().take(6) {
        let (mut r, c) = super::execute(s);
        wd_stages_mut(target_wd(&mut r)).1.swap(0, 1);
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_preserves_formation_membership_subject() {
    for (n, s) in SOURCES {
        let (mut r, c) = super::execute(s);
        let AtomicFact::InFact(p) =
            &mut super::atomic_proof_mut(&mut wd_stages_mut(target_wd(&mut r)).1[0]).fact
        else {
            panic!()
        };
        p.element = super::number_object("7");
        reject47(&r, &c, n)
    }
}
#[test]
fn known_interval_rejects_changed_constructor_kind_before_child_replay() {
    use std::collections::{HashMap, HashSet};
    for (n, s) in SOURCES {
        let (mut r, c) = super::execute(s);
        let cap = capture(&mut r);
        let subst: HashMap<_, _> = cap
            .instantiation_requirements
            .detailed_ref()
            .param_type_requirements
            .iter()
            .zip(&cap.forall_parameters_match_what_args)
            .map(|(q, a)| (q.param_id, a.clone()))
            .collect();
        let matched = &mut cap.arg_match_proofs[0];
        let Match::ByStructure {
            pattern, goal_arg, ..
        } = matched.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        let original_pattern = pattern.clone();
        retag47(goal_arg);
        let wrong = goal_arg.clone();
        let e = c
            .compile_forall_argument_match(
                &original_pattern,
                &wrong,
                matched,
                &subst,
                &mut HashSet::new(),
                None,
            )
            .unwrap_err();
        assert!(
            matches!(
                e.route.as_str(),
                "CompoundKnown/IntervalKind" | "CompoundKnown/StructureConstructor"
            ),
            "{e}"
        );
        reject47(&r, &c, n)
    }
}
fn retag47(o: &mut Obj) {
    match o {
        Obj::SetFormer(SetFormer::Range(p)) => {
            *o = Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
                start: p.start.clone(),
                end: p.end.clone(),
            }))
        }
        Obj::SetFormer(SetFormer::ClosedRange(p)) => {
            *o = Obj::SetFormer(SetFormer::Range(Range {
                start: p.start.clone(),
                end: p.end.clone(),
            }))
        }
        Obj::SetFormer(SetFormer::IntervalObj(p)) => {
            *p = match p {
                IntervalObj::LeftOpenRightOpen(p) => IntervalObj::LeftClosedRightOpen(p.clone()),
                IntervalObj::LeftOpenRightClosed(p) => {
                    IntervalObj::LeftClosedRightClosed(p.clone())
                }
                IntervalObj::LeftClosedRightOpen(p) => IntervalObj::LeftOpenRightOpen(p.clone()),
                IntervalObj::LeftClosedRightClosed(p) => {
                    IntervalObj::LeftOpenRightClosed(p.clone())
                }
            }
        }
        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) => {
            *p = match p {
                OneSideInfinityIntervalObj::LowerOpen(p) => {
                    OneSideInfinityIntervalObj::UpperOpen(p.clone())
                }
                OneSideInfinityIntervalObj::LowerClosed(p) => {
                    OneSideInfinityIntervalObj::UpperClosed(p.clone())
                }
                OneSideInfinityIntervalObj::UpperOpen(p) => {
                    OneSideInfinityIntervalObj::LowerOpen(p.clone())
                }
                OneSideInfinityIntervalObj::UpperClosed(p) => {
                    OneSideInfinityIntervalObj::LowerClosed(p.clone())
                }
            }
        }
        _ => panic!(),
    }
}

#[test]
fn known_interval_original_generic_guards_retain_cited_domain_evidence() {
    for n in ["range_generic_guarded", "upper_closed_generic_guarded"] {
        let (mut r, c) = super::execute(profile(n));
        let p = capture(&mut r);
        let q = p.instantiation_requirements.detailed_ref();
        assert_eq!(q.dom_facts.len(), 1);
        assert_eq!(q.proof_of_dom_facts.len(), 1);
        assert_eq!(
            source_subject(&q.proof_of_dom_facts[0]).unwrap(),
            q.dom_facts[0]
        );
        assert!(matches!(
            super::atomic_proof_mut(&mut requirements(&mut r).proof_of_dom_facts[0]).searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(_)
        ));
        super::compile_run(&r, &c, n).unwrap();
    }
}
fn fixed_source_wd47(r: &mut RunLitexCodeResult) -> &mut ObjWellDefinedProof {
    let p = super::forall_proof_mut(r.statement_results.last_mut().unwrap());
    let FactWellDefinedProof::ForallFact(q) = &mut p.assumed_dom_facts[0].well_defined else {
        panic!()
    };
    let FactWellDefinedProof::AtomicExceptEquality(q) = &mut q.as_detailed_mut().unwrap().then[0]
    else {
        panic!()
    };
    &mut q.as_detailed_mut().unwrap().well_defined_of_each_parameter[0]
}
fn fixed_factory47(
    r: &RunLitexCodeResult,
    c: &crate::compile_to_lean::LitexToLeanCompiler,
) -> Result<String, crate::compile_to_lean::LeanCompileError> {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = r.statement_results.last().unwrap()
    else {
        panic!()
    };
    let VerifyFactResult::ForallFact(p) = &s.verify_result else {
        panic!()
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = p.as_ref()
    else {
        panic!()
    };
    let VerifyFactResult::AtomicExceptEquality(q) =
        &p.proved_then_facts.last().unwrap().verify_result
    else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(q) = q.as_ref() else {
        panic!()
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(a) = &q.searched_proof else {
        panic!()
    };
    let root = SourcePosition::new(None, SourceOwner::Run(r), r.statement_results.len() - 1);
    let scope = SourcePosition::new(
        Some(&root),
        SourceOwner::Forall(p),
        1 + p.assumed_dom_facts.len(),
    );
    let current = SourcePosition::new(Some(&scope), SourceOwner::KnownApplication(a), 0);
    let formation = SourcePosition::new(Some(&current), SourceOwner::CalleeInstance(a), usize::MAX);
    c.compile_object_reference(&super::number_object("0"), &formation)
}
#[test]
fn known_interval_fixed_literal_factory_requires_exact_original_wd() {
    for n in ["range_fixed_left", "closed_closed_fixed_left"] {
        let (mut r, c) = super::execute(profile(n));
        fixed_factory47(&r, &c).unwrap();
        // Membership formation also retains authentic numeric WD. Remove the
        // complete selected constructor closure rather than demanding that
        // deleting one duplicate certificate invalidate another valid one.
        dead_wd(fixed_source_wd47(&mut r));
        fixed_factory47(&r, &c).expect_err("the complete selected original formation is required");
        reject47(&r, &c, n);
    }
}

#[test]
fn known_interval_keeps_function_return_producers_before_consumers() {
    for n in ["range_returned", "upper_closed_returned"] {
        let (mut r, c) = super::execute(profile(n));
        super::compile_run(&r, &c, n).unwrap();
        let p = super::forall_proof_mut(r.statement_results.last_mut().unwrap());
        p.proved_then_facts.rotate_left(1);
        reject47(&r, &c, n);
    }
}
