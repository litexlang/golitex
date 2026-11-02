use crate::compile_to_lean::helper::source_subject;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::{
    corresponding_arg_pairs, fn_obj_prefix_obj,
};
use crate::prelude::*;

#[test]
fn function_application_strategy_original_order_and_subjects() {
    for (name,source) in [("returned_prefix","forall sc50_S set,sc50_F fn(sc50_t sc50_S) fn(sc50_x R) R,sc50_a,sc50_b sc50_S:\n    sc50_F(sc50_a)=sc50_F(sc50_b)\n    =>:\n        sc50_F(sc50_a)(0)=sc50_F(sc50_b)(0)\n"),
("returned_binary","forall sc50b_S set,sc50b_F fn(sc50b_t sc50b_S) fn(sc50b_x,sc50b_y R) R,sc50b_a,sc50b_b sc50b_S:\n    sc50b_F(sc50b_a)=sc50b_F(sc50b_b)\n    =>:\n        sc50b_F(sc50b_a)(0,1)=sc50b_F(sc50b_b)(0,1)\n"),
("returned_cartesian","forall sc50v_S set,sc50v_F fn(sc50v_t sc50v_S) cart(R,R),sc50v_a,sc50v_b sc50v_S:\n    sc50v_F(sc50v_a)=sc50v_F(sc50v_b)\n    =>:\n        sc50v_F(sc50v_a)(1)=sc50v_F(sc50v_b)(1)\n"),
("returned_changed_args","forall sc50c_S set,sc50c_F fn(sc50c_t sc50c_S) fn(sc50c_u R) R,sc50c_a,sc50c_b sc50c_S,sc50c_x,sc50c_y R:\n    sc50c_F(sc50c_a)=sc50c_F(sc50c_b)\n    sc50c_x=sc50c_y\n    =>:\n        sc50c_F(sc50c_a)(sc50c_x)=sc50c_F(sc50c_b)(sc50c_y)\n"),
("returned_generic","forall sc50g_S,sc50g_A,sc50g_B,sc50g_C set,sc50g_F fn(sc50g_t sc50g_S) fn(sc50g_x sc50g_A,sc50g_y sc50g_B) sc50g_C,sc50g_a,sc50g_b sc50g_S,sc50g_x sc50g_A,sc50g_y sc50g_B:\n    sc50g_F(sc50g_a)=sc50g_F(sc50g_b)\n    =>:\n        sc50g_F(sc50g_a)(sc50g_x,sc50g_y)=sc50g_F(sc50g_b)(sc50g_x,sc50g_y)\n"),
("returned_repeated","forall sc50r_S set,sc50r_F fn(sc50r_t sc50r_S) fn(sc50r_u,sc50r_v R) R,sc50r_a,sc50r_b sc50r_S,sc50r_x,sc50r_y R:\n    sc50r_F(sc50r_a)=sc50r_F(sc50r_b)\n    sc50r_x=sc50r_y\n    =>:\n        sc50r_F(sc50r_a)(sc50r_x,sc50r_x)=sc50r_F(sc50r_b)(sc50r_y,sc50r_y)\n"),
("returned_ternary","forall sc50t_S set,sc50t_F fn(sc50t_s sc50t_S) fn(sc50t_x,sc50t_y,sc50t_z R) R,sc50t_a,sc50t_b sc50t_S:\n    sc50t_F(sc50t_a)=sc50t_F(sc50t_b)\n    =>:\n        sc50t_F(sc50t_a)(0,1,2)=sc50t_F(sc50t_b)(0,1,2)\n"),
("returned_two_layers","forall sc50d_S set,sc50d_F fn(sc50d_t sc50d_S) fn(sc50d_u R) fn(sc50d_v R) R,sc50d_a,sc50d_b sc50d_S:\n    sc50d_F(sc50d_a)(0)=sc50d_F(sc50d_b)(0)\n    =>:\n        sc50d_F(sc50d_a)(0)(1)=sc50d_F(sc50d_b)(0)(1)\n")] {
  let (run,compiler)=super::execute(source);
  let outer=super::forall_proof(run.statement_results.last().unwrap());
  let equal=super::equality_proof(&outer.proved_then_facts[0].verify_result);
  let EqualFactSearchedProof::ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy::FunctionApplicationCongruence(p))=&equal.searched_proof else {panic!("actual selected strategy:{name}")};
  let (Obj::FnObj(left),Obj::FnObj(right))=(&equal.fact.left,&equal.fact.right)else{panic!()};
  let args_left=left.body.last().unwrap();let args_right=right.body.last().unwrap();
  let mut pairs=vec![(fn_obj_prefix_obj(left,left.body.len()-1),fn_obj_prefix_obj(right,right.body.len()-1))];
  pairs.extend(args_left.iter().zip(args_right).map(|(a,b)|(a.as_ref().clone(),b.as_ref().clone())));
  assert_eq!(p.requirement_facts.len(),pairs.len());assert_eq!(p.proof_of_requirement_facts.len(),pairs.len());
  for(index,((requirement,child),(a,b)))in p.requirement_facts.iter().zip(&p.proof_of_requirement_facts).zip(pairs).enumerate(){
   assert_eq!(source_subject(child).unwrap(),*requirement);
   let Fact::AtomicFact(AtomicFact::EqualFact(f))=requirement else{panic!()};assert_eq!(f.left.ir(),a.ir());assert_eq!(f.right.ir(),b.ir());
   let child=super::equality_proof(child);
   let kind=match &child.searched_proof{
    EqualFactSearchedProof::ByEquivalenceClass(EqualFactSearchedProofByEquivalenceClass::KnownPath(path))=>{
      assert_eq!(path.path.len(),1);if index==0{assert_eq!(path.path[0].2,outer.fact.dom_facts[0].fact_id());}
      eprintln!("ORIGINAL50 {name} child:{index} cite:{}",path.path[0].2.value());"KnownPath"},
    EqualFactSearchedProof::ByTheyAreTheSame(_)=>"ByTheyAreTheSame",
    EqualFactSearchedProof::ByClosedCalculation(_)=>"ByClosedCalculation",
    _=>"OtherOriginal",
   };
   eprintln!("ORIGINAL50 {name} child:{index} requirement:{} kind:{kind} subject:{}",requirement.fact_id().value(),requirement.ir());
  }
  compiler.compile_run(&run,"OriginalApplication50").unwrap();
 }
}

#[test]
fn function_application_matching_original_ternary_order() {
    let source="forall sc50o_f,sc50o_g fn(sc50o_x,sc50o_y,sc50o_z R) R:\n    sc50o_f=sc50o_g\n    =>:\n        sc50o_f(0,1,2)=sc50o_g(0,1,2)\n";
    let (run, compiler) = super::execute(source);
    let outer = super::forall_proof(run.statement_results.last().unwrap());
    let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
        panic!("original ordinary matching")
    };
    let pairs = corresponding_arg_pairs(&equal.fact.left, &equal.fact.right).unwrap();
    assert_eq!(pairs.len(), 4);
    for (index, (child, (a, b))) in p
        .corresponding_arg_equal_proofs
        .iter()
        .zip(pairs)
        .enumerate()
    {
        assert!(
            matches!(source_subject(child).unwrap(),Fact::AtomicFact(AtomicFact::EqualFact(f))if f.left.ir()==a.ir()&&f.right.ir()==b.ir())
        );
        eprintln!(
            "ORIGINAL50 matching child:{index} subject:{}",
            source_subject(child).unwrap().ir()
        );
    }
    assert!(compiler
        .compile_run(&run, "OriginalMatching50")
        .unwrap()
        .contains("tupleValue"));
}

#[test]
fn function_application_interleaved_wd_original_audit() {
    let source="have fn scwd_h(x R) R = x+1\nforall scwd_F fn(scwd_x R: scwd_h(scwd_x)!=0) fn(scwd_y R) R,scwd_a R:\n    scwd_h(scwd_a)!=0\n    =>:\n        scwd_F(scwd_a)(scwd_h(scwd_a))=scwd_F(scwd_a)(scwd_h(scwd_a))\n";
    let (mut run, compiler) = super::execute(source);
    compiler
        .compile_run(&run, "OriginalInterleaving50")
        .unwrap();
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let equal = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(call),
        ..
    } = equal
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!()
    };
    eprintln!(
        "ORIGINAL50 interleaved children:{} requirements:{}",
        call.child_obj_well_defined.len(),
        call.requirement_fact_verified.len()
    );
    for (i, p) in call.requirement_fact_verified.iter().enumerate() {
        eprintln!(
            "ORIGINAL50 interleaved requirement{i}:{}",
            source_subject(p).unwrap().ir()
        );
    }
    assert_eq!(call.child_obj_well_defined.len(), 2);
    assert_eq!(call.requirement_fact_verified.len(), 3);
    let scope = call.argument_scope.as_ref().unwrap();
    assert!(scope.formed_children.is_empty());
    eprintln!("AUDIT50 interleaved probe has no newly formed later WD producer;no future-reference reproduction established");
}

const APPLICATION_SOURCE50: &str = "forall sc50_S set,sc50_F fn(sc50_t sc50_S) fn(sc50_x R) R,sc50_a,sc50_b sc50_S:\n    sc50_F(sc50_a)=sc50_F(sc50_b)\n    =>:\n        sc50_F(sc50_a)(0)=sc50_F(sc50_b)(0)\n";
const REPEATED_SOURCE50: &str = "forall sc50r_S set,sc50r_F fn(sc50r_t sc50r_S) fn(sc50r_u,sc50r_v R) R,sc50r_a,sc50r_b sc50r_S,sc50r_x,sc50r_y R:\n    sc50r_F(sc50r_a)=sc50r_F(sc50r_b)\n    sc50r_x=sc50r_y\n    =>:\n        sc50r_F(sc50r_a)(sc50r_x,sc50r_x)=sc50r_F(sc50r_b)(sc50r_y,sc50r_y)\n";
const BINARY_SOURCE50: &str = "forall sc50b_S set,sc50b_F fn(sc50b_t sc50b_S) fn(sc50b_x,sc50b_y R) R,sc50b_a,sc50b_b sc50b_S:\n    sc50b_F(sc50b_a)=sc50b_F(sc50b_b)\n    =>:\n        sc50b_F(sc50b_a)(0,1)=sc50b_F(sc50b_b)(0,1)\n";
const MATCHING_SOURCE50: &str = "forall sc50o_f,sc50o_g fn(sc50o_x,sc50o_y,sc50o_z R) R:\n    sc50o_f=sc50o_g\n    =>:\n        sc50o_f(0,1,2)=sc50o_g(0,1,2)\n";

fn selected_application50(run: &mut RunLitexCodeResult) -> &mut crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_by_composed_structure::FunctionApplicationCongruenceProof{
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::FunctionApplicationCongruence(p),
    ) = &mut equal.searched_proof
    else {
        panic!()
    };
    p
}

#[test]
fn function_application_rejects_missing_and_extra_original_children() {
    for change in 0..3 {
        let (mut run, compiler) = super::execute(APPLICATION_SOURCE50);
        let p = selected_application50(&mut run);
        match change {
            0 => {
                p.requirement_facts.pop();
            }
            1 => {
                p.proof_of_requirement_facts.pop();
            }
            _ => p.requirement_facts.push(p.requirement_facts[0].clone()),
        };
        assert_eq!(
            compiler
                .compile_run(&run, "BadApplicationCount50")
                .unwrap_err()
                .route,
            "FunctionApplicationStrategy/Requirements"
        );
    }
}

#[test]
fn function_application_rejects_reordered_original_child_proofs_and_subjects() {
    for both in [false, true] {
        let (mut run, compiler) = super::execute(APPLICATION_SOURCE50);
        let p = selected_application50(&mut run);
        p.proof_of_requirement_facts.swap(0, 1);
        if both {
            p.requirement_facts.swap(0, 1);
        }
        assert_eq!(
            compiler
                .compile_run(&run, "BadApplicationOrder50")
                .unwrap_err()
                .route,
            "FunctionApplicationStrategy/RequirementSubject"
        );
    }
}

#[test]
fn function_application_rejects_a_changed_original_prefix_citation() {
    let (mut run, compiler) = super::execute(APPLICATION_SOURCE50);
    let p = selected_application50(&mut run);
    let head = super::equality_proof_mut(&mut p.proof_of_requirement_facts[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut head.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = FactId::new(u64::MAX);
    compiler
        .compile_run(&run, "ForeignPrefix50")
        .expect_err("the original prefix citation must be replayed");
}

#[test]
fn function_application_rejects_a_later_sibling_prefix_citation() {
    let (mut run, compiler) = super::execute(&format!("{APPLICATION_SOURCE50}{BINARY_SOURCE50}"));
    let later = super::forall_proof(&run.statement_results[1]);
    let id = later.fact.dom_facts[0].fact_id();
    let p = selected_application50(&mut run);
    let head = super::equality_proof_mut(&mut p.proof_of_requirement_facts[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &mut head.searched_proof
    else {
        panic!()
    };
    path.path[0].2 = id;
    compiler
        .compile_run(&run, "SiblingPrefix50")
        .expect_err("a later closed sibling is not the original active prefix");
}

#[test]
fn function_application_repeated_arguments_keep_original_fact_ids() {
    let (mut run, compiler) = super::execute(REPEATED_SOURCE50);
    let p = selected_application50(&mut run);
    assert_ne!(
        p.requirement_facts[1].fact_id(),
        p.requirement_facts[2].fact_id()
    );
    p.proof_of_requirement_facts.swap(1, 2);
    assert_eq!(
        compiler
            .compile_run(&run, "RepeatedWrongId50")
            .unwrap_err()
            .route,
        "FunctionApplicationStrategy/RequirementSubject"
    );
}

#[test]
fn function_application_requires_both_original_parent_formations() {
    let (mut run, compiler) = super::execute(APPLICATION_SOURCE50);
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(p),
        ..
    } = equal
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!()
    };
    p.requirement_fact_verified.pop();
    assert_eq!(
        compiler
            .compile_run(&run, "MissingApplicationWd50")
            .unwrap_err()
            .route,
        "WD/FnObj/StageArity"
    );
}

#[test]
fn function_application_matching_rejects_wrong_higher_arity_children() {
    for order in [false, true] {
        let (mut run, compiler) = super::execute(MATCHING_SOURCE50);
        let outer = super::forall_proof_mut(&mut run.statement_results[0]);
        let equal = super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal.searched_proof else {
            panic!()
        };
        if order {
            p.corresponding_arg_equal_proofs.swap(0, 3);
        } else {
            p.corresponding_arg_equal_proofs.pop();
        }
        assert_eq!(
            compiler
                .compile_run(&run, "BadMatchingArguments50")
                .unwrap_err()
                .route,
            if order {
                "FunctionCongruence/ChildSubject"
            } else {
                "FunctionCongruence/Children"
            }
        );
    }
}

#[test]
fn function_application_replays_the_checked_prefix_after_forall_instantiation() {
    let source="forall sc50k_S set,sc50k_F fn(sc50k_t sc50k_S) fn(sc50k_x R) R,sc50k_a,sc50k_b sc50k_S:\n    forall sc50k_u,sc50k_v sc50k_S:\n        sc50k_F(sc50k_u)=sc50k_F(sc50k_v)\n    =>:\n        sc50k_F(sc50k_a)=sc50k_F(sc50k_b)\n        sc50k_F(sc50k_a)(0)=sc50k_F(sc50k_b)(0)\n";
    let (run, compiler) = super::execute(source);
    let outer = super::forall_proof(run.statement_results.last().unwrap());
    assert_eq!(outer.proved_then_facts.len(), 2);
    let prefix = super::equality_proof(&outer.proved_then_facts[0].verify_result);
    assert!(matches!(
        prefix.searched_proof,
        EqualFactSearchedProof::ByKnownForallFact(_)
    ));
    let target = super::equality_proof(&outer.proved_then_facts[1].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::FunctionApplicationCongruence(p),
    ) = &target.searched_proof
    else {
        panic!()
    };
    let head = super::equality_proof(&p.proof_of_requirement_facts[0]);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
    ) = &head.searched_proof
    else {
        panic!()
    };
    assert_eq!(path.path.len(), 1);
    assert_eq!(path.path[0].2, prefix.fact.fact_id);
    compiler.compile_run(&run, "InstantiatedPrefix50").unwrap();
}
