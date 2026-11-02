use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof, ForallConclusionArgMatchProof,
};
use crate::prelude::*;
use std::collections::HashSet;
pub(super) const SOURCES64: &[(&str,&str)] = &[
("returned_binary_value","forall sc64a_S set,sc64a_F fn(sc64a_t sc64a_S) fn(sc64a_u,sc64a_v,sc64a_w R) R,sc64a_a sc64a_S,sc64a_x,sc64a_y,sc64a_z R:\n    forall sc64a_s sc64a_S,sc64a_p,sc64a_q,sc64a_r R:\n        sc64a_F(sc64a_s)(sc64a_p,sc64a_q,sc64a_r)=0 or sc64a_F(sc64a_s)(sc64a_p,sc64a_q,sc64a_r)=1\n    =>:\n        sc64a_F(sc64a_a)(sc64a_x,sc64a_y,sc64a_z)=0 or sc64a_F(sc64a_a)(sc64a_x,sc64a_y,sc64a_z)=1\n"),
("returned_guarded_binary_value","forall sc64b_S set,sc64b_F fn(sc64b_t sc64b_S) fn(sc64b_u,sc64b_v,sc64b_w R:sc64b_u+sc64b_v>sc64b_w) R,sc64b_a sc64b_S,sc64b_x,sc64b_y,sc64b_z R:\n    sc64b_x+sc64b_y>sc64b_z\n    forall sc64b_s sc64b_S,sc64b_p,sc64b_q,sc64b_r R:\n        sc64b_p+sc64b_q>sc64b_r\n        =>:\n            sc64b_F(sc64b_s)(sc64b_p,sc64b_q,sc64b_r)=0 or sc64b_F(sc64b_s)(sc64b_p,sc64b_q,sc64b_r)=1\n    =>:\n        sc64b_F(sc64b_a)(sc64b_x,sc64b_y,sc64b_z)=0 or sc64b_F(sc64b_a)(sc64b_x,sc64b_y,sc64b_z)=1\n"),
("returned_generic_binary_value","forall sc64c_S,sc64c_A,sc64c_B,sc64c_C,sc64c_D set,sc64c_F fn(sc64c_t sc64c_S) fn(sc64c_u sc64c_A,sc64c_v sc64c_B,sc64c_w sc64c_C) sc64c_D,sc64c_a sc64c_S,sc64c_x sc64c_A,sc64c_y sc64c_B,sc64c_z sc64c_C,sc64c_lo,sc64c_hi sc64c_D:\n    forall sc64c_s sc64c_S,sc64c_p sc64c_A,sc64c_q sc64c_B,sc64c_r sc64c_C:\n        sc64c_F(sc64c_s)(sc64c_p,sc64c_q,sc64c_r)=sc64c_lo or sc64c_F(sc64c_s)(sc64c_p,sc64c_q,sc64c_r)=sc64c_hi\n    =>:\n        sc64c_F(sc64c_a)(sc64c_x,sc64c_y,sc64c_z)=sc64c_lo or sc64c_F(sc64c_a)(sc64c_x,sc64c_y,sc64c_z)=sc64c_hi\n"),
("returned_three_groups_binary_value","forall sc64d_S set,sc64d_F fn(sc64d_t sc64d_S) fn(sc64d_u R) fn(sc64d_v,sc64d_w R) R,sc64d_a sc64d_S,sc64d_x,sc64d_y,sc64d_z R:\n    forall sc64d_s sc64d_S,sc64d_p,sc64d_q,sc64d_r R:\n        sc64d_F(sc64d_s)(sc64d_p)(sc64d_q,sc64d_r)=0 or sc64d_F(sc64d_s)(sc64d_p)(sc64d_q,sc64d_r)=1\n    =>:\n        sc64d_F(sc64d_a)(sc64d_x)(sc64d_y,sc64d_z)=0 or sc64d_F(sc64d_a)(sc64d_x)(sc64d_y,sc64d_z)=1\n"),
("returned_conjunctive_branches","forall sc64e_S set,sc64e_F fn(sc64e_t sc64e_S) fn(sc64e_u,sc64e_v,sc64e_w R) R,sc64e_a sc64e_S,sc64e_x,sc64e_y,sc64e_z R:\n    forall sc64e_s sc64e_S,sc64e_p,sc64e_q,sc64e_r R:\n        sc64e_F(sc64e_s)(sc64e_p,sc64e_q,sc64e_r)=0 and sc64e_F(sc64e_s)(sc64e_p,sc64e_q,sc64e_r)<1 or sc64e_F(sc64e_s)(sc64e_p,sc64e_q,sc64e_r)=1 and sc64e_F(sc64e_s)(sc64e_p,sc64e_q,sc64e_r)>0\n    =>:\n        sc64e_F(sc64e_a)(sc64e_x,sc64e_y,sc64e_z)=0 and sc64e_F(sc64e_a)(sc64e_x,sc64e_y,sc64e_z)<1 or sc64e_F(sc64e_a)(sc64e_x,sc64e_y,sc64e_z)=1 and sc64e_F(sc64e_a)(sc64e_x,sc64e_y,sc64e_z)>0\n"),
("returned_three_values","forall sc64f_S set,sc64f_F fn(sc64f_t sc64f_S) fn(sc64f_u,sc64f_v,sc64f_w R) R,sc64f_a sc64f_S,sc64f_x,sc64f_y,sc64f_z R:\n    forall sc64f_s sc64f_S,sc64f_p,sc64f_q,sc64f_r R:\n        sc64f_F(sc64f_s)(sc64f_p,sc64f_q,sc64f_r)=0 or sc64f_F(sc64f_s)(sc64f_p,sc64f_q,sc64f_r)=1 or sc64f_F(sc64f_s)(sc64f_p,sc64f_q,sc64f_r)=2\n    =>:\n        sc64f_F(sc64f_a)(sc64f_x,sc64f_y,sc64f_z)=0 or sc64f_F(sc64f_a)(sc64f_x,sc64f_y,sc64f_z)=1 or sc64f_F(sc64f_a)(sc64f_x,sc64f_y,sc64f_z)=2\n"),
];
fn walk64(
    pattern: &Obj,
    goal: &Obj,
    proof: &ForallConclusionArgMatchProof,
    ids: &[IdentifierId],
    args: &[Obj],
    bound: &mut HashSet<IdentifierId>,
    order: &mut Vec<usize>,
    stats: &mut [usize; 4],
    name: &str,
) {
    match proof.as_detailed().unwrap() {
        DetailedForallConclusionArgMatchProof::BoundParam {
            param_id,
            pattern: captured,
            goal_arg,
        } => {
            let i = ids.iter().position(|id| id == param_id).unwrap();
            assert_eq!(captured.ir(), pattern.ir());
            assert_eq!(goal_arg.ir(), goal.ir());
            assert_eq!(args[i].ir(), goal.ir());
            assert!(bound.insert(*param_id), "bound once:{name}");
            order.push(i);
            stats[0] += 1;
            eprintln!(
                "ORIGINAL64 {name} bound:{i} source:{} goal:{}",
                pattern.ir(),
                goal.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::ReboundParamEqual {
            param_id,
            previous,
            goal_arg,
            equal,
        } => {
            let i = ids.iter().position(|id| id == param_id).unwrap();
            assert!(
                bound.contains(param_id),
                "native prefix-first dependencies:{name}:{i}"
            );
            assert_eq!(previous.ir(), args[i].ir());
            assert_eq!(goal_arg.ir(), goal.ir());
            assert_eq!(equal.equal_fact.left.ir(), previous.ir());
            assert_eq!(equal.equal_fact.right.ir(), goal.ir());
            stats[1] += 1;
            eprintln!(
                "ORIGINAL64 {name} rebound:{i} previous:{} goal:{}",
                previous.ir(),
                goal.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::NonParamEqual {
            pattern: captured,
            pattern_after_subst,
            goal_arg,
            equal,
        } => {
            assert_eq!(captured.ir(), pattern.ir());
            assert_eq!(goal_arg.ir(), goal.ir());
            assert_eq!(equal.equal_fact.left.ir(), pattern_after_subst.ir());
            assert_eq!(equal.equal_fact.right.ir(), goal.ir());
            stats[2] += 1;
            eprintln!(
                "ORIGINAL64 {name} fixed:{} after:{} goal:{}",
                pattern.ir(),
                pattern_after_subst.ir(),
                goal.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::ByStructure {
            pattern: captured,
            goal_arg,
            child_matches,
        } => {
            assert_eq!(captured.ir(), pattern.ir());
            assert_eq!(goal_arg.ir(), goal.ir());
            let pairs = corresponding_arg_pairs(pattern, goal)
                .expect("original verifier-owned correspondence");
            assert_eq!(pairs.len(), child_matches.len());
            let (Obj::FnObj(left), Obj::FnObj(right)) = (pattern, goal) else {
                panic!("original function-only structure:{name}")
            };
            let shared = left.body.len().min(right.body.len());
            let widths = (0..shared)
                .map(|i| {
                    let l = left.body[left.body.len() - 1 - i].len();
                    assert_eq!(l, right.body[right.body.len() - 1 - i].len());
                    l
                })
                .collect::<Vec<_>>();
            assert_eq!(pairs.len(), widths.iter().sum::<usize>() + 1);
            stats[3] += 1;
            eprintln!(
                "ORIGINAL64 {name} structure_groups:{}/{} outer_widths:{widths:?} certificate_slots:{}",
                left.body.len(),
                right.body.len(),
                pairs.len()
            );
            // Producer executes the final prefix slot first,then stored outer-to-inner args.
            let last = pairs.len() - 1;
            for index in std::iter::once(last).chain(0..last) {
                walk64(
                    &pairs[index].0,
                    &pairs[index].1,
                    &child_matches[index],
                    ids,
                    args,
                    bound,
                    order,
                    stats,
                    name,
                );
            }
        }
    }
}

fn info64(result: &VerifyFactResult) -> &VerifyOrFactSuccess {
    let VerifyFactResult::OrFact(p) = result else {
        panic!("original OR family")
    };
    let VerifyOrFactResult::Success(p) = p.as_ref() else {
        panic!("original OR success")
    };
    p
}
#[test]
fn or_multigroup_original_ordered_branches_and_rebound_certificates() {
    for (name, source) in SOURCES64 {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let goal = info64(&outer.proved_then_facts[0].verify_result);
        let OrFactSearchedProof::ByKnownForallFact(p) = &goal.searched_proof else {
            panic!("actual winner must be inspected:{name}")
        };
        let p = p.as_detailed().unwrap();
        let Fact::ForallFact(cited) = outer
            .fact
            .dom_facts
            .iter()
            .find(|f| f.fact_id() == p.cite.fact_id)
            .unwrap()
        else {
            panic!()
        };
        let ForallConclusionLocation::DirectThenFact(location) = &p.cite.location else {
            panic!()
        };
        assert_eq!(location.then_fact_index, 0);
        let ExistOrAndChainAtomicFact::OrFact(selected) = &cited.then_facts[0] else {
            panic!()
        };
        assert_eq!(selected.facts.len(), goal.fact.facts.len());
        let originals = crate::ast::fact::or_fact_args_ref(selected);
        let goals = crate::ast::fact::or_fact_args_ref(&goal.fact);
        assert_eq!(originals.len(), goals.len());
        assert_eq!(goals.len(), p.arg_match_proofs.len());
        let ids = cited.typed_parameters.ordered_param_ids();
        assert_eq!(ids.len(), 4);
        assert_eq!(ids.len(), p.forall_parameters_match_what_args.len());
        let mut bound = HashSet::new();
        let mut order = Vec::new();
        let mut stats = [0; 4];
        for ((original, goal), proof) in originals.iter().zip(goals).zip(&p.arg_match_proofs) {
            walk64(
                original,
                goal,
                proof,
                &ids,
                &p.forall_parameters_match_what_args,
                &mut bound,
                &mut order,
                &mut stats,
                name,
            );
        }
        assert_eq!(bound.len(), 4);
        let calls = match *name {
            "returned_conjunctive_branches" => 4,
            "returned_three_values" => 3,
            _ => 2,
        };
        assert_eq!(stats, [4, 4 * (calls - 1), 2 * calls, calls]);
        assert_eq!(
            order,
            if *name == "returned_three_groups_binary_value" {
                vec![2, 3, 1, 0]
            } else {
                vec![1, 2, 3, 0]
            }
        );
        eprintln!(
            "ORIGINAL64 {name} cite:{} branches:{} free_args:{} binds:{order:?} stats:{stats:?}",
            p.cite.fact_id.value(),
            selected.facts.len(),
            originals.len()
        );
        let output = compiler.compile_run(&run, "Or64Original").unwrap();
        assert!(!output.contains("sorry"));
    }
}
#[test]
fn or_multigroup_original_complete_branch_formation_types_and_guard_sources() {
    for (name, source) in SOURCES64 {
        let (run, _) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let goal = info64(&outer.proved_then_facts[0].verify_result);
        let wd = goal.well_defined_proof.as_detailed().unwrap();
        assert_eq!(wd.branches.len(), goal.fact.facts.len());
        for (branch, formation) in goal.fact.facts.iter().zip(&wd.branches) {
            audit_branch64(branch, formation);
        }
        let OrFactSearchedProof::ByKnownForallFact(p) = &goal.searched_proof else {
            panic!()
        };
        let p = p.as_detailed().unwrap();
        let Fact::ForallFact(cited) = outer
            .fact
            .dom_facts
            .iter()
            .find(|f| f.fact_id() == p.cite.fact_id)
            .unwrap()
        else {
            panic!()
        };
        let ids = cited.typed_parameters.ordered_param_ids();
        let req = p.instantiation_requirements.as_detailed().unwrap();
        assert_eq!(req.param_type_requirements.len(), 4);
        for (i, ty) in req.param_type_requirements.iter().enumerate() {
            assert_eq!(ty.param_id, ids[i]);
            assert_eq!(ty.arg.ir(), p.forall_parameters_match_what_args[i].ir());
            assert_eq!(
                crate::compile_to_lean::helper::source_subject(&ty.proof).unwrap(),
                ty.type_fact
            );
        }
        let guards = usize::from(*name == "returned_guarded_binary_value");
        assert_eq!(req.dom_facts.len(), guards);
        assert_eq!(req.proof_of_dom_facts.len(), guards);
        for (fact, proof) in req.dom_facts.iter().zip(&req.proof_of_dom_facts) {
            assert_eq!(
                crate::compile_to_lean::helper::source_subject(proof).unwrap(),
                *fact
            );
            assert_eq!(fact.ir(), outer.fact.dom_facts[0].ir());
            let VerifyFactResult::AtomicExceptEquality(proof) = proof else {
                panic!()
            };
            let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
                panic!()
            };
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                &proof.searched_proof
            else {
                panic!()
            };
            assert_eq!(known.cite_fact_id, outer.fact.dom_facts[0].fact_id());
            assert_eq!(
                known.why_parameters_of_known_fact_are_equal_to_givens.len(),
                2
            );
        }
        eprintln!(
            "ORIGINAL64 {name} complete_branch_WD:{} parameter_types:{} guards:{guards}",
            wd.branches.len(),
            req.param_type_requirements.len()
        );
    }
}

fn atomic_wd64(fact: &AtomicFact, proof: &AtomicFactWellDefinedProof) {
    let args = crate::ast::fact::atomic_fact_args_ref(fact);
    let children = &proof.as_detailed().unwrap().well_defined_of_each_parameter;
    assert_eq!(args.len(), children.len());
    for (arg, child) in args.iter().zip(children) {
        assert_eq!(arg.ir(), child.obj().ir());
    }
}
fn audit_branch64(branch: &AndChainAtomicFact, proof: &FactWellDefinedProof) {
    match (branch, proof) {
        (
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(fact)),
            FactWellDefinedProof::Equality(p),
        ) => {
            let p = p.as_detailed().unwrap();
            assert_eq!(fact.left.ir(), p.left.obj().ir());
            assert_eq!(fact.right.ir(), p.right.obj().ir());
        }
        (AndChainAtomicFact::AtomicFact(fact), FactWellDefinedProof::AtomicExceptEquality(p)) => {
            atomic_wd64(fact, p)
        }
        (AndChainAtomicFact::AndFact(fact), FactWellDefinedProof::AndFact(p)) => {
            let p = p.as_detailed().unwrap();
            assert_eq!(fact.facts.len(), p.components.len());
            for (fact, p) in fact.facts.iter().zip(&p.components) {
                atomic_wd64(fact, p);
            }
        }
        _ => panic!("actual branch formation family"),
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedSearchProofByKnownForallFact;
fn info64_mut(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let VerifyFactResult::OrFact(p) = &mut outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}
fn app64(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let OrFactSearchedProof::ByKnownForallFact(p) = &mut info64_mut(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn call_index64(
    run: &mut RunLitexCodeResult,
    index: usize,
) -> &mut Vec<ForallConclusionArgMatchProof> {
    let p = app64(run);
    let proof = p
        .arg_match_proofs
        .iter_mut()
        .filter(|p| {
            matches!(
                p.as_detailed().unwrap(),
                DetailedForallConclusionArgMatchProof::ByStructure { .. }
            )
        })
        .nth(index)
        .unwrap();
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        proof.as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches
}
fn call64(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    call_index64(run, 0)
}
fn reject64(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Or64ChangedEvidence")
        .expect_err("changed original evidence must reject");
}
#[test]
fn or_returned_requires_complete_ordered_branch_formation() {
    for (_, source) in SOURCES64 {
        for change in ["missing", "extra", "order"] {
            let (mut run, compiler) = super::execute(source);
            let branches = &mut info64_mut(&mut run)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .branches;
            match change {
                "missing" => {
                    branches.pop();
                }
                "order" => branches.swap(0, 1),
                _ => {
                    let (mut donor, _) = super::execute(source);
                    branches.push(
                        info64_mut(&mut donor)
                            .well_defined_proof
                            .as_detailed_mut()
                            .unwrap()
                            .branches
                            .pop()
                            .unwrap(),
                    );
                }
            }
            reject64(&run, &compiler);
        }
    }
}
#[test]
fn or_returned_preserves_original_ordered_branch_subjects() {
    for (_, source) in SOURCES64 {
        for missing in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let goal = &mut info64_mut(&mut run).fact;
            if missing {
                goal.facts.pop();
            } else {
                goal.facts.swap(0, 1);
            }
            reject64(&run, &compiler);
        }
    }
}
#[test]
fn or_returned_preserves_every_rebound_identity_previous_and_strict_endpoint() {
    for (_, source) in SOURCES64 {
        for index in 0..4 {
            for change in ["id", "previous", "goal", "left", "right"] {
                let (mut run, compiler) = super::execute(source);
                let DetailedForallConclusionArgMatchProof::ReboundParamEqual {
                    param_id,
                    previous,
                    goal_arg,
                    equal,
                } = call_index64(&mut run, 1)[index].as_detailed_mut().unwrap()
                else {
                    panic!("actual repeated binding")
                };
                if change == "id" {
                    *param_id = IdentifierId::new(u64::MAX);
                } else {
                    let subject = match change {
                        "previous" => previous,
                        "goal" => goal_arg,
                        "left" => &mut equal.equal_fact.left,
                        _ => &mut equal.equal_fact.right,
                    };
                    let wrong = Obj::StandardSet(StandardSet::R);
                    assert_ne!(subject.ir(), wrong.ir());
                    *subject = wrong;
                }
                reject64(&run, &compiler);
            }
        }
    }
}
#[test]
fn or_returned_cannot_move_rebound_match_before_its_original_binding() {
    for (_, source) in SOURCES64 {
        let (mut run, compiler) = super::execute(source);
        let p = app64(&mut run);
        assert!(matches!(
            p.arg_match_proofs[0].as_detailed().unwrap(),
            DetailedForallConclusionArgMatchProof::ByStructure { .. }
        ));
        assert!(matches!(
            p.arg_match_proofs[2].as_detailed().unwrap(),
            DetailedForallConclusionArgMatchProof::ByStructure { .. }
        ));
        p.arg_match_proofs.swap(0, 2);
        reject64(&run, &compiler);
    }
}

fn guard64(run: &mut RunLitexCodeResult) -> &mut AtomicExceptEqualityFactSearchedProof {
    let VerifyFactResult::AtomicExceptEquality(p) = &mut app64(run)
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap()
        .proof_of_dom_facts[0]
    else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    &mut p.searched_proof
}

#[test]
fn or_returned_requires_complete_free_argument_and_nested_call_proofs() {
    for (_, source) in SOURCES64 {
        for nested in [false, true] {
            for extra in [false, true] {
                let (mut run, compiler) = super::execute(source);
                let proofs = if nested {
                    call64(&mut run)
                } else {
                    &mut app64(&mut run).arg_match_proofs
                };
                let removed = proofs.pop().unwrap();
                if extra {
                    proofs.push(removed);
                    let (mut donor, _) = super::execute(source);
                    let donor = if nested {
                        call64(&mut donor)
                    } else {
                        &mut app64(&mut donor).arg_match_proofs
                    };
                    proofs.push(donor.pop().unwrap());
                }
                reject64(&run, &compiler);
            }
        }
    }
}

#[test]
fn or_returned_preserves_flattened_prefix_first_dependencies() {
    for (_, source) in SOURCES64 {
        let (mut run, compiler) = super::execute(source);
        let proofs = call64(&mut run);
        let last = proofs.len() - 1;
        proofs.swap(0, last);
        reject64(&run, &compiler);
    }
}

#[test]
fn or_returned_requires_each_bound_source_parameter_and_captured_argument() {
    for (_, source) in SOURCES64 {
        for index in 0..4 {
            for captured in [false, true] {
                let (mut run, compiler) = super::execute(source);
                let wrong = Obj::StandardSet(StandardSet::R);
                let DetailedForallConclusionArgMatchProof::BoundParam {
                    param_id, goal_arg, ..
                } = call64(&mut run)[index].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                if captured {
                    assert_ne!(goal_arg.ir(), wrong.ir());
                    *goal_arg = wrong
                } else {
                    *param_id = IdentifierId::new(u64::MAX)
                }
                reject64(&run, &compiler);
            }
        }
    }
}

#[test]
fn or_returned_requires_original_fixed_prefix_and_equal_endpoints() {
    for (_, source) in SOURCES64 {
        for change in ["after", "left", "right"] {
            let (mut run, compiler) = super::execute(source);
            let wrong = app64(&mut run).forall_parameters_match_what_args[0].clone();
            let DetailedForallConclusionArgMatchProof::NonParamEqual {
                pattern_after_subst,
                equal,
                ..
            } = call64(&mut run)
                .last_mut()
                .unwrap()
                .as_detailed_mut()
                .unwrap()
            else {
                panic!()
            };
            let subject = match change {
                "after" => pattern_after_subst,
                "left" => &mut equal.equal_fact.left,
                _ => &mut equal.equal_fact.right,
            };
            assert_ne!(subject.ir(), wrong.ir());
            *subject = wrong;
            reject64(&run, &compiler);
        }
    }
}

#[test]
fn or_returned_preserves_source_type_and_captured_argument_ids() {
    for (_, source) in SOURCES64 {
        for change in ["source", "first_type", "last_type", "argument"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "source" => app64(&mut run).cite.fact_id = FactId::new(u64::MAX),
                "first_type" => {
                    app64(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[0]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                "last_type" => {
                    app64(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[3]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                _ => app64(&mut run).forall_parameters_match_what_args.swap(0, 1),
            }
            reject64(&run, &compiler);
        }
    }
}

#[test]
fn or_returned_rejects_enclosing_unfinished_forall_citation() {
    for (_, source) in SOURCES64 {
        let (mut run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "Function64EnclosingPristine")
            .unwrap();
        let id = super::forall_proof(&run.statement_results[0]).fact.fact_id;
        assert_ne!(app64(&mut run).cite.fact_id, id);
        app64(&mut run).cite.fact_id = id;
        reject64(&run, &compiler);
    }
}

#[test]
fn or_returned_rejects_sibling_forall_citation() {
    for (_, source) in SOURCES64 {
        let sibling = source.replace("sc64", "sc64s");
        let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
        compiler
            .compile_run(&run, "Function64SiblingPristine")
            .unwrap();
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
        else {
            panic!()
        };
        let Fact::ForallFact(sibling) =
            crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
        else {
            panic!()
        };
        let id = sibling
            .dom_facts
            .iter()
            .find(|fact| matches!(fact, Fact::ForallFact(_)))
            .unwrap()
            .fact_id();
        app64(&mut run).cite.fact_id = id;
        reject64(&run, &compiler);
    }
}

#[test]
fn or_returned_requires_all_ordered_type_certificates() {
    for (_, source) in SOURCES64 {
        for order in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let types = &mut app64(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements;
            if order {
                types.swap(0, 3);
            } else {
                types.pop();
            }
            reject64(&run, &compiler);
        }
    }
}

#[test]
fn or_returned_requires_original_guard_lists_and_subject() {
    for change in ["facts", "proofs", "extra", "subject"] {
        let (mut run, compiler) = super::execute(SOURCES64[1].1);
        if change == "subject" {
            let (mut donor, _) = super::execute(SOURCES64[0].1);
            let wrong = super::forall_proof_mut(&mut donor.statement_results[0])
                .proved_then_facts
                .pop()
                .unwrap()
                .verify_result;
            app64(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0] = wrong;
        } else {
            let req = app64(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap();
            match change {
                "facts" => req.dom_facts.clear(),
                "proofs" => req.proof_of_dom_facts.clear(),
                _ => req.dom_facts.push(req.dom_facts[0].clone()),
            }
        }
        reject64(&run, &compiler);
    }
}

#[test]
fn or_returned_rejects_foreign_and_self_guard_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES64[1].1);
        let id = crate::compile_to_lean::helper::source_subject(
            &app64(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0],
        )
        .unwrap()
        .fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard64(&mut run)
        else {
            panic!()
        };
        assert_ne!(known.cite_fact_id, id);
        known.cite_fact_id = if own { id } else { FactId::new(u64::MAX) };
        reject64(&run, &compiler);
    }
}

#[test]
fn or_returned_rejects_future_and_sibling_guard_citations() {
    let source = SOURCES64[1].1;
    let later = "sc64b_x+sc64b_y>sc64b_z";
    let (mut run, compiler) = super::execute(&format!("{source}        {later}\n"));
    compiler
        .compile_run(&run, "Function64FutureGuardPristine")
        .unwrap();
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future =
        crate::compile_to_lean::helper::source_subject(&outer.proved_then_facts[1].verify_result)
            .unwrap();
    assert_eq!(future.ir(), outer.fact.dom_facts[0].ir());
    let id = future.fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard64(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject64(&run, &compiler);
    let sibling = source.replace("sc64", "sc64s");
    let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
    compiler
        .compile_run(&run, "Function64SiblingGuardPristine")
        .unwrap();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
    else {
        panic!()
    };
    let Fact::ForallFact(sibling) =
        crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
    else {
        panic!()
    };
    let id = sibling.dom_facts[0].fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard64(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject64(&run, &compiler);
}

#[test]
fn or_returned_requires_original_guard_argument_proofs() {
    for count in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES64[1].1);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard64(&mut run)
        else {
            panic!()
        };
        if count {
            known.why_parameters_of_known_fact_are_equal_to_givens.pop();
        } else {
            let (mut donor, _) =
                super::execute(super::function_multigroup_context_tests::SOURCES62[0].1);
            std::mem::swap(
                &mut known.why_parameters_of_known_fact_are_equal_to_givens[0],
                &mut super::equality_proof_mut(
                    &mut super::forall_proof_mut(&mut donor.statement_results[0]).proved_then_facts
                        [0]
                    .verify_result,
                )
                .searched_proof,
            );
        }
        reject64(&run, &compiler);
    }
}
