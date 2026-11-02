use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof, ForallConclusionArgMatchProof,
};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::*;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};
pub(super) const SOURCES63: &[(&str, &str)] = &[
    (
        "returned_ternary_existence",
        "forall sc63b_S set,sc63b_F fn(sc63b_t sc63b_S) fn(sc63b_u,sc63b_v,sc63b_w R) R,sc63b_a sc63b_S,sc63b_x,sc63b_y,sc63b_z R:\n    forall sc63b_s sc63b_S,sc63b_p,sc63b_q,sc63b_r R:\n        exist sc63b_root R st {sc63b_root^2=sc63b_F(sc63b_s)(sc63b_p,sc63b_q,sc63b_r)}\n    =>:\n        exist sc63b_answer R st {sc63b_answer^2=sc63b_F(sc63b_a)(sc63b_x,sc63b_y,sc63b_z)}\n",
    ),
    (
        "returned_guarded_ternary_existence",
        "forall sc63c_S set,sc63c_F fn(sc63c_t sc63c_S) fn(sc63c_u,sc63c_v,sc63c_w R:sc63c_u+sc63c_v>sc63c_w) R,sc63c_a sc63c_S,sc63c_x,sc63c_y,sc63c_z R:\n    sc63c_x+sc63c_y>sc63c_z\n    forall sc63c_s sc63c_S,sc63c_p,sc63c_q,sc63c_r R:\n        sc63c_p+sc63c_q>sc63c_r\n        =>:\n            exist sc63c_root R st {sc63c_root^2=sc63c_F(sc63c_s)(sc63c_p,sc63c_q,sc63c_r)}\n    =>:\n        exist sc63c_answer R st {sc63c_answer^2=sc63c_F(sc63c_a)(sc63c_x,sc63c_y,sc63c_z)}\n",
    ),
    (
        "returned_generic_ternary_existence",
        "forall sc63d_S,sc63d_A,sc63d_B,sc63d_C,sc63d_D set,sc63d_F fn(sc63d_t sc63d_S) fn(sc63d_u sc63d_A,sc63d_v sc63d_B,sc63d_w sc63d_C) sc63d_D,sc63d_a sc63d_S,sc63d_x sc63d_A,sc63d_y sc63d_B,sc63d_z sc63d_C:\n    forall sc63d_s sc63d_S,sc63d_p sc63d_A,sc63d_q sc63d_B,sc63d_r sc63d_C:\n        exist sc63d_root sc63d_D st {sc63d_root=sc63d_F(sc63d_s)(sc63d_p,sc63d_q,sc63d_r)}\n    =>:\n        exist sc63d_answer sc63d_D st {sc63d_answer=sc63d_F(sc63d_a)(sc63d_x,sc63d_y,sc63d_z)}\n",
    ),
    (
        "returned_three_groups_existence",
        "forall sc63e_S set,sc63e_F fn(sc63e_t sc63e_S) fn(sc63e_u R) fn(sc63e_v,sc63e_w R) R,sc63e_a sc63e_S,sc63e_x,sc63e_y,sc63e_z R:\n    forall sc63e_s sc63e_S,sc63e_p,sc63e_q,sc63e_r R:\n        exist sc63e_root R st {sc63e_root^2=sc63e_F(sc63e_s)(sc63e_p)(sc63e_q,sc63e_r)}\n    =>:\n        exist sc63e_answer R st {sc63e_answer^2=sc63e_F(sc63e_a)(sc63e_x)(sc63e_y,sc63e_z)}\n",
    ),
    (
        "returned_unique_positive_root",
        "forall sc63f_S set,sc63f_F fn(sc63f_t sc63f_S) fn(sc63f_u,sc63f_v,sc63f_w R) R+,sc63f_a sc63f_S,sc63f_x,sc63f_y,sc63f_z R:\n    forall sc63f_s sc63f_S,sc63f_p,sc63f_q,sc63f_r R:\n        exist! sc63f_root R+ st {sc63f_root^2=sc63f_F(sc63f_s)(sc63f_p,sc63f_q,sc63f_r)}\n    =>:\n        exist! sc63f_answer R+ st {sc63f_answer^2=sc63f_F(sc63f_a)(sc63f_x,sc63f_y,sc63f_z)}\n",
    ),
    (
        "returned_unique_to_plain_root",
        "forall sc63g_S set,sc63g_F fn(sc63g_t sc63g_S) fn(sc63g_u,sc63g_v,sc63g_w R) R+,sc63g_a sc63g_S,sc63g_x,sc63g_y,sc63g_z R:\n    forall sc63g_s sc63g_S,sc63g_p,sc63g_q,sc63g_r R:\n        exist! sc63g_root R+ st {sc63g_root^2=sc63g_F(sc63g_s)(sc63g_p,sc63g_q,sc63g_r)}\n    =>:\n        exist sc63g_answer R+ st {sc63g_answer^2=sc63g_F(sc63g_a)(sc63g_x,sc63g_y,sc63g_z)}\n",
    ),
    (
        "returned_no_real_root",
        "forall sc63h_S set,sc63h_F fn(sc63h_t sc63h_S) fn(sc63h_u,sc63h_v,sc63h_w R) R,sc63h_a sc63h_S,sc63h_x,sc63h_y,sc63h_z R:\n    forall sc63h_s sc63h_S,sc63h_p,sc63h_q,sc63h_r R:\n        not exist sc63h_root R st {sc63h_root^2=sc63h_F(sc63h_s)(sc63h_p,sc63h_q,sc63h_r)}\n    =>:\n        not exist sc63h_answer R st {sc63h_answer^2=sc63h_F(sc63h_a)(sc63h_x,sc63h_y,sc63h_z)}\n",
    ),
    (
        "returned_two_witnesses",
        "forall sc63i_S set,sc63i_F fn(sc63i_t sc63i_S) fn(sc63i_u,sc63i_v,sc63i_w R) R,sc63i_a sc63i_S,sc63i_x,sc63i_y,sc63i_z R:\n    forall sc63i_s sc63i_S,sc63i_p,sc63i_q,sc63i_r R:\n        exist sc63i_root,sc63i_root_shift R st {sc63i_root^2=sc63i_F(sc63i_s)(sc63i_p,sc63i_q,sc63i_r),sc63i_root_shift=sc63i_root+1}\n    =>:\n        exist sc63i_answer,sc63i_answer_shift R st {sc63i_answer^2=sc63i_F(sc63i_a)(sc63i_x,sc63i_y,sc63i_z),sc63i_answer_shift=sc63i_answer+1}\n",
    ),
];
fn walk63(
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
                "ORIGINAL63 {name} bound:{i} source:{} goal:{}",
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
                "ORIGINAL63 {name} rebound:{i} previous:{} goal:{}",
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
                "ORIGINAL63 {name} fixed:{} after:{} goal:{}",
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
                "ORIGINAL63 {name} structure_groups:{}/{} outer_widths:{widths:?} certificate_slots:{}",
                left.body.len(),
                right.body.len(),
                pairs.len()
            );
            // Producer executes the final prefix slot first,then stored outer-to-inner args.
            let last = pairs.len() - 1;
            for index in std::iter::once(last).chain(0..last) {
                walk63(
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

fn info63(
    result: &VerifyFactResult,
) -> (
    &ExistShapedFact,
    &ExistShapedFactWellDefinedProof,
    &ExistShapedFactSearchedProof,
) {
    let VerifyFactResult::ExistShapedFact(result) = result else {
        panic!("actual existential family")
    };
    match result.as_ref() {
        VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) => {
            (&p.fact, &p.well_defined_proof, &p.searched_proof)
        }
        VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(p)) => {
            (&p.fact, &p.well_defined_proof, &p.searched_proof)
        }
        VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(p)) => {
            (&p.fact, &p.well_defined_proof, &p.searched_proof)
        }
        _ => panic!("successful original existential family"),
    }
}
fn source63(source: &ForallFact) -> ExistShapedFact {
    match &source.then_facts[0] {
        ExistOrAndChainAtomicFact::ExistFact(p) => ExistShapedFact::Exist(p.clone()),
        ExistOrAndChainAtomicFact::ExistUniqueFact(p) => ExistShapedFact::ExistUnique(p.clone()),
        ExistOrAndChainAtomicFact::NotExistFact(p) => ExistShapedFact::NotExist(p.clone()),
        _ => panic!("original source family"),
    }
}
#[test]
fn exist_multigroup_original_families_alpha_and_flattened_match_certificates() {
    for (name, source) in SOURCES63 {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let (goal, wd, searched) = info63(&outer.proved_then_facts[0].verify_result);
        assert_eq!(
            matches!(goal, ExistShapedFact::ExistUnique(_)),
            *name == "returned_unique_positive_root"
        );
        assert_eq!(
            matches!(goal, ExistShapedFact::NotExist(_)),
            *name == "returned_no_real_root"
        );
        let witness_ids = goal.plain().typed_parameters.ordered_param_ids();
        assert_eq!(
            witness_ids.len(),
            if *name == "returned_two_witnesses" {
                2
            } else {
                1
            }
        );
        let wd = wd.as_detailed().unwrap();
        assert_eq!(
            wd.introduced_params
                .defined_params
                .store_and_infer_results
                .len(),
            witness_ids.len()
        );
        assert_eq!(wd.assumed_body_facts.len(), goal.plain().facts.len());
        eprintln!(
            "ORIGINAL63 {name} family_witnesses:{} body:{}",
            witness_ids.len(),
            goal.plain().facts.len()
        );
        {
            let ExistShapedFactSearchedProof::ByKnownForallFact(p) = searched else {
                panic!("original known forall:{name}")
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
            let selected = source63(cited);
            assert_eq!(
                matches!(selected, ExistShapedFact::ExistUnique(_)),
                name.starts_with("returned_unique")
            );
            let source_witnesses = selected.plain().typed_parameters.ordered_param_ids();
            assert_eq!(source_witnesses.len(), witness_ids.len());
            assert!(source_witnesses.iter().all(|id| !witness_ids.contains(id)));
            let renamed: HashMap<_, _> = source_witnesses
                .into_iter()
                .zip(
                    goal.plain()
                        .typed_parameters
                        .groups
                        .iter()
                        .flat_map(|g| g.params.iter())
                        .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p))),
                )
                .collect();
            let ids = cited.typed_parameters.ordered_param_ids();
            assert_eq!(ids.len(), 4);
            assert_eq!(ids.len(), p.forall_parameters_match_what_args.len());
            assert!(witness_ids.iter().all(|id| !ids.contains(id)));
            let originals = crate::ast::fact::plain_exist_fact_free_args_ref(selected.plain());
            let goals = crate::ast::fact::plain_exist_fact_free_args_ref(goal.plain());
            assert_eq!(originals.len(), goals.len());
            assert_eq!(goals.len(), p.arg_match_proofs.len());
            let mut bound = HashSet::new();
            let mut order = Vec::new();
            let mut stats = [0; 4];
            for ((original, goal), proof) in originals.iter().zip(goals).zip(&p.arg_match_proofs) {
                let pattern = match proof.as_detailed().unwrap() {
                    DetailedForallConclusionArgMatchProof::BoundParam { pattern, .. }
                    | DetailedForallConclusionArgMatchProof::NonParamEqual { pattern, .. }
                    | DetailedForallConclusionArgMatchProof::ByStructure { pattern, .. } => pattern,
                    DetailedForallConclusionArgMatchProof::ReboundParamEqual { .. } => original,
                };
                assert!(
                    crate::compile_to_lean::helper::instantiated_object_matches(
                        original, pattern, &renamed
                    ),
                    "original inner witness alignment:{name}"
                );
                walk63(
                    pattern,
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
            let fixed = match *name {
                "returned_generic_ternary_existence" => 2,
                "returned_two_witnesses" => 4,
                _ => 3,
            };
            assert_eq!(stats, [4, 0, fixed, 1]);
            assert_eq!(bound.len(), 4);
            assert_eq!(
                order,
                if *name == "returned_three_groups_existence" {
                    vec![2, 3, 1, 0]
                } else {
                    vec![1, 2, 3, 0]
                }
            );
            eprintln!(
                "ORIGINAL63 {name} cite:{} free_args:{} binds:{order:?} stats:{stats:?}",
                p.cite.fact_id.value(),
                originals.len()
            );
        }
        let output = compiler.compile_run(&run, "Exist63Original").unwrap();
        assert!(!output.contains("sorry"));
        eprintln!("ORIGINAL63 {name} current_compiler_replay");
    }
}
#[test]
fn exist_multigroup_original_type_guard_and_witness_formation_certificates() {
    for (name, source) in SOURCES63 {
        let (run, _) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let (goal, wd, searched) = info63(&outer.proved_then_facts[0].verify_result);
        let ids = goal.plain().typed_parameters.ordered_param_ids();
        let wd = wd.as_detailed().unwrap();
        assert_eq!(
            wd.introduced_params
                .defined_params
                .store_and_infer_results
                .len(),
            ids.len()
        );
        assert_eq!(wd.assumed_body_facts.len(), goal.plain().facts.len());
        let ExistShapedFactSearchedProof::ByKnownForallFact(p) = searched else {
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
            eprintln!("ORIGINAL63 {name} type:{i} id:{}", ty.param_id.value());
        }
        let guards = usize::from(*name == "returned_guarded_ternary_existence");
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
            eprintln!(
                "ORIGINAL63 {name} guard:{} cite:{}",
                fact.ir(),
                known.cite_fact_id.value()
            );
        }
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedSearchProofByKnownForallFact;
fn info63_mut(
    run: &mut RunLitexCodeResult,
) -> (
    &mut ExistShapedFact,
    &mut ExistShapedFactWellDefinedProof,
    &mut ExistShapedFactSearchedProof,
) {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let VerifyFactResult::ExistShapedFact(result) = &mut outer.proved_then_facts[0].verify_result
    else {
        panic!()
    };
    match result.as_mut() {
        VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) => (
            &mut p.fact,
            &mut p.well_defined_proof,
            &mut p.searched_proof,
        ),
        VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(p)) => (
            &mut p.fact,
            &mut p.well_defined_proof,
            &mut p.searched_proof,
        ),
        VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(p)) => (
            &mut p.fact,
            &mut p.well_defined_proof,
            &mut p.searched_proof,
        ),
        _ => panic!(),
    }
}
fn app63(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let ExistShapedFactSearchedProof::ByKnownForallFact(p) = info63_mut(run).2 else {
        panic!("original forall route")
    };
    p.as_detailed_mut().unwrap()
}
fn plain63_mut(fact: &mut ExistShapedFact) -> &mut PlainExistFact {
    match fact {
        ExistShapedFact::Exist(p)
        | ExistShapedFact::ExistUnique(p)
        | ExistShapedFact::NotExist(p) => p,
    }
}
fn call63(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let p = app63(run);
    for proof in &mut p.arg_match_proofs {
        if matches!(
            proof.as_detailed().unwrap(),
            DetailedForallConclusionArgMatchProof::ByStructure { .. }
        ) {
            let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
                proof.as_detailed_mut().unwrap()
            else {
                unreachable!()
            };
            return child_matches;
        }
    }
    panic!("original returned-call match")
}
fn reject63(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Exist63ChangedEvidence")
        .expect_err("changed original evidence must reject");
}
#[test]
fn exist_returned_preserves_plain_unique_negative_goal_family() {
    for (_, source) in SOURCES63 {
        let (mut run, compiler) = super::execute(source);
        let goal = info63_mut(&mut run).0;
        let plain = goal.plain().clone();
        *goal = if matches!(goal, ExistShapedFact::ExistUnique(_)) {
            ExistShapedFact::Exist(plain)
        } else {
            ExistShapedFact::ExistUnique(plain)
        };
        reject63(&run, &compiler);
    }
}
#[test]
fn exist_returned_preserves_each_inner_witness_identity() {
    for (_, source) in SOURCES63 {
        let (mut original, _) = super::execute(source);
        let count = info63_mut(&mut original)
            .0
            .plain()
            .typed_parameters
            .ordered_param_ids()
            .len();
        for index in 0..count {
            let (mut run, compiler) = super::execute(source);
            let goal = plain63_mut(info63_mut(&mut run).0);
            let p = goal
                .typed_parameters
                .groups
                .iter_mut()
                .flat_map(|g| g.params.iter_mut())
                .nth(index)
                .unwrap();
            p.id = IdentifierId::new(u64::MAX);
            reject63(&run, &compiler);
        }
    }
}
#[test]
fn exist_returned_requires_complete_free_argument_and_nested_call_proofs() {
    for (_, source) in SOURCES63 {
        for nested in [false, true] {
            for extra in [false, true] {
                let (mut run, compiler) = super::execute(source);
                let proofs = if nested {
                    call63(&mut run)
                } else {
                    &mut app63(&mut run).arg_match_proofs
                };
                let removed = proofs.pop().unwrap();
                if extra {
                    proofs.push(removed);
                    let (mut donor, _) = super::execute(source);
                    let donor = if nested {
                        call63(&mut donor)
                    } else {
                        &mut app63(&mut donor).arg_match_proofs
                    };
                    proofs.push(donor.pop().unwrap());
                }
                reject63(&run, &compiler);
            }
        }
    }
}
#[test]
fn exist_returned_preserves_flattened_prefix_first_dependencies() {
    for (_, source) in SOURCES63 {
        let (mut run, compiler) = super::execute(source);
        let proofs = call63(&mut run);
        let last = proofs.len() - 1;
        proofs.swap(0, last);
        reject63(&run, &compiler);
    }
}
#[test]
fn exist_returned_requires_each_bound_source_parameter_and_captured_argument() {
    for (_, source) in SOURCES63 {
        for index in 0..4 {
            for captured in [false, true] {
                let (mut run, compiler) = super::execute(source);
                let wrong = Obj::StandardSet(StandardSet::R);
                let DetailedForallConclusionArgMatchProof::BoundParam {
                    param_id, goal_arg, ..
                } = call63(&mut run)[index].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                if captured {
                    assert_ne!(goal_arg.ir(), wrong.ir());
                    *goal_arg = wrong
                } else {
                    *param_id = IdentifierId::new(u64::MAX)
                }
                reject63(&run, &compiler);
            }
        }
    }
}
#[test]
fn exist_returned_requires_original_fixed_prefix_and_equal_endpoints() {
    for (_, source) in SOURCES63 {
        for change in ["after", "left", "right"] {
            let (mut run, compiler) = super::execute(source);
            let wrong = app63(&mut run).forall_parameters_match_what_args[0].clone();
            let DetailedForallConclusionArgMatchProof::NonParamEqual {
                pattern_after_subst,
                equal,
                ..
            } = call63(&mut run)
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
            reject63(&run, &compiler);
        }
    }
}
#[test]
fn exist_returned_requires_original_inner_alpha_alignment() {
    for (_, source) in SOURCES63 {
        let (original, _) = super::execute(source);
        let outer = super::forall_proof(&original.statement_results[0]);
        let (_, _, searched) = info63(&outer.proved_then_facts[0].verify_result);
        let ExistShapedFactSearchedProof::ByKnownForallFact(p) = searched else {
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
        let selected = source63(cited);
        let args = crate::ast::fact::plain_exist_fact_free_args_ref(selected.plain());
        let changes = args
            .iter()
            .zip(&p.arg_match_proofs)
            .enumerate()
            .filter_map(|(index, (arg, proof))| {
                let DetailedForallConclusionArgMatchProof::NonParamEqual { pattern, .. } =
                    proof.as_detailed().unwrap()
                else {
                    return None;
                };
                (arg.ir() != pattern.ir()).then(|| (index, (**arg).clone()))
            })
            .collect::<Vec<_>>();
        for (index, unrenamed) in changes {
            let (mut run, compiler) = super::execute(source);
            let DetailedForallConclusionArgMatchProof::NonParamEqual { pattern, .. } =
                app63(&mut run).arg_match_proofs[index]
                    .as_detailed_mut()
                    .unwrap()
            else {
                panic!()
            };
            *pattern = unrenamed;
            reject63(&run, &compiler);
        }
    }
}
#[test]
fn exist_returned_requires_complete_ordered_witness_and_body_formation() {
    for (_, source) in SOURCES63 {
        for part in ["intro", "body"] {
            let (mut run, compiler) = super::execute(source);
            let wd = info63_mut(&mut run).1.as_detailed_mut().unwrap();
            if part == "intro" {
                wd.introduced_params
                    .defined_params
                    .store_and_infer_results
                    .pop();
            } else {
                wd.assumed_body_facts.pop();
            }
            reject63(&run, &compiler);
        }
    }
    for part in ["intro", "body"] {
        let (mut run, compiler) = super::execute(SOURCES63[7].1);
        let wd = info63_mut(&mut run).1.as_detailed_mut().unwrap();
        if part == "intro" {
            assert_eq!(
                wd.introduced_params
                    .defined_params
                    .store_and_infer_results
                    .len(),
                2
            );
            wd.introduced_params
                .defined_params
                .store_and_infer_results
                .swap(0, 1)
        } else {
            assert_eq!(wd.assumed_body_facts.len(), 2);
            wd.assumed_body_facts.swap(0, 1)
        }
        reject63(&run, &compiler);
    }
}

fn guard63(run: &mut RunLitexCodeResult) -> &mut AtomicExceptEqualityFactSearchedProof {
    let VerifyFactResult::AtomicExceptEquality(p) = &mut app63(run)
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
fn exist_returned_preserves_source_type_and_captured_argument_ids() {
    for (_, source) in SOURCES63 {
        for change in ["source", "first_type", "last_type", "argument"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "source" => app63(&mut run).cite.fact_id = FactId::new(u64::MAX),
                "first_type" => {
                    app63(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[0]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                "last_type" => {
                    app63(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[3]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                _ => app63(&mut run).forall_parameters_match_what_args.swap(0, 1),
            }
            reject63(&run, &compiler);
        }
    }
}
#[test]
fn exist_returned_rejects_enclosing_unfinished_forall_citation() {
    for (_, source) in SOURCES63 {
        let (mut run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "Function63EnclosingPristine")
            .unwrap();
        let id = super::forall_proof(&run.statement_results[0]).fact.fact_id;
        assert_ne!(app63(&mut run).cite.fact_id, id);
        app63(&mut run).cite.fact_id = id;
        reject63(&run, &compiler);
    }
}

#[test]
fn exist_returned_rejects_sibling_forall_citation() {
    for (_, source) in SOURCES63 {
        let sibling = source.replace("sc63", "sc63s");
        let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
        compiler
            .compile_run(&run, "Function63SiblingPristine")
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
        app63(&mut run).cite.fact_id = id;
        reject63(&run, &compiler);
    }
}
#[test]
fn exist_returned_requires_all_ordered_type_certificates() {
    for (_, source) in SOURCES63 {
        for order in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let types = &mut app63(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements;
            if order {
                types.swap(0, 3);
            } else {
                types.pop();
            }
            reject63(&run, &compiler);
        }
    }
}
#[test]
fn exist_returned_requires_original_guard_lists_and_subject() {
    for change in ["facts", "proofs", "extra", "subject"] {
        let (mut run, compiler) = super::execute(SOURCES63[1].1);
        if change == "subject" {
            let (mut donor, _) = super::execute(SOURCES63[0].1);
            let wrong = super::forall_proof_mut(&mut donor.statement_results[0])
                .proved_then_facts
                .pop()
                .unwrap()
                .verify_result;
            app63(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0] = wrong;
        } else {
            let req = app63(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap();
            match change {
                "facts" => req.dom_facts.clear(),
                "proofs" => req.proof_of_dom_facts.clear(),
                _ => req.dom_facts.push(req.dom_facts[0].clone()),
            }
        }
        reject63(&run, &compiler);
    }
}
#[test]
fn exist_returned_rejects_foreign_and_self_guard_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES63[1].1);
        let id = crate::compile_to_lean::helper::source_subject(
            &app63(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0],
        )
        .unwrap()
        .fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard63(&mut run)
        else {
            panic!()
        };
        assert_ne!(known.cite_fact_id, id);
        known.cite_fact_id = if own { id } else { FactId::new(u64::MAX) };
        reject63(&run, &compiler);
    }
}
#[test]
fn exist_returned_rejects_future_and_sibling_guard_citations() {
    let source = SOURCES63[1].1;
    let later = "sc63c_x+sc63c_y>sc63c_z";
    let (mut run, compiler) = super::execute(&format!("{source}        {later}\n"));
    compiler
        .compile_run(&run, "Function63FutureGuardPristine")
        .unwrap();
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future =
        crate::compile_to_lean::helper::source_subject(&outer.proved_then_facts[1].verify_result)
            .unwrap();
    assert_eq!(future.ir(), outer.fact.dom_facts[0].ir());
    let id = future.fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard63(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject63(&run, &compiler);
    let sibling = source.replace("sc63", "sc63s");
    let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
    compiler
        .compile_run(&run, "Function63SiblingGuardPristine")
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
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard63(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject63(&run, &compiler);
}
#[test]
fn exist_returned_requires_original_guard_argument_proofs() {
    for count in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES63[1].1);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard63(&mut run)
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
        reject63(&run, &compiler);
    }
}
