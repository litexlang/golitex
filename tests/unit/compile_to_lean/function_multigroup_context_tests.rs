use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof, ForallConclusionArgMatchProof,
};
use crate::prelude::*;
use std::collections::HashSet;
pub(super) const SOURCES62: &[(&str, &str)] = &[
    (
        "returned_ternary",
        "forall sc62a_S set,sc62a_F fn(sc62a_t sc62a_S) fn(sc62a_u,sc62a_v,sc62a_w R) R,sc62a_a sc62a_S,sc62a_x,sc62a_y,sc62a_z R,sc62a_P fn(sc62a_h fn(sc62a_i,sc62a_j,sc62a_k R) R,sc62a_b,sc62a_c,sc62a_d R) R:\n    forall sc62a_s sc62a_S,sc62a_p,sc62a_q,sc62a_r R:\n        sc62a_F(sc62a_s)(sc62a_p,sc62a_q,sc62a_r)=sc62a_P(sc62a_F(sc62a_s),sc62a_p,sc62a_q,sc62a_r)\n    =>:\n        sc62a_F(sc62a_a)(sc62a_x,sc62a_y,sc62a_z)=sc62a_P(sc62a_F(sc62a_a),sc62a_x,sc62a_y,sc62a_z)\n",
    ),
    (
        "returned_guarded_ternary",
        "forall sc62b_S set,sc62b_F fn(sc62b_t sc62b_S) fn(sc62b_u,sc62b_v,sc62b_w R:sc62b_u+sc62b_v>sc62b_w) R,sc62b_a sc62b_S,sc62b_x,sc62b_y,sc62b_z R,sc62b_P fn(sc62b_h fn(sc62b_i,sc62b_j,sc62b_k R:sc62b_i+sc62b_j>sc62b_k) R,sc62b_b,sc62b_c,sc62b_d R:sc62b_b+sc62b_c>sc62b_d) R:\n    sc62b_x+sc62b_y>sc62b_z\n    forall sc62b_s sc62b_S,sc62b_p,sc62b_q,sc62b_r R:\n        sc62b_p+sc62b_q>sc62b_r\n        =>:\n            sc62b_F(sc62b_s)(sc62b_p,sc62b_q,sc62b_r)=sc62b_P(sc62b_F(sc62b_s),sc62b_p,sc62b_q,sc62b_r)\n    =>:\n        sc62b_F(sc62b_a)(sc62b_x,sc62b_y,sc62b_z)=sc62b_P(sc62b_F(sc62b_a),sc62b_x,sc62b_y,sc62b_z)\n",
    ),
    (
        "returned_generic_ternary",
        "forall sc62c_S,sc62c_A,sc62c_B,sc62c_C,sc62c_D set,sc62c_F fn(sc62c_t sc62c_S) fn(sc62c_u sc62c_A,sc62c_v sc62c_B,sc62c_w sc62c_C) sc62c_D,sc62c_a sc62c_S,sc62c_x sc62c_A,sc62c_y sc62c_B,sc62c_z sc62c_C,sc62c_P fn(sc62c_h fn(sc62c_i sc62c_A,sc62c_j sc62c_B,sc62c_k sc62c_C) sc62c_D,sc62c_b sc62c_A,sc62c_c sc62c_B,sc62c_d sc62c_C) sc62c_D:\n    forall sc62c_s sc62c_S,sc62c_p sc62c_A,sc62c_q sc62c_B,sc62c_r sc62c_C:\n        sc62c_F(sc62c_s)(sc62c_p,sc62c_q,sc62c_r)=sc62c_P(sc62c_F(sc62c_s),sc62c_p,sc62c_q,sc62c_r)\n    =>:\n        sc62c_F(sc62c_a)(sc62c_x,sc62c_y,sc62c_z)=sc62c_P(sc62c_F(sc62c_a),sc62c_x,sc62c_y,sc62c_z)\n",
    ),
    (
        "returned_three_groups",
        "forall sc62d_S set,sc62d_F fn(sc62d_t sc62d_S) fn(sc62d_u R) fn(sc62d_v,sc62d_w R) R,sc62d_a sc62d_S,sc62d_x,sc62d_y,sc62d_z R,sc62d_P fn(sc62d_h fn(sc62d_i,sc62d_j R) R,sc62d_b,sc62d_c R) R:\n    forall sc62d_s sc62d_S,sc62d_p,sc62d_q,sc62d_r R:\n        sc62d_F(sc62d_s)(sc62d_p)(sc62d_q,sc62d_r)=sc62d_P(sc62d_F(sc62d_s)(sc62d_p),sc62d_q,sc62d_r)\n    =>:\n        sc62d_F(sc62d_a)(sc62d_x)(sc62d_y,sc62d_z)=sc62d_P(sc62d_F(sc62d_a)(sc62d_x),sc62d_y,sc62d_z)\n",
    ),
    (
        "returned_repeated_index",
        "forall sc62e_F fn(sc62e_t R) fn(sc62e_u R) R,sc62e_a R,sc62e_P fn(sc62e_h fn(sc62e_i R) R,sc62e_b R) R:\n    forall sc62e_s R:\n        sc62e_F(sc62e_s)(sc62e_s)=sc62e_P(sc62e_F(sc62e_s),sc62e_s)\n    =>:\n        sc62e_F(sc62e_a)(sc62e_a)=sc62e_P(sc62e_F(sc62e_a),sc62e_a)\n",
    ),
    (
        "bound_head_to_returned_prefix",
        "forall sc62f_S set,sc62f_F fn(sc62f_t sc62f_S) fn(sc62f_u,sc62f_v,sc62f_w R) R,sc62f_a sc62f_S,sc62f_x,sc62f_y,sc62f_z R,sc62f_P fn(sc62f_h fn(sc62f_i,sc62f_j,sc62f_k R) R,sc62f_b,sc62f_c,sc62f_d R) R:\n    forall sc62f_g fn(sc62f_l,sc62f_m,sc62f_n R) R,sc62f_p,sc62f_q,sc62f_r R:\n        sc62f_g(sc62f_p,sc62f_q,sc62f_r)=sc62f_P(sc62f_g,sc62f_p,sc62f_q,sc62f_r)\n    =>:\n        sc62f_F(sc62f_a)(sc62f_x,sc62f_y,sc62f_z)=sc62f_P(sc62f_F(sc62f_a),sc62f_x,sc62f_y,sc62f_z)\n",
    ),
];
fn walk62(
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
                "ORIGINAL62 {name} bound:{i} source:{} goal:{}",
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
                "ORIGINAL62 {name} rebound:{i} previous:{} goal:{}",
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
                "ORIGINAL62 {name} fixed:{} after:{} goal:{}",
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
                "ORIGINAL62 {name} structure_groups:{}/{} outer_widths:{widths:?} certificate_slots:{}",
                left.body.len(),
                right.body.len(),
                pairs.len()
            );
            // Producer executes the final prefix slot first,then stored outer-to-inner args.
            let last = pairs.len() - 1;
            for index in std::iter::once(last).chain(0..last) {
                walk62(
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
#[test]
fn function_multigroup_original_flattened_certificates_and_prefix_order() {
    for (name, source) in SOURCES62 {
        let (run, _compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
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
        let ids = cited
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect::<Vec<_>>();
        assert_eq!(p.arg_match_proofs.len(), 2);
        assert_eq!(ids.len(), p.forall_parameters_match_what_args.len());
        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(source_equal)) =
            &cited.then_facts[0]
        else {
            panic!()
        };
        let mut bound = HashSet::new();
        let mut order = Vec::new();
        let mut stats = [0; 4];
        walk62(
            &source_equal.left,
            &equal.fact.left,
            &p.arg_match_proofs[0],
            &ids,
            &p.forall_parameters_match_what_args,
            &mut bound,
            &mut order,
            &mut stats,
            name,
        );
        walk62(
            &source_equal.right,
            &equal.fact.right,
            &p.arg_match_proofs[1],
            &ids,
            &p.forall_parameters_match_what_args,
            &mut bound,
            &mut order,
            &mut stats,
            name,
        );
        let expected = match *name {
            "returned_repeated_index" => [1, 3, 3, 3],
            "bound_head_to_returned_prefix" => [4, 4, 1, 2],
            _ => [4, 4, 3, 3],
        };
        assert_eq!(stats, expected);
        assert_eq!(bound.len(), ids.len());
        let visit = match *name {
            "returned_three_groups" => vec![2, 3, 1, 0],
            "returned_repeated_index" => vec![0],
            "bound_head_to_returned_prefix" => vec![0, 1, 2, 3],
            _ => vec![1, 2, 3, 0],
        };
        assert_eq!(order, visit);
        let wd = equal.well_defined_proof.as_detailed().unwrap();
        assert_eq!(wd.left.obj().ir(), equal.fact.left.ir());
        assert_eq!(wd.right.obj().ir(), equal.fact.right.ir());
        eprintln!(
            "ORIGINAL62 {name} cite:{} binds:{order:?} stats:{stats:?}",
            p.cite.fact_id.value()
        );
    }
}
#[test]
fn function_multigroup_original_types_guard_and_compiler_boundary() {
    for (name, source) in SOURCES62 {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
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
        let ids = cited
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect::<Vec<_>>();
        let req = p.instantiation_requirements.as_detailed().unwrap();
        assert_eq!(req.param_type_requirements.len(), ids.len());
        for (i, ty) in req.param_type_requirements.iter().enumerate() {
            assert_eq!(ty.param_id, ids[i]);
            eprintln!("ORIGINAL62 {name} type:{i} id:{}", ty.param_id.value());
        }
        let guards = usize::from(*name == "returned_guarded_ternary");
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
                panic!("original guard route:{name}")
            };
            assert_eq!(known.cite_fact_id, outer.fact.dom_facts[0].fact_id());
            assert_eq!(
                known.why_parameters_of_known_fact_are_equal_to_givens.len(),
                2
            );
            eprintln!(
                "ORIGINAL62 {name} guard:{} cite:{} equal_args:2",
                fact.ir(),
                known.cite_fact_id.value()
            );
        }
        let output = compiler.compile_run(&run, "Function62Original").unwrap();
        assert!(!output.contains("sorry"));
        assert!(output.contains("Litex.FunctionSemantics.callValue"));
        eprintln!("ORIGINAL62 {name} original_compiler_replay");
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedSearchProofByKnownForallFact;

fn equal62(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn app62(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal62(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn node62<'a>(
    mut proof: &'a mut ForallConclusionArgMatchProof,
    path: &[usize],
) -> &'a mut DetailedForallConclusionArgMatchProof {
    for index in path {
        let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
            proof.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        proof = &mut child_matches[*index];
    }
    proof.as_detailed_mut().unwrap()
}
fn paths62(proof: &ForallConclusionArgMatchProof, kind: usize) -> Vec<Vec<usize>> {
    let detail = proof.as_detailed().unwrap();
    let current = match detail {
        DetailedForallConclusionArgMatchProof::BoundParam { .. } => 0,
        DetailedForallConclusionArgMatchProof::ReboundParamEqual { .. } => 1,
        DetailedForallConclusionArgMatchProof::NonParamEqual { .. } => 2,
        DetailedForallConclusionArgMatchProof::ByStructure { .. } => 3,
    };
    let mut paths = if current == kind {
        vec![Vec::new()]
    } else {
        Vec::new()
    };
    if let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = detail {
        for (index, child) in child_matches.iter().enumerate() {
            for path in paths62(child, kind) {
                paths.push(std::iter::once(index).chain(path).collect());
            }
        }
    }
    paths
}
fn reject62(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Function62ChangedEvidence")
        .expect_err("changed original evidence must reject");
}

#[test]
fn function_multigroup_requires_all_nested_structure_slots() {
    for (_, source) in SOURCES62 {
        for side in 0..2 {
            let (mut original, _) = super::execute(source);
            for path in paths62(&app62(&mut original).arg_match_proofs[side], 3) {
                for extra in [false, true] {
                    let (mut run, compiler) = super::execute(source);
                    let DetailedForallConclusionArgMatchProof::ByStructure {
                        child_matches, ..
                    } = node62(&mut app62(&mut run).arg_match_proofs[side], &path)
                    else {
                        panic!()
                    };
                    let removed = child_matches.pop().unwrap();
                    if extra {
                        child_matches.push(removed);
                        let (mut donor, _) = super::execute(source);
                        let DetailedForallConclusionArgMatchProof::ByStructure {
                            child_matches: donor,
                            ..
                        } = node62(&mut app62(&mut donor).arg_match_proofs[side], &path)
                        else {
                            panic!()
                        };
                        child_matches.push(donor.pop().unwrap());
                    }
                    assert_eq!(
                        compiler
                            .compile_run(&run, "Function62Slots")
                            .unwrap_err()
                            .route,
                        "KnownApplication/FunctionArity"
                    );
                }
            }
        }
    }
}
#[test]
fn function_multigroup_preserves_flattened_prefix_and_argument_order() {
    for (_, source) in SOURCES62 {
        for side in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
                node62(&mut app62(&mut run).arg_match_proofs[side], &[])
            else {
                panic!()
            };
            let last = child_matches.len() - 1;
            child_matches.swap(0, last);
            reject62(&run, &compiler);
        }
    }
}
#[test]
fn function_multigroup_requires_bound_before_rebound_even_with_identical_subjects() {
    let (mut run, compiler) = super::execute(SOURCES62[4].1);
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        node62(&mut app62(&mut run).arg_match_proofs[0], &[])
    else {
        panic!()
    };
    assert!(matches!(
        child_matches[0].as_detailed().unwrap(),
        DetailedForallConclusionArgMatchProof::BoundParam { .. }
    ));
    assert!(matches!(
        child_matches[1].as_detailed().unwrap(),
        DetailedForallConclusionArgMatchProof::ReboundParamEqual { .. }
    ));
    child_matches.swap(0, 1);
    assert_eq!(
        compiler
            .compile_run(&run, "Function62DependencyOrder")
            .unwrap_err()
            .route,
        "CompoundKnown/ReboundParameter"
    );
}
#[test]
fn function_multigroup_requires_each_original_bound_identity_and_subject() {
    for (_, source) in SOURCES62 {
        let (mut original, _) = super::execute(source);
        for path in paths62(&app62(&mut original).arg_match_proofs[0], 0) {
            for change in ["binder", "captured", "goal"] {
                let (mut run, compiler) = super::execute(source);
                let wrong = equal62(&mut run).fact.right.clone();
                let DetailedForallConclusionArgMatchProof::BoundParam {
                    param_id,
                    pattern,
                    goal_arg,
                } = node62(&mut app62(&mut run).arg_match_proofs[0], &path)
                else {
                    panic!()
                };
                match change {
                    "binder" => *param_id = IdentifierId::new(u64::MAX),
                    "captured" => {
                        assert_ne!(pattern.ir(), wrong.ir());
                        *pattern = wrong;
                    }
                    _ => {
                        assert_ne!(goal_arg.ir(), wrong.ir());
                        *goal_arg = wrong;
                    }
                }
                reject62(&run, &compiler);
            }
        }
    }
}
#[test]
fn function_multigroup_requires_every_nested_rebound_and_strict_equal_subject() {
    for (_, source) in SOURCES62 {
        for side in 0..2 {
            let (mut original, _) = super::execute(source);
            for path in paths62(&app62(&mut original).arg_match_proofs[side], 1) {
                for change in ["binder", "previous", "goal", "equal_left", "equal_right"] {
                    let (mut run, compiler) = super::execute(source);
                    let wrong = equal62(&mut run).fact.right.clone();
                    let DetailedForallConclusionArgMatchProof::ReboundParamEqual {
                        param_id,
                        previous,
                        goal_arg,
                        equal,
                    } = node62(&mut app62(&mut run).arg_match_proofs[side], &path)
                    else {
                        panic!()
                    };
                    match change {
                        "binder" => *param_id = IdentifierId::new(u64::MAX),
                        "previous" => {
                            assert_ne!(previous.ir(), wrong.ir());
                            *previous = wrong;
                        }
                        "goal" => {
                            assert_ne!(goal_arg.ir(), wrong.ir());
                            *goal_arg = wrong;
                        }
                        "equal_left" => {
                            assert_ne!(equal.equal_fact.left.ir(), wrong.ir());
                            equal.equal_fact.left = wrong;
                        }
                        _ => {
                            assert_ne!(equal.equal_fact.right.ir(), wrong.ir());
                            equal.equal_fact.right = wrong;
                        }
                    }
                    reject62(&run, &compiler);
                }
            }
        }
    }
}
#[test]
fn function_multigroup_requires_original_fixed_prefix_and_evaluator() {
    for (_, source) in SOURCES62 {
        for side in 0..2 {
            let (mut original, _) = super::execute(source);
            for path in paths62(&app62(&mut original).arg_match_proofs[side], 2) {
                for change in ["captured", "after", "goal", "equal"] {
                    let (mut run, compiler) = super::execute(source);
                    let wrong = equal62(&mut run).fact.right.clone();
                    let DetailedForallConclusionArgMatchProof::NonParamEqual {
                        pattern,
                        pattern_after_subst,
                        goal_arg,
                        equal,
                    } = node62(&mut app62(&mut run).arg_match_proofs[side], &path)
                    else {
                        panic!()
                    };
                    let subject = match change {
                        "captured" => pattern,
                        "after" => pattern_after_subst,
                        "goal" => goal_arg,
                        _ => &mut equal.equal_fact.left,
                    };
                    assert_ne!(subject.ir(), wrong.ir());
                    *subject = wrong;
                    reject62(&run, &compiler);
                }
            }
        }
    }
}
#[test]
fn function_multigroup_requires_exact_nested_structure_subjects() {
    for (_, source) in SOURCES62 {
        for side in 0..2 {
            let (mut original, _) = super::execute(source);
            for path in paths62(&app62(&mut original).arg_match_proofs[side], 3) {
                for captured in [false, true] {
                    let (mut run, compiler) = super::execute(source);
                    let wrong = app62(&mut run).forall_parameters_match_what_args[0].clone();
                    let DetailedForallConclusionArgMatchProof::ByStructure {
                        pattern,
                        goal_arg,
                        ..
                    } = node62(&mut app62(&mut run).arg_match_proofs[side], &path)
                    else {
                        panic!()
                    };
                    let subject = if captured { pattern } else { goal_arg };
                    assert_ne!(subject.ir(), wrong.ir());
                    *subject = wrong;
                    reject62(&run, &compiler);
                }
            }
        }
    }
}

fn guard62(run: &mut RunLitexCodeResult) -> &mut AtomicExceptEqualityFactSearchedProof {
    let VerifyFactResult::AtomicExceptEquality(p) = &mut app62(run)
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
fn function_multigroup_preserves_source_type_and_captured_argument_ids() {
    for (_, source) in SOURCES62 {
        for change in ["source", "first_type", "last_type", "argument"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "source" => app62(&mut run).cite.fact_id = FactId::new(u64::MAX),
                "first_type" => {
                    app62(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[0]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                "last_type" => {
                    app62(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements
                        .last_mut()
                        .unwrap()
                        .param_id = IdentifierId::new(u64::MAX)
                }
                _ => {
                    let wrong = equal62(&mut run).fact.left.clone();
                    app62(&mut run).forall_parameters_match_what_args[0] = wrong;
                }
            }
            reject62(&run, &compiler);
        }
    }
}
#[test]
fn function_multigroup_rejects_enclosing_unfinished_forall_citation() {
    for (_, source) in SOURCES62 {
        let (mut run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "Function62EnclosingPristine")
            .unwrap();
        let id = super::forall_proof(&run.statement_results[0]).fact.fact_id;
        assert_ne!(app62(&mut run).cite.fact_id, id);
        app62(&mut run).cite.fact_id = id;
        reject62(&run, &compiler);
    }
}

#[test]
fn function_multigroup_rejects_sibling_forall_citation() {
    for (_, source) in SOURCES62 {
        let sibling = source.replace("sc62", "sc62s");
        let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
        compiler
            .compile_run(&run, "Function62SiblingPristine")
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
        app62(&mut run).cite.fact_id = id;
        reject62(&run, &compiler);
    }
}
#[test]
fn function_multigroup_requires_full_parent_and_call_formation() {
    for (_, source) in SOURCES62 {
        for missing in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let wd = equal62(&mut run)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap();
            if missing {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(p),
                    ..
                } = wd.right.as_detailed_mut().unwrap()
                else {
                    panic!("original evaluator call WD")
                };
                p.requirement_fact_verified.pop();
            } else {
                std::mem::swap(&mut wd.left, &mut wd.right);
            }
            reject62(&run, &compiler);
        }
    }
}
#[test]
fn function_multigroup_requires_all_ordered_type_certificates() {
    for (_, source) in SOURCES62 {
        for order in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let types = &mut app62(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements;
            if order {
                let last = types.len() - 1;
                if last > 0 {
                    types.swap(0, last);
                } else {
                    types[0].param_id = IdentifierId::new(u64::MAX);
                }
            } else {
                types.pop();
            }
            reject62(&run, &compiler);
        }
    }
}
#[test]
fn function_multigroup_requires_original_guard_lists_and_subject() {
    for change in ["facts", "proofs", "extra", "subject"] {
        let (mut run, compiler) = super::execute(SOURCES62[1].1);
        if change == "subject" {
            let (mut donor, _) = super::execute(SOURCES62[0].1);
            let wrong = super::forall_proof_mut(&mut donor.statement_results[0])
                .proved_then_facts
                .pop()
                .unwrap()
                .verify_result;
            app62(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0] = wrong;
        } else {
            let req = app62(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap();
            match change {
                "facts" => req.dom_facts.clear(),
                "proofs" => req.proof_of_dom_facts.clear(),
                _ => req.dom_facts.push(req.dom_facts[0].clone()),
            }
        }
        reject62(&run, &compiler);
    }
}
#[test]
fn function_multigroup_rejects_foreign_and_self_guard_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES62[1].1);
        let id = crate::compile_to_lean::helper::source_subject(
            &app62(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0],
        )
        .unwrap()
        .fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard62(&mut run)
        else {
            panic!()
        };
        assert_ne!(known.cite_fact_id, id);
        known.cite_fact_id = if own { id } else { FactId::new(u64::MAX) };
        reject62(&run, &compiler);
    }
}
#[test]
fn function_multigroup_rejects_future_and_sibling_guard_citations() {
    let source = SOURCES62[1].1;
    let later = "sc62b_x+sc62b_y>sc62b_z";
    let (mut run, compiler) = super::execute(&format!("{source}        {later}\n"));
    compiler
        .compile_run(&run, "Function62FutureGuardPristine")
        .unwrap();
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future =
        crate::compile_to_lean::helper::source_subject(&outer.proved_then_facts[1].verify_result)
            .unwrap();
    assert_eq!(future.ir(), outer.fact.dom_facts[0].ir());
    let id = future.fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard62(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject62(&run, &compiler);
    let sibling = source.replace("sc62", "sc62s");
    let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
    compiler
        .compile_run(&run, "Function62SiblingGuardPristine")
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
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard62(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject62(&run, &compiler);
}
#[test]
fn function_multigroup_requires_original_guard_argument_proofs() {
    for count in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES62[1].1);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard62(&mut run)
        else {
            panic!()
        };
        if count {
            known.why_parameters_of_known_fact_are_equal_to_givens.pop();
        } else {
            let (mut donor, _) = super::execute(SOURCES62[0].1);
            std::mem::swap(
                &mut known.why_parameters_of_known_fact_are_equal_to_givens[0],
                &mut equal62(&mut donor).searched_proof,
            );
        }
        reject62(&run, &compiler);
    }
}
