use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof, ForallConclusionArgMatchProof,
};
use crate::prelude::*;
pub(super) const SOURCES60:&[(&str,&str)]=&[
("trace_all_operands","forall sc60_0_n,sc60_0_p N,sc60_0_A matrix(C,sc60_0_n,sc60_0_n),sc60_0_B matrix(C,sc60_0_p,sc60_0_p):\n    sc60_0_A=sc60_0_B\n    sc60_0_n=sc60_0_p\n    =>:\n        trace(sc60_0_A,sc60_0_n)=trace(sc60_0_B,sc60_0_p)\n"),
("det_all_operands","forall sc60_1_n,sc60_1_p N,sc60_1_A matrix(C,sc60_1_n,sc60_1_n),sc60_1_B matrix(C,sc60_1_p,sc60_1_p):\n    sc60_1_A=sc60_1_B\n    sc60_1_n=sc60_1_p\n    =>:\n        det(sc60_1_A,sc60_1_n)=det(sc60_1_B,sc60_1_p)\n"),
("matrix_adjugate_all_operands","forall sc60_2_n,sc60_2_p N,sc60_2_A matrix(C,sc60_2_n,sc60_2_n),sc60_2_B matrix(C,sc60_2_p,sc60_2_p):\n    sc60_2_A=sc60_2_B\n    sc60_2_n=sc60_2_p\n    =>:\n        matrix_adjugate(sc60_2_A,sc60_2_n)=matrix_adjugate(sc60_2_B,sc60_2_p)\n"),
("matrix_inverse_all_operands","forall sc60_3_n,sc60_3_p N,sc60_3_A matrix(C,sc60_3_n,sc60_3_n),sc60_3_B matrix(C,sc60_3_p,sc60_3_p):\n    sc60_3_A=sc60_3_B\n    sc60_3_n=sc60_3_p\n    det(sc60_3_A,sc60_3_n)!=0\n    det(sc60_3_B,sc60_3_p)!=0\n    =>:\n        matrix_inv(sc60_3_A,sc60_3_n)=matrix_inv(sc60_3_B,sc60_3_p)\n"),
("matrix_power_all_operands","forall sc60_4_n,sc60_4_p,sc60_4_e,sc60_4_f N,sc60_4_A matrix(C,sc60_4_n,sc60_4_n),sc60_4_B matrix(C,sc60_4_p,sc60_4_p):\n    sc60_4_A=sc60_4_B\n    sc60_4_n=sc60_4_p\n    sc60_4_e=sc60_4_f\n    =>:\n        matrix_power(sc60_4_A,sc60_4_n,sc60_4_e)=matrix_power(sc60_4_B,sc60_4_p,sc60_4_f)\n"),
("matrix_rank_all_operands","forall sc60_5_m,sc60_5_n,sc60_5_p,sc60_5_q N,sc60_5_A matrix(C,sc60_5_m,sc60_5_n),sc60_5_B matrix(C,sc60_5_p,sc60_5_q):\n    sc60_5_A=sc60_5_B\n    sc60_5_m=sc60_5_p\n    sc60_5_n=sc60_5_q\n    =>:\n        matrix_rank(sc60_5_A,sc60_5_m,sc60_5_n)=matrix_rank(sc60_5_B,sc60_5_p,sc60_5_q)\n"),
("frobenius_norm_all_operands","forall sc60_6_m,sc60_6_n,sc60_6_p,sc60_6_q N,sc60_6_A matrix(C,sc60_6_m,sc60_6_n),sc60_6_B matrix(C,sc60_6_p,sc60_6_q):\n    sc60_6_A=sc60_6_B\n    sc60_6_m=sc60_6_p\n    sc60_6_n=sc60_6_q\n    =>:\n        frobenius_norm(sc60_6_A,sc60_6_m,sc60_6_n)=frobenius_norm(sc60_6_B,sc60_6_p,sc60_6_q)\n"),
("matrix_apply_all_operands","forall sc60_7_m,sc60_7_n,sc60_7_p,sc60_7_q N,sc60_7_A matrix(C,sc60_7_m,sc60_7_n),sc60_7_B matrix(C,sc60_7_p,sc60_7_q),sc60_7_x fn(sc60_7_i closed_range(1,sc60_7_n)) C,sc60_7_y fn(sc60_7_j closed_range(1,sc60_7_q)) C:\n    sc60_7_A=sc60_7_B\n    sc60_7_x=sc60_7_y\n    sc60_7_m=sc60_7_p\n    sc60_7_n=sc60_7_q\n    =>:\n        matrix_apply(sc60_7_A,sc60_7_x,sc60_7_m,sc60_7_n)=matrix_apply(sc60_7_B,sc60_7_y,sc60_7_p,sc60_7_q)\n"),
("matrix_minor_all_operands","forall sc60_8_n,sc60_8_p N+,sc60_8_A matrix(C,sc60_8_n,sc60_8_n),sc60_8_B matrix(C,sc60_8_p,sc60_8_p),sc60_8_i,sc60_8_j closed_range(1,sc60_8_n),sc60_8_k,sc60_8_l closed_range(1,sc60_8_p):\n    sc60_8_A=sc60_8_B\n    sc60_8_n=sc60_8_p\n    sc60_8_i=sc60_8_k\n    sc60_8_j=sc60_8_l\n    =>:\n        matrix_minor(sc60_8_A,sc60_8_n,sc60_8_i,sc60_8_j)=matrix_minor(sc60_8_B,sc60_8_p,sc60_8_k,sc60_8_l)\n"),
("matrix_cofactor_all_operands","forall sc60_9_n,sc60_9_p N+,sc60_9_A matrix(C,sc60_9_n,sc60_9_n),sc60_9_B matrix(C,sc60_9_p,sc60_9_p),sc60_9_i,sc60_9_j closed_range(1,sc60_9_n),sc60_9_k,sc60_9_l closed_range(1,sc60_9_p):\n    sc60_9_A=sc60_9_B\n    sc60_9_n=sc60_9_p\n    sc60_9_i=sc60_9_k\n    sc60_9_j=sc60_9_l\n    =>:\n        matrix_cofactor(sc60_9_A,sc60_9_n,sc60_9_i,sc60_9_j)=matrix_cofactor(sc60_9_B,sc60_9_p,sc60_9_k,sc60_9_l)\n"),
("inner_product_all_operands","forall sc60_10_n,sc60_10_p N,sc60_10_x fn(sc60_10_i closed_range(1,sc60_10_n)) C,sc60_10_y fn(sc60_10_j closed_range(1,sc60_10_n)) C,sc60_10_u fn(sc60_10_k closed_range(1,sc60_10_p)) C,sc60_10_v fn(sc60_10_l closed_range(1,sc60_10_p)) C:\n    sc60_10_x=sc60_10_u\n    sc60_10_y=sc60_10_v\n    sc60_10_n=sc60_10_p\n    =>:\n        inner_product(sc60_10_x,sc60_10_y,sc60_10_n)=inner_product(sc60_10_u,sc60_10_v,sc60_10_p)\n"),
("euclidean_norm_all_operands","forall sc60_11_n,sc60_11_p N,sc60_11_x fn(sc60_11_i closed_range(1,sc60_11_n)) C,sc60_11_y fn(sc60_11_j closed_range(1,sc60_11_p)) C:\n    sc60_11_x=sc60_11_y\n    sc60_11_n=sc60_11_p\n    =>:\n        euclidean_norm(sc60_11_x,sc60_11_n)=euclidean_norm(sc60_11_y,sc60_11_p)\n"),
("forall_trace","forall sc60k_0_A matrix(C,2,2),sc60k_0_P fn(sc60k_0_T matrix(C,2,2)) C:\n    forall sc60k_0_X matrix(C,2,2):\n        trace(sc60k_0_X,2)=sc60k_0_P(sc60k_0_X)\n    =>:\n        trace(sc60k_0_A,2)=sc60k_0_P(sc60k_0_A)\n"),
("forall_det","forall sc60k_1_A matrix(C,2,2),sc60k_1_P fn(sc60k_1_T matrix(C,2,2)) C:\n    forall sc60k_1_X matrix(C,2,2):\n        det(sc60k_1_X,2)=sc60k_1_P(sc60k_1_X)\n    =>:\n        det(sc60k_1_A,2)=sc60k_1_P(sc60k_1_A)\n"),
("forall_matrix_adjugate","forall sc60k_2_A matrix(C,2,2),sc60k_2_P fn(sc60k_2_T matrix(C,2,2)) matrix(C,2,2):\n    forall sc60k_2_X matrix(C,2,2):\n        matrix_adjugate(sc60k_2_X,2)=sc60k_2_P(sc60k_2_X)\n    =>:\n        matrix_adjugate(sc60k_2_A,2)=sc60k_2_P(sc60k_2_A)\n"),
("forall_matrix_inverse","forall sc60k_3_A matrix(C,2,2),sc60k_3_P fn(sc60k_3_T matrix(C,2,2): det(sc60k_3_T,2)!=0) matrix(C,2,2):\n    det(sc60k_3_A,2)!=0\n    forall sc60k_3_X matrix(C,2,2):\n        det(sc60k_3_X,2)!=0\n        =>:\n            matrix_inv(sc60k_3_X,2)=sc60k_3_P(sc60k_3_X)\n    =>:\n        matrix_inv(sc60k_3_A,2)=sc60k_3_P(sc60k_3_A)\n"),
("forall_matrix_power","forall sc60k_4_A matrix(C,2,2),sc60k_4_e N,sc60k_4_P fn(sc60k_4_T matrix(C,2,2),sc60k_4_f N) matrix(C,2,2):\n    forall sc60k_4_X matrix(C,2,2),sc60k_4_k N:\n        matrix_power(sc60k_4_X,2,sc60k_4_k)=sc60k_4_P(sc60k_4_X,sc60k_4_k)\n    =>:\n        matrix_power(sc60k_4_A,2,sc60k_4_e)=sc60k_4_P(sc60k_4_A,sc60k_4_e)\n"),
("forall_matrix_rank","forall sc60k_5_A matrix(C,2,3),sc60k_5_P fn(sc60k_5_T matrix(C,2,3)) N:\n    forall sc60k_5_X matrix(C,2,3):\n        matrix_rank(sc60k_5_X,2,3)=sc60k_5_P(sc60k_5_X)\n    =>:\n        matrix_rank(sc60k_5_A,2,3)=sc60k_5_P(sc60k_5_A)\n"),
("forall_frobenius_norm","forall sc60k_6_A matrix(C,2,3),sc60k_6_P fn(sc60k_6_T matrix(C,2,3)) R:\n    forall sc60k_6_X matrix(C,2,3):\n        frobenius_norm(sc60k_6_X,2,3)=sc60k_6_P(sc60k_6_X)\n    =>:\n        frobenius_norm(sc60k_6_A,2,3)=sc60k_6_P(sc60k_6_A)\n"),
("forall_matrix_apply","forall sc60k_7_A matrix(C,2,3),sc60k_7_v fn(sc60k_7_i closed_range(1,3)) C,sc60k_7_P fn(sc60k_7_T matrix(C,2,3),sc60k_7_w fn(sc60k_7_j closed_range(1,3)) C) fn(sc60k_7_r closed_range(1,2)) C:\n    forall sc60k_7_X matrix(C,2,3),sc60k_7_u fn(sc60k_7_k closed_range(1,3)) C:\n        matrix_apply(sc60k_7_X,sc60k_7_u,2,3)=sc60k_7_P(sc60k_7_X,sc60k_7_u)\n    =>:\n        matrix_apply(sc60k_7_A,sc60k_7_v,2,3)=sc60k_7_P(sc60k_7_A,sc60k_7_v)\n"),
("forall_matrix_minor","forall sc60k_8_A matrix(C,2,2),sc60k_8_r,sc60k_8_c closed_range(1,2),sc60k_8_P fn(sc60k_8_T matrix(C,2,2),sc60k_8_s,sc60k_8_t closed_range(1,2)) matrix(C,1,1):\n    forall sc60k_8_X matrix(C,2,2),sc60k_8_i,sc60k_8_j closed_range(1,2):\n        matrix_minor(sc60k_8_X,2,sc60k_8_i,sc60k_8_j)=sc60k_8_P(sc60k_8_X,sc60k_8_i,sc60k_8_j)\n    =>:\n        matrix_minor(sc60k_8_A,2,sc60k_8_r,sc60k_8_c)=sc60k_8_P(sc60k_8_A,sc60k_8_r,sc60k_8_c)\n"),
("forall_matrix_cofactor","forall sc60k_9_A matrix(C,2,2),sc60k_9_r,sc60k_9_c closed_range(1,2),sc60k_9_P fn(sc60k_9_T matrix(C,2,2),sc60k_9_s,sc60k_9_t closed_range(1,2)) C:\n    forall sc60k_9_X matrix(C,2,2),sc60k_9_i,sc60k_9_j closed_range(1,2):\n        matrix_cofactor(sc60k_9_X,2,sc60k_9_i,sc60k_9_j)=sc60k_9_P(sc60k_9_X,sc60k_9_i,sc60k_9_j)\n    =>:\n        matrix_cofactor(sc60k_9_A,2,sc60k_9_r,sc60k_9_c)=sc60k_9_P(sc60k_9_A,sc60k_9_r,sc60k_9_c)\n"),
("forall_inner_product","forall sc60k_10_a fn(sc60k_10_i closed_range(1,2)) C,sc60k_10_b fn(sc60k_10_j closed_range(1,2)) C,sc60k_10_P fn(sc60k_10_x fn(sc60k_10_k closed_range(1,2)) C,sc60k_10_y fn(sc60k_10_l closed_range(1,2)) C) C:\n    forall sc60k_10_u fn(sc60k_10_m closed_range(1,2)) C,sc60k_10_v fn(sc60k_10_n closed_range(1,2)) C:\n        inner_product(sc60k_10_u,sc60k_10_v,2)=sc60k_10_P(sc60k_10_u,sc60k_10_v)\n    =>:\n        inner_product(sc60k_10_a,sc60k_10_b,2)=sc60k_10_P(sc60k_10_a,sc60k_10_b)\n"),
("forall_euclidean_norm","forall sc60k_11_A fn(sc60k_11_i closed_range(1,2)) C,sc60k_11_P fn(sc60k_11_T fn(sc60k_11_i closed_range(1,2)) C) R:\n    forall sc60k_11_X fn(sc60k_11_k closed_range(1,2)) C:\n        euclidean_norm(sc60k_11_X,2)=sc60k_11_P(sc60k_11_X)\n    =>:\n        euclidean_norm(sc60k_11_A,2)=sc60k_11_P(sc60k_11_A)\n")];
fn operands60(object: &Obj) -> Vec<&Obj> {
    let Obj::MatrixOperator(a) = object else {
        panic!("original matrix operator")
    };
    a.operand_refs()
}
fn walk60(
    proof: &ForallConclusionArgMatchProof,
    ids: &[IdentifierId],
    args: &[Obj],
    counts: &mut [usize; 4],
    name: &str,
) {
    match proof.as_detailed().unwrap() {
        DetailedForallConclusionArgMatchProof::BoundParam {
            param_id,
            pattern,
            goal_arg,
        } => {
            let i = ids.iter().position(|id| id == param_id).unwrap();
            assert_eq!(goal_arg.ir(), args[i].ir());
            counts[0] += 1;
            eprintln!(
                "ORIGINAL60 {name} bound:{} pattern:{} goal:{}",
                param_id.value(),
                pattern.ir(),
                goal_arg.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::ReboundParamEqual {
            param_id,
            previous,
            goal_arg,
            equal,
        } => {
            let i = ids.iter().position(|id| id == param_id).unwrap();
            assert_eq!(previous.ir(), args[i].ir());
            assert_eq!(equal.equal_fact.left.ir(), previous.ir());
            assert_eq!(equal.equal_fact.right.ir(), goal_arg.ir());
            counts[1] += 1;
            eprintln!(
                "ORIGINAL60 {name} rebound:{} previous:{} goal:{}",
                param_id.value(),
                previous.ir(),
                goal_arg.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::NonParamEqual {
            pattern,
            pattern_after_subst,
            goal_arg,
            equal,
        } => {
            assert_eq!(equal.equal_fact.left.ir(), pattern_after_subst.ir());
            assert_eq!(equal.equal_fact.right.ir(), goal_arg.ir());
            counts[2] += 1;
            eprintln!(
                "ORIGINAL60 {name} fixed:{} after:{} goal:{}",
                pattern.ir(),
                pattern_after_subst.ir(),
                goal_arg.ir()
            );
        }
        DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } => {
            counts[3] += 1;
            eprintln!(
                "ORIGINAL60 {name} structure:{} goal:{} children:{}",
                pattern.ir(),
                goal_arg.ir(),
                child_matches.len()
            );
            for child in child_matches {
                walk60(child, ids, args, counts, name);
            }
        }
    }
}
#[test]
fn matrix_remainder_original12_ordered_direct_certificates() {
    for (name, source) in &SOURCES60[..12] {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &equal.searched_proof else {
            panic!("original direct route:{name}")
        };
        let a = operands60(&equal.fact.left);
        let b = operands60(&equal.fact.right);
        assert_eq!(p.corresponding_arg_equal_proofs.len(), a.len());
        let wd = equal.well_defined_proof.as_detailed().unwrap();
        assert_eq!(wd.left.obj().ir(), equal.fact.left.ir());
        assert_eq!(wd.right.obj().ir(), equal.fact.right.ir());
        for (index, proof) in p.corresponding_arg_equal_proofs.iter().enumerate() {
            let child = super::equality_proof(proof);
            assert_eq!(child.fact.left.ir(), a[index].ir());
            assert_eq!(child.fact.right.ir(), b[index].ir());
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &child.searched_proof
            else {
                panic!("original operand equality:{name}:{index}")
            };
            assert_eq!(path.path.len(), 1);
            assert_eq!(path.path[0].2, outer.fact.dom_facts[index].fact_id());
            eprintln!(
                "ORIGINAL60 {name} direct operand:{index} left:{} right:{} cite:{}",
                child.fact.left.ir(),
                child.fact.right.ir(),
                path.path[0].2.value()
            );
        }
        let compiled = compiler
            .compile_run(&run, "Matrix60OriginalDirect")
            .unwrap();
        if *name == "matrix_rank_all_operands" {
            assert!(compiled.contains("matrixRankValue"));
        }
        assert_eq!(
            compiled.contains("set_option smartUnfolding false in"),
            *name == "matrix_power_all_operands"
        );
    }
}
#[test]
fn matrix_remainder_original12_forall_trees_and_inverse_guard() {
    for (name, source) in &SOURCES60[12..] {
        let (run, compiler) = super::execute(source);
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
        let ids: Vec<_> = cited
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        assert_eq!(p.forall_parameters_match_what_args.len(), ids.len());
        assert_eq!(p.arg_match_proofs.len(), 2);
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } = p.arg_match_proofs[0].as_detailed().unwrap()
        else {
            panic!("original matrix structure:{name}")
        };
        let a = operands60(pattern);
        let b = operands60(goal_arg);
        assert_eq!(child_matches.len(), a.len());
        for (i, child) in child_matches.iter().enumerate() {
            match child.as_detailed().unwrap() {
                DetailedForallConclusionArgMatchProof::BoundParam {
                    param_id,
                    pattern,
                    goal_arg,
                } => {
                    assert!(ids.contains(param_id));
                    assert_eq!(pattern.ir(), a[i].ir());
                    assert_eq!(goal_arg.ir(), b[i].ir());
                    let j = ids.iter().position(|id| id == param_id).unwrap();
                    assert_eq!(p.forall_parameters_match_what_args[j].ir(), b[i].ir());
                }
                DetailedForallConclusionArgMatchProof::NonParamEqual {
                    pattern,
                    pattern_after_subst,
                    goal_arg,
                    equal,
                } => {
                    assert_eq!(pattern.ir(), a[i].ir());
                    assert_eq!(pattern_after_subst.ir(), a[i].ir());
                    assert_eq!(goal_arg.ir(), b[i].ir());
                    assert_eq!(equal.equal_fact.left.ir(), a[i].ir());
                    assert_eq!(equal.equal_fact.right.ir(), b[i].ir());
                }
                _ => panic!("unexpected original matrix child:{name}:{i}"),
            }
        }
        let mut stats = [0; 4];
        for child in &p.arg_match_proofs {
            walk60(
                child,
                &ids,
                &p.forall_parameters_match_what_args,
                &mut stats,
                name,
            );
        }
        assert_eq!(stats[0], ids.len());
        assert_eq!(stats[1], ids.len());
        let req = p.instantiation_requirements.as_detailed().unwrap();
        assert_eq!(req.param_type_requirements.len(), ids.len());
        for (i, ty) in req.param_type_requirements.iter().enumerate() {
            assert_eq!(ty.param_id, ids[i]);
        }
        let guards = usize::from(*name == "forall_matrix_inverse");
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
                panic!("original nonzero guard route")
            };
            assert_eq!(known.cite_fact_id, outer.fact.dom_facts[0].fact_id());
            assert_eq!(
                known.why_parameters_of_known_fact_are_equal_to_givens.len(),
                2
            );
            eprintln!(
                "ORIGINAL60 {name} guard_cite:{} equal_args:{}",
                known.cite_fact_id.value(),
                known.why_parameters_of_known_fact_are_equal_to_givens.len()
            );
        }
        eprintln!(
            "ORIGINAL60 {name} source:{} binders:{} types:{} guards:{}",
            p.cite.fact_id.value(),
            ids.len(),
            req.param_type_requirements.len(),
            guards
        );
        let compiled = compiler
            .compile_run(&run, "Matrix60OriginalForall")
            .unwrap();
        assert_eq!(
            compiled.contains("set_option smartUnfolding false in"),
            *name == "forall_matrix_power"
        );
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedSearchProofByKnownForallFact;

fn equal60(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn children60(run: &mut RunLitexCodeResult) -> &mut Vec<VerifyFactResult> {
    let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal60(run).searched_proof else {
        panic!()
    };
    &mut p.corresponding_arg_equal_proofs
}
fn app60(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal60(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn matches60(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        app60(run).arg_match_proofs[0].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches
}
fn rebounds60(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        app60(run).arg_match_proofs[1].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    child_matches
}
fn reject60(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Matrix60ChangedEvidence")
        .expect_err("changed original certificate must reject");
}
fn guard_search60(run: &mut RunLitexCodeResult) -> &mut AtomicExceptEqualityFactSearchedProof {
    let VerifyFactResult::AtomicExceptEquality(p) = &mut app60(run)
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
fn matrix_remainder_direct_requires_complete_arity() {
    for (name, source) in &SOURCES60[..12] {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut donor, _) = super::execute(source);
                children60(&mut run).push(children60(&mut donor).pop().unwrap());
            } else {
                children60(&mut run).pop();
            }
            let expected = if *name == "matrix_rank_all_operands" {
                "Matrix/RankCongruenceChildren"
            } else {
                "ArithmeticCongruence/Children"
            };
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix60Arity")
                    .unwrap_err()
                    .route,
                expected
            );
        }
    }
}
#[test]
fn matrix_remainder_direct_requires_each_ordered_child_subject() {
    for (name, source) in &SOURCES60[..12] {
        let (mut original, _) = super::execute(source);
        let len = children60(&mut original).len();
        for index in 0..len {
            let (mut run, compiler) = super::execute(source);
            let (mut donor, _) = super::execute(source);
            children60(&mut run)[index] = children60(&mut donor).remove((index + 1) % len);
            let expected = if *name == "matrix_rank_all_operands" {
                "Matrix/RankCongruenceChildSubject"
            } else {
                "ArithmeticCongruence/ChildSubject"
            };
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix60ChildSubject")
                    .unwrap_err()
                    .route,
                expected
            );
        }
    }
}
#[test]
fn matrix_remainder_direct_preserves_operand_order() {
    for (_, source) in &SOURCES60[..12] {
        let (mut run, compiler) = super::execute(source);
        children60(&mut run).swap(0, 1);
        reject60(&run, &compiler);
    }
}
#[test]
fn matrix_remainder_direct_rejects_foreign_and_self_citations() {
    for (_, source) in &SOURCES60[..12] {
        for own in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let last = children60(&mut run).len() - 1;
            let child = super::equality_proof_mut(&mut children60(&mut run)[last]);
            let id = child.fact.fact_id;
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = &mut child.searched_proof
            else {
                panic!()
            };
            assert_ne!(path.path[0].2, id);
            path.path[0].2 = if own { id } else { FactId::new(u64::MAX) };
            reject60(&run, &compiler);
        }
    }
}
#[test]
fn matrix_remainder_direct_rejects_matching_future_citation() {
    for (_, source) in &SOURCES60[..12] {
        let later = source
            .lines()
            .take_while(|line| !line.contains("=>:"))
            .filter(|line| line.contains('=') && !line.contains("!="))
            .last()
            .unwrap()
            .trim();
        let source = format!("{}        {}\n", source, later);
        let (mut run, compiler) = super::execute(&source);
        compiler
            .compile_run(&run, "Matrix60FuturePristine")
            .unwrap();
        let outer = super::forall_proof(&run.statement_results[0]);
        assert_eq!(outer.proved_then_facts.len(), 2);
        let future = super::equality_proof(&outer.proved_then_facts[1].verify_result);
        let id = future.fact.fact_id;
        let endpoints = (future.fact.left.ir(), future.fact.right.ir());
        let child = super::equality_proof_mut(children60(&mut run).last_mut().unwrap());
        assert_eq!((child.fact.left.ir(), child.fact.right.ir()), endpoints);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject60(&run, &compiler);
    }
}
#[test]
fn matrix_remainder_direct_rejects_sibling_citation() {
    for (_, source) in &SOURCES60[..12] {
        let sibling = source.replace("sc60_", "sc60s_");
        let (mut run, compiler) = super::execute(&format!("{}{}", source, sibling));
        compiler
            .compile_run(&run, "Matrix60SiblingPristine")
            .unwrap();
        let last = children60(&mut run).len() - 1;
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
        else {
            panic!()
        };
        let Fact::ForallFact(sibling) =
            crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
        else {
            panic!()
        };
        let id = sibling.dom_facts[last].fact_id();
        let child = super::equality_proof_mut(&mut children60(&mut run)[last]);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &mut child.searched_proof
        else {
            panic!()
        };
        path.path[0].2 = id;
        reject60(&run, &compiler);
    }
}
#[test]
fn matrix_remainder_direct_requires_parent_and_child_wd() {
    for (_, source) in &SOURCES60[..12] {
        for child in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let equal = if child {
                super::equality_proof_mut(children60(&mut run).last_mut().unwrap())
            } else {
                equal60(&mut run)
            };
            let wd = equal.well_defined_proof.as_detailed_mut().unwrap();
            std::mem::swap(&mut wd.left, &mut wd.right);
            reject60(&run, &compiler);
        }
    }
}
#[test]
fn matrix_remainder_forall_requires_structure_arity() {
    for (name, source) in &SOURCES60[12..] {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut donor, _) = super::execute(source);
                matches60(&mut run).push(matches60(&mut donor).pop().unwrap());
            } else {
                matches60(&mut run).pop();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Matrix60MatchArity")
                    .unwrap_err()
                    .route,
                if *name == "forall_det" {
                    "CompoundKnown/DeterminantArity"
                } else {
                    "CompoundKnown/StructureArity"
                }
            );
        }
    }
}
#[test]
fn matrix_remainder_forall_preserves_structure_order() {
    for (_, source) in &SOURCES60[12..] {
        let (mut run, compiler) = super::execute(source);
        matches60(&mut run).swap(0, 1);
        reject60(&run, &compiler);
    }
}
#[test]
fn matrix_remainder_forall_preserves_each_binder_identity() {
    for (_, source) in &SOURCES60[12..] {
        let (mut pristine, _) = super::execute(source);
        let positions = matches60(&mut pristine)
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                matches!(
                    p.as_detailed().unwrap(),
                    DetailedForallConclusionArgMatchProof::BoundParam { .. }
                )
                .then_some(i)
            })
            .collect::<Vec<_>>();
        for index in positions {
            let (mut run, compiler) = super::execute(source);
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                matches60(&mut run)[index].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            *param_id = IdentifierId::new(u64::MAX);
            reject60(&run, &compiler);
        }
    }
}
#[test]
fn matrix_remainder_forall_preserves_source_type_and_argument_identities() {
    for (_, source) in &SOURCES60[12..] {
        for change in ["source", "type", "argument"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "source" => app60(&mut run).cite.fact_id = FactId::new(u64::MAX),
                "type" => {
                    app60(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[0]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                _ => {
                    let wrong = equal60(&mut run).fact.left.clone();
                    app60(&mut run).forall_parameters_match_what_args[0] = wrong;
                }
            }
            reject60(&run, &compiler);
        }
    }
}
#[test]
fn matrix_remainder_forall_preserves_every_fixed_operand() {
    for (_, source) in &SOURCES60[12..] {
        let (mut pristine, _) = super::execute(source);
        let positions = matches60(&mut pristine)
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                matches!(
                    p.as_detailed().unwrap(),
                    DetailedForallConclusionArgMatchProof::NonParamEqual { .. }
                )
                .then_some(i)
            })
            .collect::<Vec<_>>();
        assert!(!positions.is_empty());
        for index in positions {
            let (mut run, compiler) = super::execute(source);
            let wrong = operands60(&equal60(&mut run).fact.left)[0].clone();
            let DetailedForallConclusionArgMatchProof::NonParamEqual { goal_arg, .. } =
                matches60(&mut run)[index].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            assert_ne!(goal_arg.ir(), wrong.ir());
            *goal_arg = wrong;
            reject60(&run, &compiler);
        }
    }
}
#[test]
fn matrix_remainder_forall_requires_each_rebound_certificate() {
    for (_, source) in &SOURCES60[12..] {
        let (mut pristine, _) = super::execute(source);
        let positions = rebounds60(&mut pristine)
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                matches!(
                    p.as_detailed().unwrap(),
                    DetailedForallConclusionArgMatchProof::ReboundParamEqual { .. }
                )
                .then_some(i)
            })
            .collect::<Vec<_>>();
        assert!(!positions.is_empty());
        for index in positions {
            for change in ["binder", "previous", "subject"] {
                let (mut run, compiler) = super::execute(source);
                let wrong = equal60(&mut run).fact.left.clone();
                let DetailedForallConclusionArgMatchProof::ReboundParamEqual {
                    param_id,
                    previous,
                    equal,
                    ..
                } = rebounds60(&mut run)[index].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                match change {
                    "binder" => *param_id = IdentifierId::new(u64::MAX),
                    "previous" => *previous = wrong,
                    _ => equal.equal_fact.left = wrong,
                };
                reject60(&run, &compiler);
            }
        }
    }
}
#[test]
fn matrix_remainder_inverse_requires_both_original_guard_lists() {
    for change in ["facts", "proofs", "extra", "subject"] {
        let (mut run, compiler) = super::execute(SOURCES60[15].1);
        if change == "subject" {
            let (mut donor, _) = super::execute(SOURCES60[0].1);
            let wrong = children60(&mut donor).pop().unwrap();
            app60(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0] = wrong;
        } else {
            let req = app60(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap();
            match change {
                "facts" => req.dom_facts.clear(),
                "proofs" => req.proof_of_dom_facts.clear(),
                _ => req.dom_facts.push(req.dom_facts[0].clone()),
            }
        }
        reject60(&run, &compiler);
    }
}
#[test]
fn matrix_remainder_inverse_rejects_foreign_and_self_guard_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES60[15].1);
        let id = crate::compile_to_lean::helper::source_subject(
            &app60(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0],
        )
        .unwrap()
        .fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
            guard_search60(&mut run)
        else {
            panic!()
        };
        assert_ne!(known.cite_fact_id, id);
        known.cite_fact_id = if own { id } else { FactId::new(u64::MAX) };
        reject60(&run, &compiler);
    }
}
#[test]
fn matrix_remainder_inverse_rejects_matching_future_guard_citation() {
    let source = format!("{}        det(sc60k_3_A,2)!=0\n", SOURCES60[15].1);
    let (mut run, compiler) = super::execute(&source);
    compiler
        .compile_run(&run, "Matrix60FutureGuardPristine")
        .unwrap();
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future =
        crate::compile_to_lean::helper::source_subject(&outer.proved_then_facts[1].verify_result)
            .unwrap();
    let id = future.fact_id();
    let req = app60(&mut run)
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap();
    assert_eq!(req.dom_facts[0].ir(), future.ir());
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard_search60(&mut run)
    else {
        panic!()
    };
    known.cite_fact_id = id;
    reject60(&run, &compiler);
}
#[test]
fn matrix_remainder_inverse_rejects_sibling_guard_citation() {
    let source = SOURCES60[15].1;
    let sibling = source.replace("sc60k_", "sc60s_");
    let (mut run, compiler) = super::execute(&format!("{}{}", source, sibling));
    compiler
        .compile_run(&run, "Matrix60SiblingGuardPristine")
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
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard_search60(&mut run)
    else {
        panic!()
    };
    known.cite_fact_id = id;
    reject60(&run, &compiler);
}
#[test]
fn matrix_remainder_inverse_requires_original_guard_argument_equalities() {
    for change in ["count", "subject"] {
        let (mut run, compiler) = super::execute(SOURCES60[15].1);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
            guard_search60(&mut run)
        else {
            panic!()
        };
        if change == "count" {
            known.why_parameters_of_known_fact_are_equal_to_givens.pop();
        } else {
            let (mut donor, _) = super::execute(SOURCES60[0].1);
            let wrong = super::equality_proof_mut(&mut children60(&mut donor)[0]);
            std::mem::swap(
                &mut known.why_parameters_of_known_fact_are_equal_to_givens[0],
                &mut wrong.searched_proof,
            );
        }
        reject60(&run, &compiler);
    }
}
#[test]
fn matrix_remainder_preserves_builtin_strategy_eligibility() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::ArithmeticCongruenceStrategySingleStep;
    for (_, source) in &SOURCES60[..12] {
        let (mut run, compiler) = super::execute(source);
        let children = std::mem::take(children60(&mut run));
        let requirements = children
            .iter()
            .map(|p| crate::compile_to_lean::helper::source_subject(p).unwrap())
            .collect();
        equal60(&mut run).searched_proof = EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(
                ArithmeticCongruenceStrategySingleStep {
                    requirement_facts: requirements,
                    proof_of_requirement_facts: children,
                },
            ),
        );
        assert_eq!(
            compiler
                .compile_run(&run, "Matrix60WrongStrategy")
                .unwrap_err()
                .route,
            "ArithmeticCongruence/Constructor"
        );
    }
}
#[test]
fn matrix_remainder_preserves_distinct_operation_contracts() {
    let mut subjects = Vec::new();
    for (_, source) in &SOURCES60[..12] {
        let (mut run, _) = super::execute(source);
        subjects.push(equal60(&mut run).fact.left.clone());
    }
    for i in 0..subjects.len() {
        for j in 0..subjects.len() {
            if i != j {
                assert!(
                    crate::compile_to_lean::helper::arithmetic_constructor_pairs(
                        &subjects[i],
                        &subjects[j]
                    )
                    .is_none()
                );
            }
        }
    }
}

#[test]
fn matrix_remainder_forall_requires_complete_ordered_call_tree() {
    for (_, source) in &SOURCES60[12..] {
        for change in ["missing", "extra", "head_order"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "missing" => {
                    rebounds60(&mut run).pop();
                }
                "extra" => {
                    let (mut donor, _) = super::execute(source);
                    rebounds60(&mut run).push(rebounds60(&mut donor).pop().unwrap());
                }
                _ => {
                    let last = rebounds60(&mut run).len() - 1;
                    rebounds60(&mut run).swap(0, last);
                }
            }
            reject60(&run, &compiler);
        }
    }
}
