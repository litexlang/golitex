use crate::compile_to_lean::helper::arithmetic_constructor_pairs;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::prelude::*;
pub(super) const SOURCES52:&[(&str,&str)]=&[
("abs","forall sc52a_a R,sc52a_p fn(sc52a_t R) R:\n    forall sc52a_x R:\n        abs(sc52a_x)=sc52a_p(sc52a_x)\n    =>:\n        abs(sc52a_a)=sc52a_p(sc52a_a)\n"),
("sign","forall sc52b_a R,sc52b_p fn(sc52b_t R) R:\n    forall sc52b_x R:\n        sign(sc52b_x)=sc52b_p(sc52b_x)\n    =>:\n        sign(sc52b_a)=sc52b_p(sc52b_a)\n"),
("floor","forall sc52c_a R,sc52c_p fn(sc52c_t R) R:\n    forall sc52c_x R:\n        floor(sc52c_x)=sc52c_p(sc52c_x)\n    =>:\n        floor(sc52c_a)=sc52c_p(sc52c_a)\n"),
("ceil","forall sc52d_a R,sc52d_p fn(sc52d_t R) R:\n    forall sc52d_x R:\n        ceil(sc52d_x)=sc52d_p(sc52d_x)\n    =>:\n        ceil(sc52d_a)=sc52d_p(sc52d_a)\n"),
("min","forall sc52e_a,sc52e_b R,sc52e_p fn(sc52e_t,sc52e_u R) R:\n    forall sc52e_x,sc52e_y R:\n        min(sc52e_x,sc52e_y)=sc52e_p(sc52e_x,sc52e_y)\n    =>:\n        min(sc52e_a,sc52e_b)=sc52e_p(sc52e_a,sc52e_b)\n"),
("max","forall sc52f_a,sc52f_b R,sc52f_p fn(sc52f_t,sc52f_u R) R:\n    forall sc52f_x,sc52f_y R:\n        max(sc52f_x,sc52f_y)=sc52f_p(sc52f_x,sc52f_y)\n    =>:\n        max(sc52f_a,sc52f_b)=sc52f_p(sc52f_a,sc52f_b)\n"),
("sqrt","forall sc52g_a R,sc52g_p fn(sc52g_t R) R:\n    sc52g_a>=0\n    forall sc52g_x R:\n        sc52g_x>=0\n        =>:\n            sqrt(sc52g_x)=sc52g_p(sc52g_x)\n    =>:\n        sqrt(sc52g_a)=sc52g_p(sc52g_a)\n"),
("factorial","forall sc52h_a N,sc52h_p fn(sc52h_t N) N:\n    forall sc52h_x N:\n        factorial(sc52h_x)=sc52h_p(sc52h_x)\n    =>:\n        factorial(sc52h_a)=sc52h_p(sc52h_a)\n"),
("gcd_guarded","forall sc52i_a,sc52i_b Z,sc52i_p fn(sc52i_t,sc52i_u Z) Z:\n    sc52i_a!=0\n    sc52i_b!=0\n    forall sc52i_x,sc52i_y Z:\n        sc52i_x!=0\n        sc52i_y!=0\n        =>:\n            gcd(sc52i_x,sc52i_y)=sc52i_p(sc52i_x,sc52i_y)\n    =>:\n        gcd(sc52i_a,sc52i_b)=sc52i_p(sc52i_a,sc52i_b)\n"),
("lcm_guarded","forall sc52j_a,sc52j_b Z,sc52j_p fn(sc52j_t,sc52j_u Z) Z:\n    sc52j_a!=0\n    sc52j_b!=0\n    forall sc52j_x,sc52j_y Z:\n        sc52j_x!=0\n        sc52j_y!=0\n        =>:\n            lcm(sc52j_x,sc52j_y)=sc52j_p(sc52j_x,sc52j_y)\n    =>:\n        lcm(sc52j_a,sc52j_b)=sc52j_p(sc52j_a,sc52j_b)\n"),
("log_guarded","forall sc52m_a,sc52m_b R,sc52m_p fn(sc52m_t,sc52m_u R) R:\n    sc52m_a>0\n    sc52m_a!=1\n    sc52m_b>0\n    forall sc52m_x,sc52m_y R:\n        sc52m_x>0\n        sc52m_x!=1\n        sc52m_y>0\n        =>:\n            log(sc52m_x,sc52m_y)=sc52m_p(sc52m_x,sc52m_y)\n    =>:\n        log(sc52m_a,sc52m_b)=sc52m_p(sc52m_a,sc52m_b)\n")];
#[test]
fn scalar_forall_original_typed_structure_audit() {
    for (name, source) in SOURCES52 {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(run.statement_results.last().unwrap());
        let equal = super::equality_proof(&outer.proved_then_facts.last().unwrap().verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(proof) = &equal.searched_proof else {
            panic!("original forall:{name}")
        };
        let proof = proof.as_detailed().unwrap();
        assert!(outer
            .fact
            .dom_facts
            .iter()
            .any(|f| f.fact_id() == proof.cite.fact_id));
        assert_eq!(proof.arg_match_proofs.len(), 2);
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } = proof.arg_match_proofs[0].as_detailed().unwrap()
        else {
            panic!("original scalar structure:{name}")
        };
        let (operation, pairs) = arithmetic_constructor_pairs(pattern, goal_arg).unwrap();
        assert_eq!(pairs.len(), child_matches.len());
        eprintln!("ORIGINAL52 {name} cite:{} operation:{operation} pattern:{} goal:{} children:{} bound_arguments:{}",proof.cite.fact_id.value(),pattern.ir(),goal_arg.ir(),child_matches.len(),proof.forall_parameters_match_what_args.len());
        for (index, ((a, b), child)) in pairs.iter().zip(child_matches).enumerate() {
            let DetailedForallConclusionArgMatchProof::BoundParam {
                param_id,
                pattern,
                goal_arg,
            } = child.as_detailed().unwrap()
            else {
                panic!("original first binding:{name}:{index}")
            };
            assert_eq!(pattern.ir(), a.ir());
            assert_eq!(goal_arg.ir(), b.ir());
            eprintln!(
                "ORIGINAL52 {name} child:{index} param:{} pattern:{} goal:{}",
                param_id.value(),
                pattern.ir(),
                goal_arg.ir()
            );
        }
        let requirements = proof.instantiation_requirements.as_detailed().unwrap();
        eprintln!(
            "ORIGINAL52 {name} types:{} guards:{}",
            requirements.param_type_requirements.len(),
            requirements.proof_of_dom_facts.len()
        );
        assert!(compiler
            .compile_run(&run, "Scalar52OriginalAudit")
            .unwrap()
            .contains("congrArg"));
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedSearchProofByKnownForallFact, ForallConclusionArgMatchProof,
};
fn source52(name: &str) -> &'static str {
    SOURCES52.iter().find(|(n, _)| *n == name).unwrap().1
}
fn equality52(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts.last_mut().unwrap().verify_result)
}
fn application52(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equality52(run).searched_proof else {
        panic!("original known forall")
    };
    p.as_detailed_mut().unwrap()
}
fn structure52(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        application52(run).arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
    else {
        panic!("original scalar constructor")
    };
    child_matches
}
fn reject52(
    run: &RunLitexCodeResult,
    compiler: &crate::compile_to_lean::LitexToLeanCompiler,
    name: &str,
) {
    compiler
        .compile_run(run, name)
        .expect_err("changed original matching evidence must reject");
}
#[test]
fn scalar_forall_requires_original_unary_child_count() {
    for extra in [false, true] {
        let (mut run, compiler) = super::execute(source52("abs"));
        if extra {
            let (mut other, _) = super::execute(source52("abs"));
            let added = structure52(&mut other).pop().unwrap();
            structure52(&mut run).push(added);
        } else {
            structure52(&mut run).clear();
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Scalar52Count")
                .unwrap_err()
                .route,
            "CompoundKnown/StructureArity"
        );
    }
}
#[test]
fn scalar_forall_rejects_reordered_original_binary_children() {
    let (mut run, compiler) = super::execute(source52("min"));
    structure52(&mut run).swap(0, 1);
    reject52(&run, &compiler, "Scalar52Order");
}
#[test]
fn scalar_forall_requires_captured_pattern_and_goal_subjects() {
    for goal in [false, true] {
        let (mut run, compiler) = super::execute(source52("abs"));
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern, goal_arg, ..
        } = application52(&mut run).arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
        else {
            panic!()
        };
        if goal {
            *goal_arg = pattern.clone();
        } else {
            *pattern = goal_arg.clone();
        }
        assert_eq!(
            compiler
                .compile_run(&run, "Scalar52Subjects")
                .unwrap_err()
                .route,
            "CompoundKnown/StructureSubject"
        );
    }
}
#[test]
fn scalar_forall_requires_original_bound_parameter_identity() {
    let (mut run, compiler) = super::execute(source52("abs"));
    let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
        structure52(&mut run)[0].as_detailed_mut().unwrap()
    else {
        panic!()
    };
    *param_id = IdentifierId::new(u64::MAX);
    reject52(&run, &compiler, "Scalar52Param");
}
#[test]
fn scalar_forall_preserves_ordered_instantiation_arguments() {
    let (mut run, compiler) = super::execute(source52("min"));
    application52(&mut run)
        .forall_parameters_match_what_args
        .swap(0, 1);
    reject52(&run, &compiler, "Scalar52Arguments");
}
#[test]
fn scalar_forall_requires_original_parameter_type_identity() {
    let (mut run, compiler) = super::execute(source52("sqrt"));
    let p = application52(&mut run)
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap();
    p.param_type_requirements[0].param_id = IdentifierId::new(u64::MAX);
    reject52(&run, &compiler, "Scalar52TypeId");
}
#[test]
fn scalar_forall_requires_original_domain_guards() {
    for name in ["sqrt", "gcd_guarded", "lcm_guarded", "log_guarded"] {
        let (mut run, compiler) = super::execute(source52(name));
        let p = application52(&mut run)
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap();
        assert!(!p.proof_of_dom_facts.is_empty());
        p.proof_of_dom_facts.clear();
        reject52(&run, &compiler, "Scalar52MissingGuard");
    }
}
#[test]
fn scalar_forall_requires_original_source_citation() {
    let (mut run, compiler) = super::execute(source52("abs"));
    application52(&mut run).cite.fact_id = FactId::new(u64::MAX);
    reject52(&run, &compiler, "Scalar52ForeignSource");
}
#[test]
fn scalar_forall_rejects_a_later_sibling_source() {
    let (mut run, compiler) = super::execute(&format!("{}{}", source52("abs"), source52("floor")));
    let sibling = super::forall_proof(&run.statement_results[1]);
    let id = sibling
        .fact
        .dom_facts
        .iter()
        .find(|f| matches!(f, Fact::ForallFact(_)))
        .unwrap()
        .fact_id();
    application52(&mut run).cite.fact_id = id;
    reject52(&run, &compiler, "Scalar52SiblingSource");
}
#[test]
fn scalar_forall_requires_both_original_goal_formations() {
    let (mut run, compiler) = super::execute(source52("abs"));
    let wd = equality52(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut wd.left, &mut wd.right);
    reject52(&run, &compiler, "Scalar52GoalWd");
}

const COMPOSITION52:&str="forall sc51l_a,sc51l_b R,sc51l_p,sc51l_q fn(sc51l_t R) R:\n    forall sc51l_x R:\n        abs(sc51l_x)=sc51l_p(sc51l_x)\n    forall sc51l_y R:\n        abs(sc51l_y)=sc51l_q(sc51l_y)\n    =>:\n        abs(sc51l_a)=sc51l_p(sc51l_a)\n        abs(sc51l_b)=sc51l_q(sc51l_b)\n        abs(sc51l_a*sc51l_b)=sc51l_p(sc51l_a)*sc51l_q(sc51l_b)\n";
#[test]
fn scalar_forall_composes_explicit_instances_stores_and_abs_factor_strategy() {
    let (run, compiler) = super::execute(COMPOSITION52);
    let outer = super::forall_proof(run.statement_results.last().unwrap());
    assert_eq!(outer.proved_then_facts.len(), 3);
    for result in &outer.proved_then_facts[..2] {
        assert!(matches!(
            super::equality_proof(&result.verify_result).searched_proof,
            EqualFactSearchedProof::ByKnownForallFact(_)
        ));
    }
    let final_equal = super::equality_proof(&outer.proved_then_facts[2].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::AbsProductFromFactors(p),
    ) = &final_equal.searched_proof
    else {
        panic!("original factor composition")
    };
    for (index, child) in p.proof_of_requirement_facts.iter().enumerate() {
        let child = super::equality_proof(child);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
        ) = &child.searched_proof
        else {
            panic!()
        };
        assert_eq!(path.path.len(), 1);
        assert_eq!(
            path.path[0].2,
            crate::compile_to_lean::helper::source_subject(
                &outer.proved_then_facts[index].verify_result
            )
            .unwrap()
            .fact_id()
        );
    }
    let lean = compiler
        .compile_run(&run, "Scalar52StoredComposition")
        .unwrap();
    assert!(lean.contains("Litex.absProduct"));
    assert_eq!(
        lean,
        compiler
            .compile_run(&run, "Scalar52StoredComposition")
            .unwrap()
    );
}
