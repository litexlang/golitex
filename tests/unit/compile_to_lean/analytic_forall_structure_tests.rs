use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult};
use crate::prelude::*;
pub(super) const SOURCES53:&[(&str,&str)]=&[
("arccos_guarded","forall sc53t_a R,sc53t_p fn(sc53t_t R) R:\n    -1<=sc53t_a\n    sc53t_a<=1\n    forall sc53t_x R:\n        -1<=sc53t_x\n        sc53t_x<=1\n        =>:\n            arccos(sc53t_x)=sc53t_p(sc53t_x)\n    =>:\n        arccos(sc53t_a)=sc53t_p(sc53t_a)\n"),
("arccot","forall sc53i_a R,sc53i_p fn(sc53i_t R) R:\n    forall sc53i_x R:\n        arccot(sc53i_x)=sc53i_p(sc53i_x)\n    =>:\n        arccot(sc53i_a)=sc53i_p(sc53i_a)\n"),
("arcsin_guarded","forall sc53s_a R,sc53s_p fn(sc53s_t R) R:\n    -1<=sc53s_a\n    sc53s_a<=1\n    forall sc53s_x R:\n        -1<=sc53s_x\n        sc53s_x<=1\n        =>:\n            arcsin(sc53s_x)=sc53s_p(sc53s_x)\n    =>:\n        arcsin(sc53s_a)=sc53s_p(sc53s_a)\n"),
("arctan","forall sc53h_a R,sc53h_p fn(sc53h_t R) R:\n    forall sc53h_x R:\n        arctan(sc53h_x)=sc53h_p(sc53h_x)\n    =>:\n        arctan(sc53h_a)=sc53h_p(sc53h_a)\n"),
("complex_abs","forall sc53n_a C,sc53n_p fn(sc53n_t C) R:\n    forall sc53n_x C:\n        C_abs(sc53n_x)=sc53n_p(sc53n_x)\n    =>:\n        C_abs(sc53n_a)=sc53n_p(sc53n_a)\n"),
("conjugate","forall sc53k_a C,sc53k_p fn(sc53k_t C) C:\n    forall sc53k_x C:\n        conj(sc53k_x)=sc53k_p(sc53k_x)\n    =>:\n        conj(sc53k_a)=sc53k_p(sc53k_a)\n"),
("cos","forall sc53b_a R,sc53b_p fn(sc53b_t R) R:\n    forall sc53b_x R:\n        cos(sc53b_x)=sc53b_p(sc53b_x)\n    =>:\n        cos(sc53b_a)=sc53b_p(sc53b_a)\n"),
("cosh","forall sc53e_a R,sc53e_p fn(sc53e_t R) R:\n    forall sc53e_x R:\n        cosh(sc53e_x)=sc53e_p(sc53e_x)\n    =>:\n        cosh(sc53e_a)=sc53e_p(sc53e_a)\n"),
("cot_guarded","forall sc53p_a R,sc53p_p fn(sc53p_t R) R:\n    sin(sc53p_a)!=0\n    forall sc53p_x R:\n        sin(sc53p_x)!=0\n        =>:\n            cot(sc53p_x)=sc53p_p(sc53p_x)\n    =>:\n        cot(sc53p_a)=sc53p_p(sc53p_a)\n"),
("coth_guarded","forall sc53u_a R,sc53u_p fn(sc53u_t R) R:\n    sc53u_a!=0\n    forall sc53u_x R:\n        sc53u_x!=0\n        =>:\n            coth(sc53u_x)=sc53u_p(sc53u_x)\n    =>:\n        coth(sc53u_a)=sc53u_p(sc53u_a)\n"),
("csc_guarded","forall sc53r_a R,sc53r_p fn(sc53r_t R) R:\n    sin(sc53r_a)!=0\n    forall sc53r_x R:\n        sin(sc53r_x)!=0\n        =>:\n            csc(sc53r_x)=sc53r_p(sc53r_x)\n    =>:\n        csc(sc53r_a)=sc53r_p(sc53r_a)\n"),
("csch_guarded","forall sc53v_a R,sc53v_p fn(sc53v_t R) R:\n    sc53v_a!=0\n    forall sc53v_x R:\n        sc53v_x!=0\n        =>:\n            csch(sc53v_x)=sc53v_p(sc53v_x)\n    =>:\n        csch(sc53v_a)=sc53v_p(sc53v_a)\n"),
("exp","forall sc53c_a R,sc53c_p fn(sc53c_t R) R:\n    forall sc53c_x R:\n        exp(sc53c_x)=sc53c_p(sc53c_x)\n    =>:\n        exp(sc53c_a)=sc53c_p(sc53c_a)\n"),
("imag_part","forall sc53m_a C,sc53m_p fn(sc53m_t C) R:\n    forall sc53m_x C:\n        img(sc53m_x)=sc53m_p(sc53m_x)\n    =>:\n        img(sc53m_a)=sc53m_p(sc53m_a)\n"),
("ln_guarded","forall sc53j_a R,sc53j_p fn(sc53j_t R) R:\n    sc53j_a>0\n    forall sc53j_x R:\n        sc53j_x>0\n        =>:\n            ln(sc53j_x)=sc53j_p(sc53j_x)\n    =>:\n        ln(sc53j_a)=sc53j_p(sc53j_a)\n"),
("real_part","forall sc53l_a C,sc53l_p fn(sc53l_t C) R:\n    forall sc53l_x C:\n        re(sc53l_x)=sc53l_p(sc53l_x)\n    =>:\n        re(sc53l_a)=sc53l_p(sc53l_a)\n"),
("sec_guarded","forall sc53q_a R,sc53q_p fn(sc53q_t R) R:\n    cos(sc53q_a)!=0\n    forall sc53q_x R:\n        cos(sc53q_x)!=0\n        =>:\n            sec(sc53q_x)=sc53q_p(sc53q_x)\n    =>:\n        sec(sc53q_a)=sc53q_p(sc53q_a)\n"),
("sech","forall sc53g_a R,sc53g_p fn(sc53g_t R) R:\n    forall sc53g_x R:\n        sech(sc53g_x)=sc53g_p(sc53g_x)\n    =>:\n        sech(sc53g_a)=sc53g_p(sc53g_a)\n"),
("sin","forall sc53a_a R,sc53a_p fn(sc53a_t R) R:\n    forall sc53a_x R:\n        sin(sc53a_x)=sc53a_p(sc53a_x)\n    =>:\n        sin(sc53a_a)=sc53a_p(sc53a_a)\n"),
("sinh","forall sc53d_a R,sc53d_p fn(sc53d_t R) R:\n    forall sc53d_x R:\n        sinh(sc53d_x)=sc53d_p(sc53d_x)\n    =>:\n        sinh(sc53d_a)=sc53d_p(sc53d_a)\n"),
("tan_guarded","forall sc53o_a R,sc53o_p fn(sc53o_t R) R:\n    cos(sc53o_a)!=0\n    forall sc53o_x R:\n        cos(sc53o_x)!=0\n        =>:\n            tan(sc53o_x)=sc53o_p(sc53o_x)\n    =>:\n        tan(sc53o_a)=sc53o_p(sc53o_a)\n"),
("tanh","forall sc53f_a R,sc53f_p fn(sc53f_t R) R:\n    forall sc53f_x R:\n        tanh(sc53f_x)=sc53f_p(sc53f_x)\n    =>:\n        tanh(sc53f_a)=sc53f_p(sc53f_a)\n")];
fn original_unary53(object: &Obj) -> (&'static str, &Obj) {
    match object {
        Obj::TrigOperator(TrigOperator::Sin(p)) => ("TrigOperator::Sin", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Cos(p)) => ("TrigOperator::Cos", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Tan(p)) => ("TrigOperator::Tan", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Cot(p)) => ("TrigOperator::Cot", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Sec(p)) => ("TrigOperator::Sec", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Csc(p)) => ("TrigOperator::Csc", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Arcsin(p)) => ("TrigOperator::Arcsin", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Arccos(p)) => ("TrigOperator::Arccos", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Arctan(p)) => ("TrigOperator::Arctan", p.arg.as_ref()),
        Obj::TrigOperator(TrigOperator::Arccot(p)) => ("TrigOperator::Arccot", p.arg.as_ref()),
        Obj::HyperbolicOperator(HyperbolicOperator::Sinh(p)) => {
            ("HyperbolicOperator::Sinh", p.arg.as_ref())
        }
        Obj::HyperbolicOperator(HyperbolicOperator::Cosh(p)) => {
            ("HyperbolicOperator::Cosh", p.arg.as_ref())
        }
        Obj::HyperbolicOperator(HyperbolicOperator::Tanh(p)) => {
            ("HyperbolicOperator::Tanh", p.arg.as_ref())
        }
        Obj::HyperbolicOperator(HyperbolicOperator::Coth(p)) => {
            ("HyperbolicOperator::Coth", p.arg.as_ref())
        }
        Obj::HyperbolicOperator(HyperbolicOperator::Sech(p)) => {
            ("HyperbolicOperator::Sech", p.arg.as_ref())
        }
        Obj::HyperbolicOperator(HyperbolicOperator::Csch(p)) => {
            ("HyperbolicOperator::Csch", p.arg.as_ref())
        }
        Obj::ExpLogOperator(ExpLogOperator::Exp(p)) => ("ExpLogOperator::Exp", p.arg.as_ref()),
        Obj::ExpLogOperator(ExpLogOperator::Ln(p)) => ("ExpLogOperator::Ln", p.arg.as_ref()),
        Obj::ComplexOperator(ComplexOperator::Conjugate(p)) => {
            ("ComplexOperator::Conjugate", p.arg.as_ref())
        }
        Obj::ComplexOperator(ComplexOperator::RealPart(p)) => {
            ("ComplexOperator::RealPart", p.arg.as_ref())
        }
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(p)) => {
            ("ComplexOperator::ImaginaryPart", p.arg.as_ref())
        }
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(p)) => {
            ("ComplexOperator::ComplexAbs", p.arg.as_ref())
        }
        _ => panic!("original analytic unary constructor"),
    }
}
#[test]
fn analytic_forall_original_typed_structure_audit() {
    for (name, source) in SOURCES53 {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(run.statement_results.last().unwrap());
        let equal = super::equality_proof(&outer.proved_then_facts.last().unwrap().verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
            panic!("original known forall:{name}")
        };
        let p = p.as_detailed().unwrap();
        assert_eq!(p.arg_match_proofs.len(), 2);
        assert!(outer
            .fact
            .dom_facts
            .iter()
            .any(|f| f.fact_id() == p.cite.fact_id));
        let DetailedForallConclusionArgMatchProof::ByStructure {
            pattern,
            goal_arg,
            child_matches,
        } = p.arg_match_proofs[0].as_detailed().unwrap()
        else {
            panic!("original structure:{name}")
        };
        let (a, x) = original_unary53(pattern);
        let (b, y) = original_unary53(goal_arg);
        assert_eq!(a, b);
        assert_eq!(child_matches.len(), 1);
        let DetailedForallConclusionArgMatchProof::BoundParam {
            param_id,
            pattern,
            goal_arg,
        } = child_matches[0].as_detailed().unwrap()
        else {
            panic!("original first binding:{name}")
        };
        assert_eq!(pattern.ir(), x.ir());
        assert_eq!(goal_arg.ir(), y.ir());
        let req = p.instantiation_requirements.as_detailed().unwrap();
        eprintln!("ORIGINAL53 {name} cite:{} constructor:{a} child_param:{} pattern:{} goal:{} types:{} guards:{}",p.cite.fact_id.value(),param_id.value(),x.ir(),y.ir(),req.param_type_requirements.len(),req.proof_of_dom_facts.len());
        assert!(compiler
            .compile_run(&run, "Analytic53OriginalAudit")
            .unwrap()
            .contains("congrArg"));
    }
}

#[test]
fn analytic_direct_original_matching_audit() {
    for(name,source)in &[
("direct_conjugate","forall sc53x_a,sc53x_b C:\n    sc53x_a=sc53x_b\n    =>:\n        conj(sc53x_a)=conj(sc53x_b)\n"),
("direct_exp","forall sc53y_a,sc53y_b R:\n    sc53y_a=sc53y_b\n    =>:\n        exp(sc53y_a)=exp(sc53y_b)\n"),
("direct_sin","forall sc53w_a,sc53w_b R:\n    sc53w_a=sc53w_b\n    =>:\n        sin(sc53w_a)=sin(sc53w_b)\n")]{
  let(run,compiler)=super::execute(source);let outer=super::forall_proof(run.statement_results.last().unwrap());let equal=super::equality_proof(&outer.proved_then_facts[0].verify_result);let EqualFactSearchedProof::ByMatchingOneArgByOne(p)=&equal.searched_proof else{panic!("original direct matcher:{name}")};assert_eq!(p.corresponding_arg_equal_proofs.len(),1);let child=super::equality_proof(&p.corresponding_arg_equal_proofs[0]);let(_,a)=original_unary53(&equal.fact.left);let(_,b)=original_unary53(&equal.fact.right);assert_eq!(child.fact.left.ir(),a.ir());assert_eq!(child.fact.right.ir(),b.ir());let EqualFactSearchedProof::ByEquivalenceClass(EqualFactSearchedProofByEquivalenceClass::KnownPath(path))=&child.searched_proof else{panic!("original direct premise")};assert_eq!(path.path.len(),1);assert_eq!(path.path[0].2,outer.fact.dom_facts[0].fact_id());eprintln!("DIRECT53 {name} citation:{} child:{}",path.path[0].2.value(),child.fact.ir());assert!(compiler.compile_run(&run,"Analytic53OriginalDirect").unwrap().contains("congrArg"));
 }
}

const ATOMIC_SIGNED53:&str="forall sc53atomic_S set:\n    forall sc53atomic_x R:\n        sin(sc53atomic_x) $in sc53atomic_S\n    =>:\n        sin(-1) $in sc53atomic_S\n";
#[test]
fn analytic_atomic_signed_original_structure_audit() {
    let (mut run, compiler) = super::execute(ATOMIC_SIGNED53);
    let outer = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let atomic = super::atomic_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(p) = &atomic.searched_proof else {
        panic!("original atomic forall")
    };
    let p = p.as_detailed().unwrap();
    let DetailedForallConclusionArgMatchProof::ByStructure {
        pattern,
        goal_arg,
        child_matches,
    } = p.arg_match_proofs[0].as_detailed().unwrap()
    else {
        panic!("original signed analytic structure")
    };
    assert_eq!(child_matches.len(), 1);
    let (_, a) = original_unary53(pattern);
    let (_, b) = original_unary53(goal_arg);
    let DetailedForallConclusionArgMatchProof::BoundParam {
        pattern, goal_arg, ..
    } = child_matches[0].as_detailed().unwrap()
    else {
        panic!()
    };
    assert_eq!(pattern.ir(), a.ir());
    assert_eq!(goal_arg.ir(), b.ir());
    eprintln!(
        "SIGNED53 cite:{} source:{} goal:{}",
        p.cite.fact_id.value(),
        a.ir(),
        b.ir()
    );
    assert!(compiler
        .compile_run(&run, "Analytic53SignedOriginal")
        .unwrap()
        .contains("congrArg"));
}

const EVAL_CONJ53: &str = "have sc53eval_a R = 0\neval conj(sc53eval_a)\n";
#[test]
fn analytic_eval_original_cited_conjugate_rewrite_audit() {
    for source in [
        EVAL_CONJ53,
        "have sc53qeval_a R = -3/2\neval conj(sc53qeval_a)\n",
        "have sc53qeval_a R = -3/2\neval conj(2 * sc53qeval_a + 1)\n",
    ] {
        let (run, compiler) = super::execute(source);
        let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
            &run.statement_results[1]
        else {
            panic!("original eval success")
        };
        assert!(matches!(
            p.source_object,
            Obj::ComplexOperator(ComplexOperator::Conjugate(_))
        ));
        assert!(matches!(
            p.rewritten_object,
            Obj::ComplexOperator(ComplexOperator::Conjugate(_))
        ));
        assert_eq!(p.cited_equal_fact_ids.len(), 1);
        assert!(
            p.function_evaluations.is_empty()
                && p.aggregate_evaluations.is_empty()
                && p.matrix_scalar_evaluations.is_empty()
                && p.algo_evaluations.is_empty()
        );
        eprintln!(
            "EVAL53 source:{} rewritten:{} value:{} citations:{:?}",
            p.source_object.ir(),
            p.rewritten_object.ir(),
            p.evaluated_object.ir(),
            p.cited_equal_fact_ids
                .iter()
                .map(|id| id.value())
                .collect::<Vec<_>>()
        );
        assert!(compiler
            .compile_run(&run, "Analytic53EvalOriginal")
            .unwrap()
            .contains("Litex.complexUnaryValue_number"));
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedSearchProofByKnownForallFact, ForallConclusionArgMatchProof,
};
fn source53(name: &str) -> &'static str {
    SOURCES53.iter().find(|(n, _)| *n == name).unwrap().1
}
fn equality53(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts.last_mut().unwrap().verify_result)
}
fn application53(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equality53(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn structure53(run: &mut RunLitexCodeResult) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } =
        application53(run).arg_match_proofs[0]
            .as_detailed_mut()
            .unwrap()
    else {
        panic!()
    };
    child_matches
}
fn reject53(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Analytic53ChangedEvidence")
        .expect_err("changed original evidence must reject");
}
#[test]
fn analytic_forall_requires_exact_original_unary_child_count() {
    for (_, source) in SOURCES53 {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut other, _) = super::execute(source);
                let added = structure53(&mut other).pop().unwrap();
                structure53(&mut run).push(added);
            } else {
                structure53(&mut run).clear();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Analytic53Count")
                    .unwrap_err()
                    .route,
                "CompoundKnown/StructureArity"
            );
        }
    }
}
#[test]
fn analytic_forall_requires_original_subjects_and_constructor() {
    for name in ["sin", "ln_guarded", "conjugate"] {
        for goal in [false, true] {
            let (mut run, compiler) = super::execute(source53(name));
            let DetailedForallConclusionArgMatchProof::ByStructure {
                pattern, goal_arg, ..
            } = application53(&mut run).arg_match_proofs[0]
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
            reject53(&run, &compiler);
        }
    }
}
#[test]
fn analytic_forall_requires_original_bound_parameter_and_type_identity() {
    for name in ["sin", "ln_guarded", "complex_abs"] {
        for type_id in [false, true] {
            let (mut run, compiler) = super::execute(source53(name));
            if type_id {
                application53(&mut run)
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements[0]
                    .param_id = IdentifierId::new(u64::MAX);
            } else {
                let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                    structure53(&mut run)[0].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                *param_id = IdentifierId::new(u64::MAX);
            }
            reject53(&run, &compiler);
        }
    }
}
#[test]
fn analytic_forall_requires_original_domain_guards() {
    for name in [
        "ln_guarded",
        "tan_guarded",
        "cot_guarded",
        "sec_guarded",
        "csc_guarded",
        "coth_guarded",
        "csch_guarded",
        "arcsin_guarded",
        "arccos_guarded",
    ] {
        let (mut run, compiler) = super::execute(source53(name));
        let p = application53(&mut run)
            .instantiation_requirements
            .as_detailed_mut()
            .unwrap();
        assert!(!p.proof_of_dom_facts.is_empty());
        p.proof_of_dom_facts.clear();
        reject53(&run, &compiler);
    }
}
#[test]
fn analytic_forall_rejects_foreign_and_later_sibling_sources() {
    let (mut run, compiler) = super::execute(source53("sin"));
    application53(&mut run).cite.fact_id = FactId::new(u64::MAX);
    reject53(&run, &compiler);
    let (mut run, compiler) = super::execute(&format!("{}{}", source53("sin"), source53("cos")));
    let sibling = super::forall_proof(&run.statement_results[1]);
    let id = sibling
        .fact
        .dom_facts
        .iter()
        .find(|f| matches!(f, Fact::ForallFact(_)))
        .unwrap()
        .fact_id();
    application53(&mut run).cite.fact_id = id;
    reject53(&run, &compiler);
}
#[test]
fn analytic_forall_requires_both_original_goal_formations() {
    let (mut run, compiler) = super::execute(source53("sin"));
    let wd = equality53(&mut run)
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut wd.left, &mut wd.right);
    reject53(&run, &compiler);
}
const DIRECT_SIN53: &str =
    "forall sc53w_a,sc53w_b R:\n    sc53w_a=sc53w_b\n    =>:\n        sin(sc53w_a)=sin(sc53w_b)\n";
#[test]
fn analytic_direct_requires_original_child_count_subjects_citation_and_wd() {
    for change in ["missing", "extra", "subject", "citation", "wd"] {
        let (mut run, compiler) = super::execute(DIRECT_SIN53);
        let equal = equality53(&mut run);
        let EqualFactSearchedProof::ByMatchingOneArgByOne(p) = &mut equal.searched_proof else {
            panic!()
        };
        match change {
            "missing" => p.corresponding_arg_equal_proofs.clear(),
            "extra" => {
                let (mut other, _) = super::execute(DIRECT_SIN53);
                let EqualFactSearchedProof::ByMatchingOneArgByOne(q) =
                    &mut equality53(&mut other).searched_proof
                else {
                    panic!()
                };
                p.corresponding_arg_equal_proofs
                    .push(q.corresponding_arg_equal_proofs.pop().unwrap());
            }
            _ => {
                let child = super::equality_proof_mut(&mut p.corresponding_arg_equal_proofs[0]);
                match change {
                    "subject" => child.fact.left = child.fact.right.clone(),
                    "citation" => {
                        let EqualFactSearchedProof::ByEquivalenceClass(
                            EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
                        ) = &mut child.searched_proof
                        else {
                            panic!()
                        };
                        path.path[0].2 = FactId::new(u64::MAX);
                    }
                    "wd" => {
                        let wd = child.well_defined_proof.as_detailed_mut().unwrap();
                        std::mem::swap(&mut wd.left, &mut wd.right);
                    }
                    _ => unreachable!(),
                }
            }
        }
        reject53(&run, &compiler);
    }
}
fn eval53(run: &mut RunLitexCodeResult) -> &mut crate::execute::ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[1]
    else {
        panic!()
    };
    p
}
#[test]
fn analytic_eval_requires_original_citation_rewrite_and_result() {
    for change in [
        "missing",
        "foreign",
        "self",
        "duplicate",
        "rewrite",
        "value",
    ] {
        let (mut run, compiler) = super::execute(EVAL_CONJ53);
        let p = eval53(&mut run);
        match change {
            "missing" => p.cited_equal_fact_ids.clear(),
            "foreign" => p.cited_equal_fact_ids[0] = FactId::new(u64::MAX),
            "self" => p.cited_equal_fact_ids[0] = p.evaluated_equal_fact.fact_id,
            "duplicate" => p.cited_equal_fact_ids.push(p.cited_equal_fact_ids[0]),
            "rewrite" => p.rewritten_object = p.source_object.clone(),
            "value" => {
                let wrong = Obj::Literal(Literal::Number(Number::new("1".into())));
                p.evaluated_object = wrong.clone();
                p.evaluated_equal_fact.right = wrong;
            }
            _ => unreachable!(),
        }
        reject53(&run, &compiler);
    }
    let (mut run, compiler) = super::execute(EVAL_CONJ53);
    run.statement_results.swap(0, 1);
    reject53(&run, &compiler);
}
#[test]
fn analytic_eval_keeps_nonreal_conjugate_result_boundary_explicit() {
    let (run, compiler) = super::execute("eval conj(i)\n");
    let err = compiler
        .compile_run(&run, "Analytic53Nonreal")
        .expect_err("exact real-rational helper cannot replay a nonreal output");
    assert!(err.route.starts_with("Eval/"), "{err:?}");
}
