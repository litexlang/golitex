use crate::prelude::*;

#[test]
fn coordinate_partial_keeps_point_domain_axis_and_real_value_requirements() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    for mutation in 0..3 {
        let (mut run, c) = super::execute(
            r#"# Select a coordinate partial derivative only after its original standard difference-quotient candidate is known.
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
    $has_partial_derivative_at(f,p,2,1,L)
    =>:
        partial_derivative(f,p,2,1)=L
        partial_derivative(f,p,2,1) $in R
"#,
        );
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut root.assumed_dom_facts[0].well_defined
        else {
            panic!("formation")
        };
        let PredicateDomainProof::MultivariableAnalysis(p) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("partial domains")
        };
        match mutation {
            0 => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut p.requirements[4].requirement
                else {
                    panic!("point domain")
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            1 => p.requirements.swap(4, 5),
            _ => {
                p.requirements.pop();
            }
        }
        c.compile_run(&run, "changed_partial_domain")
            .expect_err("original point/axis/real requirements");
    }
}
#[test]
fn coordinate_partial_inference_requires_original_clauses_and_producer_identity() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for mutation in 0..3 {
        let (mut run, c) = super::execute(
            r#"# Select a coordinate partial derivative only after its original standard difference-quotient candidate is known.
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
    $has_partial_derivative_at(f,p,2,1,L)
    =>:
        partial_derivative(f,p,2,1)=L
        partial_derivative(f,p,2,1) $in R
"#,
        );
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
            &mut root.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("partial inference")
        };
        let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_mut_slice() else {
            panic!("definition")
        };
        match mutation {
            0 => p.source_fact_id = FactId::new(u64::MAX),
            1 => p.function_domain = None,
            _ => p.derived.swap(0, 1),
        }
        c.compile_run(&run, "changed_partial_inference")
            .expect_err("exact source and clause order");
    }
}
#[test]
fn coordinate_partial_requires_original_coordinate_wd_child() {
    use crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof;
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof, ObjWellDefinedProofByDef,
    };
    let (mut run, c) = super::execute(
        r#"# Select a coordinate partial derivative only after its original standard difference-quotient candidate is known.
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), L R:
    $has_partial_derivative_at(f,p,2,1,L)
    =>:
        partial_derivative(f,p,2,1)=L
        partial_derivative(f,p,2,1) $in R
"#,
    );
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let equal = super::equality_proof_mut(&mut root.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::DerivativeOperator(DerivativeOperatorWellDefinedProof::Partial(p)),
        ..
    } = equal
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .left
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("partial selector")
    };
    p.stages.argument_well_defined.pop();
    c.compile_run(&run, "missing_partial_coordinate")
        .expect_err("four original argument WD proofs");
}

#[test]
fn alpha_literal_reuse_preserves_body_and_checks_the_new_occurrence_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        DetailedObjWellDefinedProof, FunctionSpaceObjWellDefinedProofByDef,
        ObjWellDefinedProofByDef,
    };
    fn literal(run: &RunLitexCodeResult, index: usize) -> &ObjWellDefinedProof {
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &run.statement_results[index]
        else {
            panic!("fact")
        };
        let VerifyFactResult::AtomicExceptEquality(p) = &p.verify_result else {
            panic!("atomic")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
            panic!("success")
        };
        &p.well_defined_proof
            .detailed_ref()
            .well_defined_of_each_parameter[0]
    }
    let source = "$is_set(fn(x R) R {x+1})\n$is_set(fn(y R) R {y+1})\n$is_set(fn(z R) R {z+2})\n";
    let (mut run, c) = super::execute(source);
    assert!(
        crate::compile_to_lean::source_position::same_wd_constructor(
            literal(&run, 0),
            literal(&run, 1)
        )
    );
    assert!(
        !crate::compile_to_lean::source_position::same_wd_constructor(
            literal(&run, 0),
            literal(&run, 2)
        )
    );
    c.compile_run(&run, "alpha_literal_reuse").unwrap();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[1] else {
        panic!("fact")
    };
    let p = super::atomic_proof_mut(&mut p.verify_result);
    let wd = &mut p
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0];
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                p,
            )),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("literal WD")
    };
    p.param_type_well_defined.clear();
    c.compile_run(&run, "missing_alpha_literal_wd")
        .expect_err("reusing a constructor does not skip original WD validation");
}
