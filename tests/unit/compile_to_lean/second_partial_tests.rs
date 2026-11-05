use crate::prelude::*;

#[test]
fn second_partial_keeps_point_domain_axis_and_real_value_requirements() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    for mutation in 0..4 {
        let (mut run, c) = super::execute(
            r#"# Retain a certified second partial and its local first-derivative witness.
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d R:
    $has_second_partial_derivative_at(f,p,2,1,2,d)
    =>:
        $has_second_partial_derivative_at(f,p,2,1,2,d)
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
            2 => p.requirements.swap(5, 6),
            _ => {
                p.requirements.pop();
            }
        }
        c.compile_run(&run, "changed_partial_domain")
            .expect_err("original point/axis/real requirements");
    }
}
#[test]
fn second_partial_inference_requires_original_clauses_and_producer_identity() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
    };
    for mutation in 0..3 {
        let (mut run, c) = super::execute(
            r#"# Retain a certified second partial and its local first-derivative witness.
forall f fn(x cart_n(R,2)) R, p cart_n(R,2), d R:
    $has_second_partial_derivative_at(f,p,2,1,2,d)
    =>:
        $has_second_partial_derivative_at(f,p,2,1,2,d)
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
