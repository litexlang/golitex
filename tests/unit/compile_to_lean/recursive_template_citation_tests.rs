use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::{
    ExecDefTemplateStmtResult, ExecDefTemplateStmtSuccessResult, ExecHaveFnByInducStmtResult,
    InducCaseBodySuccess,
};
use crate::prelude::*;

const SOURCES: &[&str] = &[
    r#"# Evaluate a recursive sequence by citing its published equation and matching its predecessor argument.
template<S set>:
    have fn recursive_zero(n N) N by induc n from 0:
        case n = 0: 0
        case n >= 1: recursive_zero(n - 1)
\recursive_zero<R>(0) = 0

\recursive_zero<R>(1) = \recursive_zero<R>(0) = 0
"#,
    r#"# Evaluate a constant recursive real sequence through its published case equations.
template<a R>:
    have fn repeat_seed(n N) R by induc n from 0:
        case n = 0: a
        case n >= 1: repeat_seed(n - 1)
\repeat_seed<2>(0) = 2
\repeat_seed<2>(1) = \repeat_seed<2>(0) = 2
forall a R:
    \repeat_seed<a>(0) = a
    \repeat_seed<a>(1) = \repeat_seed<a>(0) = a
"#,
    r#"# Evaluate a recursive reciprocal sequence while retaining its nonzero seed condition.
template<a R: a != 0,>:
    have fn inverse_repeat(n N) R by induc n from 0:
        case n = 0: 1 / a
        case n >= 1: inverse_repeat(n - 1)
\inverse_repeat<2>(0) = 1 / 2
\inverse_repeat<2>(1) = \inverse_repeat<2>(0) = 1 / 2
forall a R:
    a != 0
    =>:
        \inverse_repeat<a>(0) = 1 / a
        \inverse_repeat<a>(1) = \inverse_repeat<a>(0) = 1 / a
"#,
    r#"# Cite the published successor equation of a recursive running total.
template<a R>:
    have fn sum_seed(n N) R by induc n from 0:
        case n = 0: 0
        case n >= 1: sum_seed(n - 1) + a
\sum_seed<3>(0) = 0
\sum_seed<3>(1) = \sum_seed<3>(0) + 3 = 3
\sum_seed<3>(2) = \sum_seed<3>(1) + 3 = 6
"#,
];

fn template(run: &mut RunLitexCodeResult) -> &mut ExecDefTemplateStmtSuccessResult {
    match &mut run.statement_results[0] {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
            ExecDefTemplateStmtResult::Success(p),
        )) => p,
        _ => panic!("checked recursive template"),
    }
}

fn application(run: &mut RunLitexCodeResult) -> &mut SearchProofByKnownForallFact {
    let fact = super::fact_statement_mut(&mut run.statement_results[2]);
    let VerifyFactResult::ChainFact(chain) = &mut fact.verify_result else {
        panic!("chain")
    };
    let VerifyChainFactResult::Success(chain) = chain.as_mut() else {
        panic!("checked chain")
    };
    let equality = super::equality_proof_mut(&mut chain.adjacent[0]);
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equality.searched_proof else {
        panic!("the source selected known-forall, not direct unfolding")
    };
    p
}

#[test]
fn recursive_template_equations_keep_the_selected_citation_route() {
    for (index, source) in SOURCES.iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        // The natural tracer specifically takes known-forall matching. Other
        // fixtures may also use their recorded direct-unfold branches.
        if index == 0 {
            let id = application(&mut run).detailed_ref().cite.fact_id;
            assert!(template(&mut run)
                .definition_facts
                .iter()
                .any(|p| p.store_and_infer.primary_fact_id() == id));
        }
        let lean = compiler
            .compile_run(&run, "recursive_citation")
            .expect(source);
        assert!(
            lean.len() < 200_000,
            "Constructor reuse must keep this small recursive fixture bounded."
        );
        assert_eq!(
            lean,
            compiler.compile_run(&run, "recursive_citation").unwrap()
        );
    }
}

#[test]
fn recursive_template_citation_requires_original_matching_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let p = application(&mut run).as_detailed_mut().unwrap();
        match mutation {
            0 => p.cite.fact_id = FactId::new(u64::MAX),
            1 => p.forall_parameters_match_what_args.reverse(),
            2 => p
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts
                .clear(),
            3 => p.arg_match_proofs.clear(),
            4 => p
                .forall_parameters_match_what_args
                .pop()
                .map(|_| ())
                .unwrap(),
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_citation")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn recursive_template_citation_requires_original_prefix_call_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SOURCES[0]);
        let p = template(&mut run);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
            ExecHaveFnByInducStmtResult::Success(body),
        )) = p.body.as_mut()
        else {
            panic!()
        };
        let InducCaseBodySuccess::EqualTo { well_defined, .. } =
            &mut body.case_checks.cases[1].body
        else {
            panic!()
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = well_defined.as_detailed_success_mut().unwrap().unwrap()
        else {
            panic!()
        };
        match mutation {
            0 => call.requirement_fact_verified.clear(),
            1 => call.requirement_fact_verified.swap(1, 2),
            2 => call.child_obj_well_defined.clear(),
            3 | 4 => {
                let Some(FnObjDomainFnSetEvidence::InFunctionSet {
                    fact_id, fn_set, ..
                }) = &mut call.domain_fn_set
                else {
                    panic!()
                };
                if mutation == 3 {
                    *fact_id = FactId::new(u64::MAX);
                } else {
                    fn_set.dom_facts.clear();
                }
            }
            _ => unreachable!(),
        }
        compiler
            .compile_run(&run, "bad_prefix_call")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn recursive_template_citation_does_not_expose_future_publications() {
    let (mut run, _) = super::execute(SOURCES[0]);
    let id = application(&mut run).detailed_ref().cite.fact_id;
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let after = SourcePosition {
        before: 1,
        ..before
    };
    assert!(before.visible_template_publication(id).is_none());
    assert!(after.visible_template_publication(id).is_some());
}
