use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByStmtResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition as Definition,
    AtomicExceptEqualityFactSearchedProof as Search, BuiltinPropDefinitionProof as Builtin,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferResult, InferSequenceAnalysisFactResult,
};

const TRACER: &str = "have fn a(n N+) R = n\nby def $is_seq_nondecreasing(a)";
fn by_def(
    run: &mut RunLitexCodeResult,
) -> &mut crate::execute::execute_by_stmt::ExecByDefStmtSuccess {
    let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
        &mut run.statement_results[1]
    else {
        panic!("by def")
    };
    p
}
#[test]
fn sequence_analysis_examples_replay_definition_citations_and_components() {
    for source in [
        include_str!("../../../lean/examples/sequence_monotonicity/statement.lit"),
        include_str!("../../../lean/examples/sequence_property_citations/statement.lit"),
        include_str!("../../../lean/examples/sequence_range_bounds/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "sequence_analysis")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}
#[test]
fn sequence_analysis_rejects_changed_complete_domain() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(TRACER);
        let p = super::atomic_proof_mut(&mut by_def(&mut run).proof);
        let PredicateDomainProof::SequenceAnalysis(p) = &mut p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .predicate_domain
        else {
            panic!("sequence domain")
        };
        let s = &mut p.sequence_source.signature;
        match mutation {
            0 => {
                s.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            1 => s.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            _ => s.set_bound_parameters.groups.clear(),
        }
        assert!(compiler.compile_run(&run, "bad_sequence_domain").is_err());
    }
}
#[test]
fn sequence_analysis_rejects_changed_definition_contract() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(TRACER);
        let p = super::atomic_proof_mut(&mut by_def(&mut run).proof);
        let Search::ByDefinition(Definition::BuiltinProp(Builtin::SequenceAnalysis(p))) =
            &mut p.searched_proof
        else {
            panic!("sequence definition")
        };
        if mutation == 0 {
            p.proof_of_requirement_facts.clear();
        } else {
            let Fact::ForallFact(f) = &mut p.requirement_facts[0] else {
                panic!("universal")
            };
            match mutation {
                1 => {
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::N))
                }
                2 => {
                    f.typed_parameters.groups[0].params[1].id =
                        f.typed_parameters.groups[0].params[0].id
                }
                3 => f.dom_facts.clear(),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(c)) =
                        &mut f.then_facts[0]
                    else {
                        panic!("comparison")
                    };
                    std::mem::swap(&mut c.left, &mut c.right);
                }
            }
        }
        assert!(compiler
            .compile_run(&run, "bad_sequence_definition")
            .is_err());
    }
}
#[test]
fn sequence_analysis_rejects_changed_inference_identity() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(TRACER);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::SequenceAnalysisFact(rules))) =
            &mut by_def(&mut run).stored.infer
        else {
            panic!("inference")
        };
        let InferSequenceAnalysisFactResult::Definition(p) = &mut rules[0];
        if mutation == 0 {
            p.source_fact_id = p.derived[0].primary_fact_id();
        } else {
            p.derived.clear();
        }
        assert!(compiler
            .compile_run(&run, "bad_sequence_inference")
            .is_err());
    }
}
#[test]
fn sequence_analysis_rejects_reordered_and_missing_bounded_inferences() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/sequence_range_bounds/statement.lit"
        ));
        let p = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
        let Some(InferResult::AtomicFact(InferAtomicFactResult::SequenceAnalysisFact(rules))) =
            &mut p.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("bounded sequence inference")
        };
        let InferSequenceAnalysisFactResult::Definition(p) = &mut rules[0];
        match mutation {
            0 => p.derived.swap(1, 2),
            1 => p.derived.swap(3, 4),
            2 => {
                p.derived.remove(0);
            }
            _ => p.source_fact_id = p.derived[0].primary_fact_id(),
        }
        assert!(compiler.compile_run(&run, "bad_bounded_inference").is_err());
    }
}

#[test]
fn sequence_analysis_rejects_wrong_index_return_and_false_strictness() {
    for source in [
        "have fn a(n N) R=n\nby def $is_seq_nondecreasing(a)",
        "have fn a(n N+) C=i\nby def $is_seq_nondecreasing(a)",
        "have fn a(n N+) R=2\nby def $is_seq_strictly_increasing(a)",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_sequence")
            .is_err());
    }
}

#[test]
fn sequence_analysis_range_subset_replays_and_rejects_changed_certificates() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule as SubsetRule,
        AtomicExceptEqualityFactSearchProofByBuiltinRule as Rule,
    };
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/sequence_range_bounds/containment.lit"
        ));
        compiler.compile_run(&run, "range_subset").unwrap();
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = super::atomic_proof_mut(&mut p.proved_then_facts[0].verify_result);
        let Search::ByBuiltinRule(Rule::SubsetFact(SubsetRule::FunctionRangeInCodomain(p))) =
            &mut p.searched_proof
        else {
            panic!("function range codomain rule")
        };
        match mutation {
            0 => p.source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            1 => {
                p.source.signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            _ => p.source.signature.set_bound_parameters.groups.clear(),
        }
        assert!(compiler.compile_run(&run, "bad_range_certificate").is_err());
    }
}
