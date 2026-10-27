use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByStmtResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition as Definition,
    AtomicExceptEqualityFactSearchedProof as Search, BuiltinPropDefinitionProof as Builtin,
};
use crate::prelude::*;

#[test]
fn real_bound_examples_replay_original_evidence() {
    for source in [
        include_str!("../../../lean/examples/real_set_bound_citations/statement.lit"),
        include_str!("../../../lean/examples/real_set_bound_theorem/statement.lit"),
        include_str!("../../../lean/examples/real_set_bound_citations/substitution.lit"),
        include_str!("../../../lean/examples/real_empty_set_bounds/statement.lit"),
        include_str!("../../../lean/examples/real_singleton_bounds/statement.lit"),
        include_str!("../../../lean/examples/real_set_bounded_components/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "real_bounds")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn real_bounds_reject_missing_and_reordered_domain_evidence() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute("by def $is_real_upper_bound({},0)");
        compiler.compile_run(&run, "before_mutation").unwrap();
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
            &mut run.statement_results[0]
        else {
            panic!("by def")
        };
        let p = super::atomic_proof_mut(&mut p.proof);
        let PredicateDomainProof::ByRequirements(req) = &mut p.well_defined_proof.predicate_domain
        else {
            panic!("real predicate domain")
        };
        match mutation {
            0 => {
                req.pop();
            }
            1 => req.swap(0, 1),
            _ => {
                let Fact::AtomicFact(AtomicFact::SubsetFact(f)) = &mut req[0].requirement else {
                    panic!("real subset")
                };
                f.right = Obj::StandardSet(StandardSet::C);
            }
        }
        assert!(compiler.compile_run(&run, "bad_domain").is_err());
    }
}

#[test]
fn real_bounds_reject_missing_and_changed_definition_children() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute("by def $is_real_upper_bound({},0)");
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
            &mut run.statement_results[0]
        else {
            panic!("by def")
        };
        let p = super::atomic_proof_mut(&mut p.proof);
        let Search::ByDefinition(Definition::BuiltinProp(Builtin::RealSetBound(p))) =
            &mut p.searched_proof
        else {
            panic!("bound definition")
        };
        match mutation {
            0 => p.proof_of_requirement_facts.clear(),
            1 => p.requirement_facts.clear(),
            _ => {
                let Fact::ForallFact(f) = &mut p.requirement_facts[0] else {
                    panic!("forall")
                };
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(c)) =
                    &mut f.then_facts[0]
                else {
                    panic!("order")
                };
                std::mem::swap(&mut c.left, &mut c.right);
            }
        }
        assert!(compiler.compile_run(&run, "bad_definition").is_err());
    }
}

#[test]
fn real_bounds_reject_changed_inference_identity_and_direction() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferRealSetBoundFactResult, InferResult,
    };
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute("by def $is_real_upper_bound({},0)");
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
            &mut run.statement_results[0]
        else {
            panic!("by def")
        };
        let Some(InferResult::AtomicFact(InferAtomicFactResult::RealSetBoundFact(rules))) =
            &mut p.stored.infer
        else {
            panic!("infer")
        };
        let InferRealSetBoundFactResult::Definition(p) = &mut rules[0];
        if mutation == 0 {
            p.derived.clear();
        } else {
            p.source_fact_id = p.derived[0].primary_fact_id();
        }
        assert!(compiler.compile_run(&run, "bad_inference").is_err());
    }
}

#[test]
fn real_boundedness_rejects_reordered_lower_and_upper_witnesses() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/real_empty_set_bounds/statement.lit"
        ));
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
            &mut run.statement_results[4]
        else {
            panic!("bounded by def")
        };
        let p = super::atomic_proof_mut(&mut p.proof);
        let Search::ByDefinition(Definition::BuiltinProp(Builtin::RealSetBounded(p))) =
            &mut p.searched_proof
        else {
            panic!("bounded definition")
        };
        if mutation == 0 {
            p.proof_of_requirement_facts.pop();
        } else {
            p.requirement_facts.swap(0, 1);
            p.proof_of_requirement_facts.swap(0, 1);
        }
        assert!(compiler.compile_run(&run, "bad_bound_witnesses").is_err());
    }
}

#[test]
fn real_bounds_reject_unproved_or_nonreal_domains() {
    for source in [
        "forall A set: not $is_real_bounded(A)",
        "by def $is_real_upper_bound({},i)",
        "by def $is_real_upper_bound({2},1)",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_real_bound")
            .is_err());
    }
}

#[test]
fn real_bound_definition_keeps_its_set_semantics_dependency() {
    let (run, compiler) = super::execute("by def $is_real_upper_bound({2},2)");
    let lean = compiler.compile_run(&run, "set_bound_definition").unwrap();
    assert!(lean.contains("variable [_setSemantics : Litex.SetSemantics M]"));
    let (run, compiler) = super::execute(include_str!(
        "../../../lean/examples/real_set_bound_theorem/statement.lit"
    ));
    assert!(compiler
        .compile_run(&run, "set_bound_theorem")
        .unwrap()
        .contains("variable [_setSemantics : Litex.SetSemantics M]"));
}
