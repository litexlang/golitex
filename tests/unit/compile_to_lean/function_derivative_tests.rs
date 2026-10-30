use crate::execute::execute_fact_stmt::function_derivative::DerivativeConvergenceProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferHasDerivativeAtFactResult, InferResult,
};

const SELECTED: &str =
    include_str!("../../../lean/examples/derivative_candidate_selection/statement.lit");
#[test]
fn derivative_formation_selection_and_signed_citations_replay() {
    for source in [
        SELECTED,
        include_str!("../../../lean/examples/derivative_nested_objects/statement.lit"),
        include_str!("../../../lean/examples/derivative_existence_selection/statement.lit"),
        include_str!("../../../lean/examples/derivative_negative_citation/statement.lit"),
        include_str!("../../../lean/examples/derivative_differentiability_selection/statement.lit"),
        include_str!("../../../lean/examples/derivative_positive_domain_selection/statement.lit"),
        include_str!("../../../lean/examples/derivative_guarded_domain_selection/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "derivative_selection").expect(source);
    }
}
#[test]
fn derivative_definition_inferences_require_original_domain_and_store_identity() {
    for mutation in 0..4 {
        let (mut run, c) = super::execute(SELECTED);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::HasDerivativeAtFact(rules))) =
            &mut p.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("derivative inference");
        };
        let [InferHasDerivativeAtFactResult::Definition(p)] = rules.as_mut_slice() else {
            panic!("definition");
        };
        assert_eq!(p.derived.len(), 4);
        assert!(p.function_domain.is_some());
        match mutation {
            0 => p.function_domain = None,
            1 => p.derived.swap(0, 1),
            2 => p.source_fact_id = FactId::new(u64::MAX),
            _ => p.function_domain.as_mut().unwrap().domain = Obj::StandardSet(StandardSet::C),
        }
        c.compile_run(&run, "changed_derivative_inference")
            .expect_err("original inference evidence");
    }
}
#[test]
fn derivative_formation_requires_point_and_value_membership() {
    let (mut run, c) = super::execute(SELECTED);
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let FactWellDefinedProof::AtomicExceptEquality(p) = &mut p.assumed_dom_facts[0].well_defined
    else {
        panic!("atomic formation");
    };
    let PredicateDomainProof::FunctionAnalysis(p) =
        &mut p.as_detailed_mut().unwrap().predicate_domain
    else {
        panic!("function domain");
    };
    p.requirements.pop();
    c.compile_run(&run, "missing_derivative_value")
        .expect_err("both original memberships");
}
#[test]
fn derivative_selected_equality_requires_its_exact_candidate_citation() {
    let (mut run, c) = super::execute(SELECTED);
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::DerivativeSelectedValue(p),
    ) = &mut p.searched_proof
    else {
        panic!("selected derivative");
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
        p.candidate.searched_proof.as_mut()
    else {
        panic!("candidate citation");
    };
    citation.cite_fact_id = FactId::new(u64::MAX);
    c.compile_run(&run, "missing_derivative_citation")
        .expect_err("original known fact");
}
#[test]
fn derivative_wd_requires_its_original_point_membership() {
    use crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof;
    let (mut run, c) = super::execute(SELECTED);
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::Detailed(p) =
        &mut p.well_defined_proof.as_detailed_mut().unwrap().left
    else {
        panic!("selector WD");
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::DerivativeOperator(DerivativeOperatorWellDefinedProof::AtPoint(p)),
        ..
    } = p.as_mut()
    else {
        panic!("derivative WD");
    };
    let VerifyFactResult::AtomicExceptEquality(member) = p.point_in_domain.as_mut() else {
        panic!("point member");
    };
    let VerifyAtomicExceptEqualityFactResult::Success(member) = member.as_mut() else {
        panic!("success");
    };
    let AtomicFact::InFact(member) = &mut member.fact else {
        panic!("member");
    };
    member.set = Obj::StandardSet(StandardSet::C);
    c.compile_run(&run, "wrong_derivative_point_domain")
        .expect_err("exact domain");
}
#[test]
fn derivative_selection_rejects_a_changed_existence_candidate() {
    use crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof;
    let source="forall f fn(x R) R,p R:\n    exist L R st {$has_derivative_at(f,p,L)}\n    =>:\n        derivative(f,p)=derivative(f,p)";
    let (mut run, c) = super::execute(source);
    let p = super::forall_proof_mut(&mut run.statement_results[0]);
    let p = super::equality_proof_mut(&mut p.proved_then_facts[0].verify_result);
    let ObjWellDefinedProof::Detailed(p) =
        &mut p.well_defined_proof.as_detailed_mut().unwrap().left
    else {
        panic!("WD");
    };
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::DerivativeOperator(DerivativeOperatorWellDefinedProof::AtPoint(p)),
        ..
    } = p.as_mut()
    else {
        panic!("selector");
    };
    let DerivativeConvergenceProof::Existence {
        fact: Fact::ExistFact(exists),
        ..
    } = &mut p.convergence
    else {
        panic!("existence");
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::HasDerivativeAtFact(candidate)) =
        &mut exists.facts[0]
    else {
        panic!("candidate");
    };
    candidate.value = Obj::Literal(Literal::Number(Number::new("9".into())));
    c.compile_run(&run, "wrong_derivative_existence")
        .expect_err("quantified candidate value");
}
#[test]
fn derivative_without_existence_cannot_be_constructed_or_hidden_by_zero() {
    for source in [
        "have fn f(x R) R=x*x\nderivative(f,0)=0",
        "have fn f(x R) R=x*x\n0*derivative(f,0)=0",
        "have fn f(x R) R=abs(x)\n$has_derivative_at(f,0,0)",
        "have fn f(x {0}) R=x*x\n$is_differentiable_at(f,0)",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_derivative")
            .expect_err("failed source run");
    }
}

#[test]
fn derivative_definitions_and_formula_body_replay_original_results() {
    for source in [
        include_str!("../../../lean/examples/derivative_from_definition/statement.lit"),
        include_str!("../../../lean/examples/derivative_positive_from_definition/statement.lit"),
        include_str!("../../../lean/examples/differentiability_from_existence/statement.lit"),
        include_str!("../../../lean/examples/derivative_formula_body/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "derivative_definition")
            .expect(source);
    }
}
#[test]
fn derivative_definition_requires_both_ordered_original_clauses() {
    use crate::execute::execute_by_stmt::ExecByDefStmtResult;
    use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition as Definition,
        BuiltinPropDefinitionProof as Builtin,
    };
    use crate::execute::ExecDefinitionStmtResult;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/derivative_from_definition/statement.lit"
        ));
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) = &mut run.statement_results[0]
        else {
            panic!("theorem");
        };
        let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
            panic!("forall");
        };
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
            &mut body.proof_steps[0]
        else {
            panic!("by def");
        };
        let p = super::atomic_proof_mut(&mut p.proof);
        let AtomicExceptEqualityFactSearchedProof::ByDefinition(Definition::BuiltinProp(
            Builtin::HasDerivativeAt(p),
        )) = &mut p.searched_proof
        else {
            panic!("derivative definition");
        };
        match mutation {
            0 => {
                p.requirement_facts.pop();
                p.proof_of_requirement_facts.pop();
            }
            1 => p.proof_of_requirement_facts.swap(0, 1),
            _ => {
                let Fact::ExistFact(exists) = &mut p.requirement_facts[0] else {
                    panic!("interior");
                };
                let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset)) =
                    &mut exists.facts[0]
                else {
                    panic!("inclusion");
                };
                subset.right = Obj::StandardSet(StandardSet::C);
            }
        }
        compiler
            .compile_run(&run, "invalid_derivative_definition")
            .expect_err("interior and quotient with original subjects and order");
    }
}
#[test]
fn differentiability_inference_preserves_existence_then_optional_interior() {
    use crate::store_fact_and_infer::InferFunctionDifferentiableAtFactResult;
    let source =
        include_str!("../../../lean/examples/derivative_differentiability_selection/statement.lit");
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(source);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionDifferentiableAtFact(
            rules,
        ))) = &mut p.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("inference");
        };
        let [InferFunctionDifferentiableAtFactResult::Definition(p)] = rules.as_mut_slice() else {
            panic!("definition");
        };
        assert!(p.function_domain.is_some() && p.interior.is_some());
        match mutation {
            0 => p.interior = None,
            1 => p.function_domain = None,
            _ => p.function_domain.as_mut().unwrap().domain = Obj::StandardSet(StandardSet::C),
        }
        compiler
            .compile_run(&run, "changed_differentiability_inference")
            .expect_err("original optional domain and interior evidence");
    }
}
