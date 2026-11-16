use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferHasDerivativeAtFactResult, InferResult,
};

const SELECTED: &str = r#"# A proved derivative candidate determines the selected real derivative.
forall f fn(x R) R, p, L R:
    $has_derivative_at(f, p, L)
    =>:
        derivative(f, p) = L
        L = derivative(f, p)
        derivative(f, p) $in R
"#;
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
fn derivative_automatic_differentiability_replays_forall_and_direct_bodies() {
    use crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof;
    let forall_source = "forall f fn(x R) R:\n    forall x R:\n        $diff_at(f, x)\n    =>:\n        deriv(f, 0) = deriv(f, 0)\n";
    let (run, compiler) = super::execute(forall_source);
    let output = compiler
        .compile_run(&run, "automatic_differentiability")
        .expect("shared differentiability evidence from a known forall replays");
    assert!(output.contains("Litex.DerivativeObj.mk"));
    assert_eq!(
        output,
        compiler
            .compile_run(&run, "automatic_differentiability")
            .unwrap()
    );

    let direct_source = "have fn square(x R) R = x^2\nderiv(square, 3) = 6\nhave fn comp(x R) R = square(3*x + 1)\n$has_deriv_at(square, 3*2 + 1, 14)\nderiv(comp, 2) = 42\n";
    let (direct_run, direct_compiler) = super::execute(direct_source);
    let direct_output = direct_compiler
        .compile_run(&direct_run, "direct_derivative_value")
        .expect("direct polynomial and composite derivative values replay cleanly");
    assert!(direct_output.contains("Litex.DerivativeObj.mk"));

    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(forall_source);
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let equal = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let ObjWellDefinedProofByDef::DerivativeOperator(
            DerivativeOperatorWellDefinedProof::AtPoint(derivative),
        ) = equal
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .left
            .by_def_mut()
            .expect("derivative definition proof")
        else {
            panic!("derivative definition")
        };
        let atomic = super::atomic_proof_mut(&mut derivative.differentiability);
        let AtomicFact::FunctionDifferentiableAtFact(fact) = &mut atomic.fact else {
            panic!("differentiability subject")
        };
        let wrong = Obj::StandardSet(StandardSet::R);
        match mutation {
            0 => fact.function = wrong,
            _ => fact.point = wrong,
        }
        compiler
            .compile_run(&run, "changed_differentiability")
            .expect_err("differentiability must prove the exact function and point");
    }
}
#[test]
fn derivative_selection_rejects_a_changed_existence_candidate() {
    use crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedProof;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition as Definition,
        BuiltinPropDefinitionProof as Builtin,
    };
    let source="forall f fn(x R) R,p R:\n    exist L R st {$has_derivative_at(f,p,L)}\n    =>:\n        derivative(f,p)=derivative(f,p)";
    let (mut run, c) = super::execute(source);
    assert!(c.compile_run(&run, "valid_derivative_existence").is_ok());
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
    let atomic = super::atomic_proof_mut(&mut p.differentiability);
    let AtomicExceptEqualityFactSearchedProof::ByDefinition(Definition::BuiltinProp(
        Builtin::FunctionDifferentiableAt(def_proof),
    )) = &mut atomic.searched_proof
    else {
        panic!("differentiability definition");
    };
    let Fact::ExistFact(exists) = &mut def_proof.requirement_facts[0] else {
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
        "have f fn(x R) R\nderivative(f,0)=0",
        "have f fn(x R) R\n0*derivative(f,0)=0",
        "have fn f(x R) R=abs(x)\nderivative(f,0)=0",
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
fn derivative_definition_requires_both_ordered_original_clauses() {
    use crate::execute::execute_by_stmt::ExecByDefStmtResult;
    use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition as Definition,
        BuiltinPropDefinitionProof as Builtin,
    };
    use crate::execute::ExecDefinitionStmtResult;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(
            r#"# Derive the classical derivative from an interior neighborhood and the punctured quotient limit.
thm derivative_from_definition:
    ? forall f fn(x R) R, p, L R:
        exist radius R+ st {{x R: abs(x-p)<radius} $subset R}
        $has_limit_at(fn(x R: x-p != 0) R {(f(x)-f(p))/(x-p)}, p, L)
        =>:
            $has_derivative_at(f, p, L)
    by def $has_derivative_at(f, p, L)
"#,
        );
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
    let source = r#"# Differentiability provides the witness required to construct the derivative.
forall f fn(x R) R, p R:
    $is_differentiable_at(f, p)
    =>:
        derivative(f, p) $in R
        derivative(f, p) = derivative(f, p)
"#;
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
