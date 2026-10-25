use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::{FnSetAlphaProof, SameFreeParamShapeProof};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
use crate::prelude::*;

const SIGNATURES: &str =
    include_str!("../../../lean/examples/literal_function_signatures/statement.lit");

fn atomic_mut(
    run: &mut RunLitexCodeResult,
    index: usize,
) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    super::atomic_proof_mut(
        &mut super::fact_statement_mut(&mut run.statement_results[index]).verify_result,
    )
}

#[test]
fn declared_literal_signatures_consume_the_actual_builtin() {
    let (mut run, compiler) = super::execute(SIGNATURES);
    for index in 0..3 {
        assert!(matches!(
            atomic_mut(&mut run, index).searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                    InFactSearchProofByBuiltinRule::AnonymousFnInDeclaredFnSet(_)
                )
            )
        ));
    }
    let lean = compiler.compile_run(&run, "literal_signatures").unwrap();
    assert!(lean.contains("Litex.formulaFnInFnSet"));
    assert_eq!(
        lean,
        compiler.compile_run(&run, "literal_signatures").unwrap()
    );
}

#[test]
fn declared_literal_rule_rejects_other_subjects_and_inexact_signatures() {
    for change in 0..6 {
        let (mut run, compiler) = super::execute(SIGNATURES);
        let AtomicFact::InFact(mut fact) = atomic_mut(&mut run, 1).fact.clone() else {
            panic!()
        };
        if change == 0 {
            fact.element = super::number_object("1");
        } else if change == 1 {
            fact.set = Obj::StandardSet(StandardSet::R);
        } else {
            let Obj::FunctionSpace(FunctionSpace::FnSet(s)) = &mut fact.set else {
                panic!()
            };
            match change {
                2 => s.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
                3 => s.dom_facts.clear(),
                4 => {
                    s.set_bound_parameters.groups[0].param_type =
                        Box::new(Obj::StandardSet(StandardSet::Z))
                }
                5 => s.set_bound_parameters.groups[0].params.clear(),
                _ => unreachable!(),
            }
        }
        let scope = SourcePosition::new(None, SourceOwner::Run(&run), 0);
        assert!(
            compiler
                .compile_literal_function_member(&fact, &scope)
                .is_err(),
            "change {change}"
        );
    }
}

#[test]
fn declared_literal_membership_requires_original_constructor_wd() {
    let (mut run, compiler) = super::execute(SIGNATURES);
    let wd = &mut atomic_mut(&mut run, 1)
        .well_defined_proof
        .well_defined_of_each_parameter[0];
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                p,
            )),
        ..
    } = wd
    else {
        panic!("literal WD")
    };
    p.assumed_dom_facts.clear();
    assert!(compiler.compile_run(&run, "missing_literal_guard").is_err());
}

#[test]
fn return_carrier_alpha_proof_cannot_change_the_codomain_or_guard() {
    for change in 0..2 {
        let (mut run, compiler) = super::execute(SIGNATURES);
        let AtomicFact::InFact(fact) = atomic_mut(&mut run, 1).fact.clone() else {
            panic!()
        };
        let source = fact.set;
        let mut target = source.clone();
        let Obj::FunctionSpace(FunctionSpace::FnSet(s)) = &mut target else {
            panic!()
        };
        if change == 0 {
            s.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            s.dom_facts.clear();
        }
        let evidence =
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameFreeParamShape(
                SameFreeParamShapeProof::FnSet(FnSetAlphaProof::new()),
            ));
        let scope = SourcePosition::new(None, SourceOwner::Run(&run), 0);
        assert!(compiler
            .compile_fn_return_set_match(&source, &target, &evidence, &scope)
            .is_err());
    }
}

#[test]
fn constructed_returned_functions_and_function_arguments_replay() {
    for source in [
        include_str!("../../../lean/examples/selected_shift_function/statement.lit"),
        include_str!("../../../lean/examples/function_identity_operator/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "constructed_functions").unwrap();
        assert_eq!(
            lean,
            compiler.compile_run(&run, "constructed_functions").unwrap()
        );
    }
}
