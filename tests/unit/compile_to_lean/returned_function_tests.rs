use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnObjDomainFnSetEvidence, FunctionSpaceObjWellDefinedProofByDef,
};
use crate::prelude::*;

const RANGE: &str = include_str!("../../../lean/examples/returned_function_ranges/statement.lit");
const VALUE: &str = include_str!("../../../lean/examples/returned_function_values/statement.lit");

#[test]
fn returned_function_ranges_and_values_replay_deterministically() {
    for source in [RANGE, VALUE] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "returned_functions").unwrap();
        assert_eq!(
            lean,
            compiler.compile_run(&run, "returned_functions").unwrap()
        );
        assert!(lean.contains("Litex.callOn"));
        assert!(!lean.contains("sorry") && !lean.contains("axiom"));
    }
}

fn range_domain_mut(
    run: &mut RunLitexCodeResult,
    index: usize,
) -> &mut CompleteFunctionDomainProof {
    let forall = super::forall_proof_mut(&mut run.statement_results[index]);
    let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnRange(
                range,
            )),
        ..
    } = (&mut atomic
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0])
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("range WD")
    };
    &mut range.function_domains[0]
}

#[test]
fn returned_domain_consumes_original_applicability_and_signature() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(RANGE);
        let domain = range_domain_mut(&mut run, 0);
        let CompleteFunctionDomainSourceProof::ApplicationReturn {
            application_check,
            signature_source,
            return_space,
            ..
        } = &mut domain.source
        else {
            panic!("actual ApplicationReturn")
        };
        let checks = application_check.as_detailed_mut().unwrap();
        let application_children = &mut checks.child_obj_well_defined;
        let application_requirements = &mut checks.requirement_fact_verified;
        match mutation {
            0 => {
                application_children.clear();
            }
            1 => {
                application_requirements.clear();
            }
            2 => {
                *return_space = super::number_object("99");
            }
            3 => {
                domain.signature.ret_set = Box::new(super::number_object("99"));
            }
            4 => {
                let FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. } = signature_source
                else {
                    panic!()
                };
                fn_set.ret_set = Box::new(super::number_object("99"));
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_returned_domain").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn returned_call_rejects_missing_swapped_or_mismatched_stages() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(VALUE);
        let forall = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = (&mut atomic
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("call WD")
        };
        match mutation {
            0 => {
                call.child_obj_well_defined.pop();
            }
            1 => {
                call.requirement_fact_verified.pop();
            }
            2 => {
                call.child_obj_well_defined.swap(0, 1);
            }
            3 => {
                call.requirement_fact_verified.swap(0, 1);
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_returned_call").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn returned_function_preimages_and_membership_use_original_return_evidence() {
    for source in [
        include_str!("../../../lean/examples/returned_function_preimages/statement.lit"),
        include_str!("../../../lean/examples/returned_function_membership/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler
            .compile_run(&run, "returned_domain_consumers")
            .unwrap();
        assert!(lean.contains("_returned_source"));
        assert_eq!(
            lean,
            compiler
                .compile_run(&run, "returned_domain_consumers")
                .unwrap()
        );
    }
}

#[test]
fn returned_domain_argument_scope_rejects_a_future_registered_producer() {
    let (mut run, compiler) = super::execute(RANGE);
    let p = range_domain_mut(&mut run, 2);
    let CompleteFunctionDomainSourceProof::ApplicationReturn {
        application_check, ..
    } = &mut p.source
    else {
        panic!()
    };
    let checks = application_check.as_detailed_mut().unwrap();
    let application_children = &checks.child_obj_well_defined;
    let scope = checks.argument_scope.as_mut().unwrap();
    assert!(!scope.formed_children.is_empty());
    scope.formed_children[0].child_index = application_children.len() + 100;
    assert!(compiler
        .compile_run(&run, "future_return_argument")
        .is_err());
}

#[test]
fn returned_calls_cannot_skip_either_nonzero_guard() {
    for (outer, inner) in [("0", "2"), ("2", "0")] {
        let source = format!(
            "forall provider fn(t R: t != 0) fn(x R: x != 0) R:\n    provider({outer})({inner}) $in R\n"
        );
        let mut runtime = Runtime::new_with_result_detail(
            LaunchCommand::Eval {
                code: String::new(),
                session: false,
                strict: true,
                language: OutputLanguage::English,
            },
            crate::result_detail::OutputDetail::Detailed,
        );
        let run = runtime.run_litex_code(&source).unwrap();
        assert!(!run.success);
        assert!(crate::compile_to_lean::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_returned_call")
            .is_err());
    }
}

#[test]
fn returned_positive_domain_retains_membership_and_positivity() {
    let (run, compiler) =
        super::execute("forall provider fn(t R) fn(x R+) R:\n    provider(1)(2) $in R\n");
    let lean = compiler.compile_run(&run, "returned_positive").unwrap();
    assert!(lean.contains("Litex.FunctionSignature.one_domain"));
    assert!(lean.contains("Litex.inRPos_real"));
    assert!(lean.contains("Litex.positiveReal_members"));
}

#[test]
fn returned_matrix_and_finite_sequence_calls_consume_original_stages() {
    for source in [
        include_str!("../../../lean/examples/returned_matrix_coordinates/statement.lit"),
        include_str!("../../../lean/examples/returned_matrix_guarded/statement.lit"),
        include_str!("../../../lean/examples/returned_finite_sequence_values/statement.lit"),
        include_str!("../../../lean/examples/returned_matrix_transpose/statement.lit"),
        include_str!("../../../lean/examples/returned_matrix_function_transpose/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "returned_arrays").unwrap();
    }
}

#[test]
fn returned_matrix_rejects_missing_or_swapped_index_evidence() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/returned_matrix_coordinates/statement.lit"
        ));
        compiler.compile_run(&run, "valid_matrix_call").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = (&mut atom
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("returned matrix call WD")
        };
        match mutation {
            0 => {
                call.child_obj_well_defined.pop();
            }
            1 => {
                call.requirement_fact_verified.pop();
            }
            2 => call.child_obj_well_defined.swap(1, 2),
            3 => call.requirement_fact_verified.swap(1, 2),
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "wrong_returned_matrix").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn returned_matrix_transpose_rejects_changed_carrier_evidence() {
    use crate::execute::execute_fact_stmt::native_matrix::{MatrixMembershipProof, MatrixFunctionScalarCarrierProof};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/returned_matrix_transpose/statement.lit"
        ));
        compiler
            .compile_run(&run, "valid_returned_transpose")
            .unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::NativeMatrix(MatrixMembershipProof::Function(p)),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("matrix membership")
        };
        let MatrixFunctionScalarCarrierProof::RealReturnedFunction(domain) =
            &mut p.callable.scalar_carrier
        else {
            panic!("returned real carrier")
        };
        if mutation == 0 {
            domain.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            let CompleteFunctionDomainSourceProof::ApplicationReturn {
                application_check, ..
            } = &mut domain.source
            else {
                panic!("returned matrix source")
            };
            application_check
                .as_detailed_mut()
                .unwrap()
                .requirement_fact_verified
                .clear();
        }
        assert!(compiler
            .compile_run(&run, "wrong_returned_transpose")
            .is_err());
    }
}
