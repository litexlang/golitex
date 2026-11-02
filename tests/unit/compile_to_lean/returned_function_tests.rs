use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnObjDomainFnSetEvidence, FunctionSpaceObjWellDefinedProofByDef,
};
use crate::prelude::*;

const RANGE: &str = include_str!("../../../lean/examples/returned_function_ranges/statement.lit");
const VALUE: &str = include_str!("../../../lean/examples/returned_function_values/statement.lit");
const SEQUENCE: &str =
    include_str!("../../../lean/examples/returned_sequence_values/statement.lit");
const NESTED_SEQUENCE: &str =
    include_str!("../../../lean/examples/nested_returned_sequence_values/statement.lit");
const MIXED: &str = include_str!("../../../lean/examples/mixed_returned_calls/statement.lit");
const RETURNED_BETA: &str =
    include_str!("../../../lean/examples/returned_integer_window_beta/statement.lit");

#[test]
fn returned_known_beta_checks_receiver_and_substituted_call_evidence() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
            by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody}},
    };
    let source = include_str!("../../../lean/examples/zero_matrix_formula_functions/statement.lit");
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(source);
        if mutation == 0 {
            assert!(compiler.compile_run(&run, "returned_known").is_ok());
            continue;
        }
        let proof = super::fact_statement_mut(run.statement_results.last_mut().unwrap());
        let equal = super::equality_proof_mut(&mut proof.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                    ByParentCheckedBetaObjectDefinitionProof::OneSide(beta),
                ),
            ),
        ) = &mut equal.searched_proof
        else {
            panic!("recorded parent beta route")
        };
        let ParentCheckedBetaFunctionBody::ReturnedKnownFunctionApplication {
            receiver_well_defined,
            receiver_function_body,
            application_well_defined,
            application_function_body,
        } = &mut beta.function_body
        else {
            panic!("recorded returned known call")
        };
        match mutation {
            1 | 2 | 3 | 4 | 5 => {
                let selected = if mutation <= 2 {
                    receiver_well_defined
                } else {
                    application_well_defined
                };
                let DetailedObjWellDefinedProof::ByDef {
                    obj,
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                } = selected.as_detailed_mut().unwrap()
                else {
                    panic!("call WD")
                };
                match mutation {
                    1 => *obj = super::number_object("99"),
                    2 | 3 => call.requirement_fact_verified.clear(),
                    4 => call.child_obj_well_defined.clear(),
                    5 => {
                        let Obj::FnObj(app) = obj else {
                            panic!("call subject")
                        };
                        app.body[0].swap(0, 1);
                    }
                    _ => unreachable!(),
                }
            }
            6 => {
                let ParentCheckedBetaFunctionBody::KnownAnonymousFunction {
                    checked_domain, ..
                } = receiver_function_body.as_mut()
                else {
                    panic!("receiver definition")
                };
                checked_domain.ret_set = Box::new(super::number_object("99"));
            }
            7 => {
                *application_function_body =
                    Box::new(ParentCheckedBetaFunctionBody::AnonymousLiteral)
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "changed_returned_known")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn returned_anonymous_beta_replays_original_receiver_and_call() {
    for source in [
        RETURNED_BETA,
        include_str!("../../../lean/examples/returned_quotient_beta/statement.lit"),
        include_str!("../../../lean/examples/returned_affine_beta/statement.lit"),
        include_str!("../../../lean/examples/returned_generic_constant_beta/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "returned_beta").unwrap();
        if source == RETURNED_BETA {
            assert!(lean.contains("_litex_receiver_eq"));
            assert!(lean.contains("Litex.FunctionSemantics.pair_mem_graph"));
        }
        assert_eq!(lean, compiler.compile_run(&run, "returned_beta").unwrap());
    }
}

#[test]
fn returned_anonymous_beta_rejects_changed_receiver_formula_and_substitution() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::{
        EqualitySearchProofByObjectDefinition,
        by_fn_application::{EqualitySearchProofByFnApplicationObjectDefinition,
            by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody}},
    };
    for mutation in 0..9 {
        let (mut run, compiler) = super::execute(RETURNED_BETA);
        let index = if mutation >= 7 {
            5
        } else if mutation >= 5 {
            8
        } else {
            1
        };
        let proof = super::fact_statement_mut(&mut run.statement_results[index]);
        let equal = super::equality_proof_mut(&mut proof.verify_result);
        let EqualFactSearchedProof::ByObjectDefinition(
            EqualitySearchProofByObjectDefinition::ByFnApplication(
                EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                    ByParentCheckedBetaObjectDefinitionProof::OneSide(beta),
                ),
            ),
        ) = &mut equal.searched_proof
        else {
            panic!("recorded returned beta route")
        };
        let ParentCheckedBetaFunctionBody::ReturnedAnonymousFunctionApplication {
            receiver_well_defined,
            receiver_function_body,
            returned_function,
        } = &mut beta.function_body
        else {
            panic!("recorded returned anonymous formula")
        };
        match mutation {
            0 => returned_function.equal_to = Box::new(super::number_object("99")),
            1 => beta.expanded_body = super::number_object("99"),
            2 | 3 => {
                let DetailedObjWellDefinedProof::ByDef {
                    obj,
                    proof: ObjWellDefinedProofByDef::FnObj(call),
                } = receiver_well_defined.as_detailed_mut().unwrap()
                else {
                    panic!("receiver WD")
                };
                if mutation == 2 {
                    *obj = super::number_object("99");
                } else {
                    call.requirement_fact_verified.clear();
                }
            }
            4 => {
                let ParentCheckedBetaFunctionBody::KnownAnonymousFunction {
                    checked_domain, ..
                } = receiver_function_body.as_mut()
                else {
                    panic!("receiver definition")
                };
                checked_domain.ret_set = Box::new(super::number_object("99"));
            }
            5 => returned_function.body.dom_facts.clear(),
            6 => returned_function.body.ret_set = Box::new(Obj::StandardSet(StandardSet::Q)),
            7 => returned_function
                .body
                .set_bound_parameters
                .groups
                .swap(0, 1),
            8 => {
                let id = returned_function.body.set_bound_parameters.groups[0].params[0].id;
                returned_function.body.set_bound_parameters.groups[1].params[0].id = id;
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "changed_returned_beta").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn returned_function_ranges_and_values_replay_deterministically() {
    for source in [RANGE, VALUE, SEQUENCE, NESTED_SEQUENCE, MIXED] {
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
fn returned_chains_preserve_each_argument_stage() {
    for source in [NESTED_SEQUENCE, MIXED] {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(source);
            let all = super::forall_proof_mut(&mut run.statement_results[0]);
            let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = atom
                .well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter[0]
                .as_detailed_mut()
                .unwrap()
            else {
                panic!("nested returned sequence WD")
            };
            assert_eq!(call.child_obj_well_defined.len(), 3);
            assert_eq!(call.requirement_fact_verified.len(), 3);
            match mutation {
                0 => {
                    call.child_obj_well_defined.remove(1);
                }
                1 => {
                    call.requirement_fact_verified.remove(1);
                }
                2 => call.child_obj_well_defined.swap(1, 2),
                3 => call.requirement_fact_verified.swap(1, 2),
                _ => unreachable!(),
            }
            assert!(
                compiler.compile_run(&run, "bad_nested_indices").is_err(),
                "mutation {mutation}"
            );
        }
    }
}

#[test]
fn mixed_returned_calls_keep_outer_and_inner_guards_separate() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(MIXED);
        let all = super::forall_proof_mut(&mut run.statement_results[3]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = atom
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0]
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("mixed returned call WD")
        };
        assert_eq!(call.requirement_fact_verified.len(), 6);
        if mutation == 0 {
            call.requirement_fact_verified.remove(4);
        } else {
            call.requirement_fact_verified.swap(1, 4);
        }
        assert!(compiler.compile_run(&run, "mixed_guard_stages").is_err());
    }
}

#[test]
fn returned_sequence_rejects_missing_swapped_or_weakened_index_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(SEQUENCE);
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = atom
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0]
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("returned sequence call WD")
        };
        match mutation {
            0 => {
                call.child_obj_well_defined.pop();
            }
            1 => {
                call.requirement_fact_verified.pop();
            }
            2 => call.child_obj_well_defined.swap(0, 1),
            3 => call.requirement_fact_verified.swap(0, 1),
            4 => {
                let atom =
                    super::atomic_proof_mut(call.requirement_fact_verified.last_mut().unwrap());
                let AtomicFact::InFact(f) = &mut atom.fact else {
                    panic!("index membership")
                };
                f.set = Obj::StandardSet(StandardSet::N);
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_sequence_call").is_err(),
            "mutation {mutation}"
        );
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
