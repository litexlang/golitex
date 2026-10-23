use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::well_defined_results::{
    ObjWellDefinedProof, ObjWellDefinedProofByDef, VerifyObjWellDefinedResult,
};
use crate::execute::{
    ExecDefineObjStmtResult, ExecDefinitionStmtResult, ExecLetObjStmtResult, ExecStmtResult,
};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::prelude::*;
use crate::runtime::Runtime;

#[test]
fn application_wd_does_not_return_ids_owned_only_by_a_discarded_candidate_scope() {
    for source in [
        "have fn choose(a, b R) R = a\nlet value = choose(1 + 1, 1 + 1)\n",
        "let value = fn(a, b R) R {a}(1 + 1, 1 + 1)\n",
        "let cached = 1 + 1\nhave fn choose(a, b R) R = a\nlet value = choose(1 + 1, 1 + 1)\n",
        "struct Guarded:\n    point R\n    call fn(x R:x=point) R\nhave fn at_zero(x R:x=0) R=0\nhave guarded &Guarded=(0,at_zero)\nlet value=guarded(2)(guarded.point)\n",
    ] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        });
        let run = rt.run_litex_code(source).unwrap();
        assert!(
            run.success && run.session_error.is_none(),
            "{source}: {:?}",
            run.session_error
        );
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(s)),
        )) = run.statement_results.last().unwrap()
        else {
            panic!("let result")
        };
        let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(p),
            ..
        }) = &s.value_well_defined
        else {
            panic!("application WD proof")
        };
        // The application proof retains its candidate argument scope. Its
        // local env is part of the returned evidence, so it owns the WD ids
        // that the candidate formed before the application was committed.
        let mut retained_owners: Vec<&_> = rt
            .execution_environments_stack
            .iter()
            .map(|env| env.as_ref())
            .collect();
        if let Some(scope) = &p.argument_scope {
            retained_owners.push(scope.local_env.as_ref());
        }
        for child in &p.child_obj_well_defined {
            if let ObjWellDefinedProof::ByKnown { wd_id, obj } = child.as_ref() {
                assert!(
                    retained_owners.iter().any(|env| env
                        .well_defined_objects
                        .wd_id_to_object
                        .get(wd_id)
                        == Some(obj)),
                    "returned WD id {wd_id} must have a retained owner"
                );
            }
        }
        assert_eq!(rt.execution_environments_stack.len(), 1);
        let projected =
            crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt);
        let mut ids = Vec::new();
        collect_wd_ids(&projected, &mut ids);
        let mut retained_ids: Vec<String> = retained_owners
            .iter()
            .flat_map(|env| {
                env.well_defined_objects
                    .wd_id_to_object
                    .keys()
                    .map(|wd| wd.to_string())
            })
            .collect();
        // Literal heads and nested function-space proofs retain their own
        // binder environments; add those to the resolvable-id set as well.
        for child in &p.child_obj_well_defined {
            if let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FunctionSpace(space),
                ..
            } = child.as_ref()
            {
                let env = match space {
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(proof) => {
                        Some(&proof.local_env)
                    }
                    FunctionSpaceObjWellDefinedProofByDef::FnSet(proof) => Some(&proof.local_env),
                    _ => None,
                };
                if let Some(env) = env {
                    retained_ids.extend(
                        env.well_defined_objects
                            .wd_id_to_object
                            .keys()
                            .map(|wd| wd.to_string()),
                    );
                }
            }
        }
        for id in ids {
            assert!(
                retained_ids.contains(&id),
                "{source}: projected WD id {id} must remain resolvable"
            );
        }
        assert!(!rt.run_litex_code("0 = 1").unwrap().success);
    }
}

#[test]
fn field_application_wd_citations_stay_in_the_retained_definition_scope() {
    use crate::execute::execute_def_prop_stmt::ExecDefPropStmtResult;
    use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let source = "struct Pair:\n    operation fn(a, b R) R\n    value R\nprop call(pair &Pair):\n    pair.operation(1 + 1, 1 + 1) = 0\n";
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    let result = run.statement_results.last().unwrap();
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Success(s),
    )) = result
    else {
        panic!("prop result")
    };
    let FactWellDefinedProof::Equality(wd) = &s.assumed_iff_facts[0].well_defined else {
        panic!("equality WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(p),
        ..
    } = &wd.left
    else {
        panic!("field application WD")
    };
    let mut owners: Vec<_> = rt
        .execution_environments_stack
        .iter()
        .map(|env| env.as_ref())
        .chain(std::iter::once(s.local_env.as_ref()))
        .collect();
    if let Some(scope) = &p.argument_scope {
        owners.push(scope.local_env.as_ref());
    }
    for child in &p.child_obj_well_defined {
        if let ObjWellDefinedProof::ByKnown { wd_id, obj } = child.as_ref() {
            assert!(
                owners
                    .iter()
                    .any(|env| env.well_defined_objects.wd_id_to_object.get(wd_id) == Some(obj)),
                "returned field-call WD id {wd_id} must have a retained owner"
            );
        }
    }
    let detailed = crate::json_output::project_stmt_detailed(result, &rt);
    let body = detailed
        .as_object()
        .unwrap()
        .get("iff_fact_well_defined")
        .unwrap();
    let mut ids = Vec::new();
    collect_wd_ids(body, &mut ids);
    for id in ids {
        assert!(
            owners.iter().any(|env| env
                .well_defined_objects
                .wd_id_to_object
                .keys()
                .any(|wd| wd.to_string() == id)),
            "projected field-call WD id {id} must stay in its retained scope"
        );
    }
}

#[test]
fn function_binder_capture_preserves_ordered_parameter_and_guard_producers() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = rt
        .run_litex_code("have fn ratio(a, b R: b != 0) R = a / b\n")
        .unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        crate::execute::ExecHaveFnEqualStmtResult::Success(result),
    )) = &run.statement_results[0]
    else {
        panic!("function definition result")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                anonymous,
            )),
        ..
    }) = &result.anonymous_fn_well_defined
    else {
        panic!("anonymous function WD")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(
                signature,
            )),
        ..
    }) = &result.fn_set_well_defined
    else {
        panic!("function set WD")
    };
    let header = &result.statement.equal_to_anonymous_fn.body;
    let parameters: Vec<_> = header
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|group| {
            group
                .params
                .iter()
                .map(|parameter| (parameter, &group.param_type))
        })
        .collect();
    let expected_guard =
        crate::instantiate::quantifier_free_fact_to_fact(header.dom_facts[0].clone());
    for (defined, assumed, env) in [
        (
            &anonymous.defined_params,
            &anonymous.assumed_dom_facts,
            &anonymous.local_env,
        ),
        (
            &signature.defined_params,
            &signature.assumed_dom_facts,
            &signature.local_env,
        ),
    ] {
        assert_eq!(defined.store_and_infer_results.len(), parameters.len());
        for ((parameter, carrier), stored) in
            parameters.iter().zip(&defined.store_and_infer_results)
        {
            let id = stored.primary_fact_id();
            let Fact::AtomicFact(AtomicFact::InFact(member)) =
                env.facts.facts_by_id.get(&id).unwrap()
            else {
                panic!("captured parameter membership")
            };
            assert_eq!(
                member.element.ir(),
                Obj::Identifier(IdentifierObj::from_bound_name(parameter)).ir()
            );
            assert_eq!(member.set.ir(), carrier.ir());
            assert_eq!(
                stored.store.atomic_components()[0].1,
                AtomicFact::InFact(member.clone())
            );
            assert!(
                rt.fact_by_id_in_stack(id).is_none(),
                "local parameter fact must remain local"
            );
        }
        assert_eq!(assumed.len(), 1);
        let guard_id = assumed[0].store_and_infer.primary_fact_id();
        assert_eq!(env.facts.facts_by_id.get(&guard_id), Some(&expected_guard));
        assert!(
            rt.fact_by_id_in_stack(guard_id).is_none(),
            "local guard must remain local"
        );
    }
    let stores = &result.store_and_infer_result;
    assert_eq!(
        stores.membership.primary_fact_id(),
        stores.membership_fact_id
    );
    assert_eq!(
        stores.defining_equal.primary_fact_id(),
        stores.defining_equal_fact_id
    );
    let mut expected_ids = stores.membership.stored_fact_ids();
    expected_ids.extend(stores.defining_equal.stored_fact_ids());
    assert_eq!(stores.stored_fact_ids, expected_ids);
    let projected = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let stages = projected
        .as_object()
        .unwrap()
        .get("store_and_infer_results")
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(stages.len(), 2);
    for (stage, id) in stages
        .iter()
        .zip([stores.membership_fact_id, stores.defining_equal_fact_id])
    {
        let stored = &stage
            .as_object()
            .unwrap()
            .get("stores")
            .unwrap()
            .as_array()
            .unwrap()[0];
        assert_eq!(
            stored
                .as_object()
                .unwrap()
                .get("fact_id")
                .unwrap()
                .as_str()
                .unwrap(),
            id.to_string()
        );
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

#[test]
fn anonymous_function_division_wd_cites_its_captured_nonzero_guard() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = rt
        .run_litex_code("have fn reciprocal(x R: x != 0) R = 1 / x\n")
        .unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        crate::execute::ExecHaveFnEqualStmtResult::Success(result),
    )) = &run.statement_results[0]
    else {
        panic!("function definition result")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                anonymous,
            )),
        ..
    }) = &result.anonymous_fn_well_defined
    else {
        panic!("anonymous function WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Div(division),
            ),
        ..
    } = anonymous.body_well_defined.as_ref()
    else {
        panic!("body division WD")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &division.requirement_fact_verified[0]
    else {
        panic!("nonzero requirement")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful nonzero check")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cited) = &proof.searched_proof
    else {
        panic!("nonzero guard citation")
    };
    assert_eq!(
        cited.cite_fact_id,
        anonymous.assumed_dom_facts[0]
            .store_and_infer
            .primary_fact_id()
    );
    let rejected = rt
        .run_litex_code("let failed_value = reciprocal(0)\n")
        .unwrap();
    assert!(!rejected.success && rejected.session_error.is_none());
    assert!(
        rt.run_litex_code("let failed_value = reciprocal(2)\n")
            .unwrap()
            .success
    );
}

#[test]
fn concrete_prop_capture_retains_body_guard_used_by_later_wd() {
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let rejected = rt
        .run_litex_code("prop guarded_value(x R):\n    1 / x $in R\n")
        .unwrap();
    assert!(!rejected.success && rejected.session_error.is_none());
    let run = rt
        .run_litex_code("prop guarded_value(x R):\n    x != 0\n    1 / x $in R\n")
        .unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{:?}",
        run.session_error
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        crate::execute::execute_def_prop_stmt::ExecDefPropStmtResult::Success(result),
    )) = &run.statement_results[0]
    else {
        panic!("concrete proposition result")
    };
    assert_eq!(result.assumed_iff_facts.len(), 2);
    for (expected, captured) in result
        .statement
        .iff_facts
        .iter()
        .zip(&result.assumed_iff_facts)
    {
        let id = captured.store_and_infer.primary_fact_id();
        assert_eq!(result.local_env.facts.facts_by_id.get(&id), Some(expected));
        assert!(
            rt.fact_by_id_in_stack(id).is_none(),
            "definition body fact must remain local"
        );
    }
    let guard_id = result.assumed_iff_facts[0]
        .store_and_infer
        .primary_fact_id();
    let FactWellDefinedProof::AtomicExceptEquality(wd) = &result.assumed_iff_facts[1].well_defined
    else {
        panic!("membership WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Div(division),
            ),
        ..
    } = &wd.well_defined_of_each_parameter[0]
    else {
        panic!("guarded division WD")
    };
    let VerifyFactResult::AtomicExceptEquality(proof) = &division.requirement_fact_verified[0]
    else {
        panic!("nonzero requirement")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
        panic!("successful nonzero check")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cited) = &proof.searched_proof
    else {
        panic!("earlier definition-body citation")
    };
    assert_eq!(cited.cite_fact_id, guard_id);
    let projected = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt);
    let fields = projected.as_object().unwrap();
    assert_eq!(
        fields
            .get("iff_fact_well_defined")
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(
        fields
            .get("store_and_infer_results")
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(rt.execution_environments_stack.len(), 1);
}

fn collect_wd_ids(value: &crate::knowledge_base::JsonValue, ids: &mut Vec<String>) {
    use crate::knowledge_base::JsonValue;
    match value {
        JsonValue::Object(fields) => {
            if let Some(JsonValue::String(id)) = fields.get("wd_id") {
                ids.push(id.clone());
            }
            for (_, value) in fields.iter() {
                collect_wd_ids(value, ids);
            }
        }
        JsonValue::Array(values) => {
            for value in values {
                collect_wd_ids(value, ids);
            }
        }
        _ => {}
    }
}

#[test]
fn template_alias_application_wd_cites_its_checked_instance_and_equality_path() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
    let mut rt = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let run = rt.run_litex_code("template<S set>:\n    have fn pair(x S) cart(S,S) = (x,x)\nlet alias = \\pair<R>\nlet other_alias = alias\nother_alias = \\pair<R>\nlet value = other_alias(2)\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(result)),
    )) = run.statement_results.last().unwrap()
    else {
        panic!("let result")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(proof),
        ..
    }) = &result.value_well_defined
    else {
        panic!("application WD")
    };
    let Some(FnObjDomainFnSetEvidence::TemplateDefinition { function_equal, .. }) =
        &proof.domain_fn_set
    else {
        panic!("template signature")
    };
    assert_eq!(function_equal.path.len(), 1);
    for (_, _, id) in &function_equal.path {
        assert!(rt.fact_by_id_in_stack(*id).is_some());
    }
    assert!(!proof.child_obj_well_defined.is_empty());
    let json =
        crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt)
            .stringify();
    for field in ["template_definition", "function_equal", "cite_fact_id"] {
        assert!(json.contains(field), "{field}: {json}");
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(
        !rt.run_litex_code("other_alias(i) = (i,i)\n")
            .unwrap()
            .success
    );
}
