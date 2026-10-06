use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::well_defined_results::{
    ObjWellDefinedProof, ObjWellDefinedProofByDef, VerifyObjWellDefinedResult,
};
use crate::execute::{
    ExecDefineObjStmtResult, ExecDefinitionStmtResult, ExecLetObjStmtResult, ExecStmtResult,
};
use crate::launch_command::{LaunchCommand, OutputLanguage};
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
        for child in &p.child_obj_well_defined {
            if let ObjWellDefinedProof::ByKnown { wd_id, obj } = child.as_ref() {
                assert!(
                    rt.execution_environments_stack.iter().any(|env| env
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
        let mut retained_ids: Vec<String> = rt
            .execution_environments_stack
            .iter()
            .flat_map(|env| {
                env.well_defined_objects
                    .wd_id_to_object
                    .keys()
                    .map(|wd| wd.to_string())
            })
            .collect();
        // Literal heads legitimately retain their own binder environment.
        // Candidate argument scopes have no such returned owner.
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
    let FactWellDefinedProof::Equality(wd) = &s.iff_fact_well_defined[0] else {
        panic!("equality WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(p),
        ..
    } = &wd.left
    else {
        panic!("field application WD")
    };
    let owners: Vec<_> = rt
        .execution_environments_stack
        .iter()
        .map(|env| env.as_ref())
        .chain(std::iter::once(s.local_env.as_ref()))
        .collect();
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
        code: String::new(), session: false, strict: true, language: OutputLanguage::English,
    });
    let run = rt.run_litex_code("template<S set>:\n    have fn pair(x S) cart(S,S) = (x,x)\nlet alias = \\pair<R>\nlet other_alias = alias\nother_alias = \\pair<R>\nlet value = other_alias(2)\n").unwrap();
    assert!(run.success && run.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(result)),
    )) = run.statement_results.last().unwrap() else { panic!("let result") };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(proof), ..
    }) = &result.value_well_defined else { panic!("application WD") };
    let Some(FnObjDomainFnSetEvidence::TemplateDefinition { function_equal, .. }) = &proof.domain_fn_set else { panic!("template signature") };
    assert_eq!(function_equal.path.len(), 1);
    for (_, _, id) in &function_equal.path {
        assert!(rt.fact_by_id_in_stack(*id).is_some());
    }
    assert!(!proof.child_obj_well_defined.is_empty());
    let json = crate::json_output::project_stmt_detailed(run.statement_results.last().unwrap(), &rt).stringify();
    for field in ["template_definition", "function_equal", "cite_fact_id"] {
        assert!(json.contains(field), "{field}: {json}");
    }
    assert_eq!(rt.execution_environments_stack.len(), 1);
    assert!(!rt.run_litex_code("other_alias(i) = (i,i)\n").unwrap().success);
}
