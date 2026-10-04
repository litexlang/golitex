use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn forall_source_replay_supports_an_unused_parameter_and_same_spelling() {
    for source_name in ["t", "x"] {
        let code = format!("claim:\n    ? forall {source_name} R:\n        exist! y R st {{y = 0}}\n    witness exist! y R st {{y = 0}} from 0\nhave fn selected by exist!:\n    ? forall x R:\n        exist! z R st {{z = 0}}\nselected(0) = 0\nselected(2) = 0\n");
        let mut rt = runtime();
        let run = rt.run_litex_code(&code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(run.success, "{code}");
        let detail = format!(
            "{:?}",
            crate::json_output::project_stmt_detailed(&run.statement_results[1], &rt)
        );
        assert!(detail.contains("by_known_forall_fact"), "{detail}");
        assert!(detail.contains("cite_fact_id"), "{detail}");
        assert!(detail.contains("parameter_renamings"), "{detail}");
        let crate::execute::ExecStmtResult::Definition(
            crate::execute::ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(selected),
            ),
        ) = &run.statement_results[1]
        else {
            panic!("selected function");
        };
        let crate::execute::execute_fact_stmt::VerifyFactResult::ForallFact(source) =
            &selected.source_forall
        else {
            panic!("source forall");
        };
        let crate::execute::execute_fact_stmt::verify_forall_fact::VerifyForallFactResult::Success(
            crate::execute::execute_fact_stmt::verify_forall_fact::VerifyForallFactProof::ByKnownForallFact(proof),
        ) = source.as_ref() else { panic!("proved whole-source replay"); };
        let Some(crate::ast::fact::Fact::ForallFact(cited)) =
            rt.fact_by_id_in_stack(proof.cite_fact_id)
        else {
            panic!("citation must refer to a real stored forall");
        };
        assert_eq!(proof.parameter_renamings.len(), 1);
        assert_eq!(
            proof.parameter_renamings[0].source,
            cited.typed_parameters.groups[0].params[0].id
        );
        assert_eq!(
            proof.parameter_renamings[0].target,
            proof.fact.typed_parameters.groups[0].params[0].id
        );
        assert_ne!(
            proof.parameter_renamings[0].source,
            proof.parameter_renamings[0].target
        );
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(
            rt.run_litex_code("have x R = 7\nhave z R = 8\nx = 7\nz = 8\n")
                .unwrap()
                .success
        );
    }
}

#[test]
fn forall_source_replay_requires_a_proved_unique_source_and_keeps_rollback() {
    for prefix in [
        "",
        "claim:\n    ? forall t R:\n        exist y R st {y = 0}\n    witness exist y R st {y = 0} from 0\n",
        "claim:\n    ? forall t R:\n        t > 0\n        =>:\n            exist! y R st {y = 0}\n    witness exist! y R st {y = 0} from 0\n",
    ] {
        let mut rt = runtime();
        let setup = rt.run_litex_code(prefix).unwrap();
        assert!(setup.success, "{prefix}: {:?}", setup.session_error);
        let run = rt.run_litex_code("have fn selected by exist!:\n    ? forall x R:\n        exist! z R st {z = 0}\n").unwrap();
        assert!(run.session_error.is_none(), "{prefix}: {:?}", run.session_error);
        assert!(!run.success, "{prefix}");
        assert!(rt.run_litex_code("have selected R = 3\nselected = 3\n").unwrap().success);
        assert!(!rt.run_litex_code("0 = 1\n").unwrap().success);
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn forall_source_replay_keeps_free_object_identity_and_carriers() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have first R = 0\nhave second R = 1\nclaim:\n    ? forall t R:\n        exist! y R st {y = first}\n    witness exist! y R st {y = first} from first\n").unwrap().success);
    let run = rt
        .run_litex_code(
            "have fn selected by exist!:\n    ? forall x R:\n        exist! z R st {z = second}\n",
        )
        .unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(!run.success);
    assert!(rt.run_litex_code("have fn selected by exist!:\n    ? forall x R:\n        exist! z R st {z = first}\nselected(1) = first\n").unwrap().success);
    let mut rt = runtime();
    assert!(rt.run_litex_code("claim:\n    ? forall t N:\n        exist! y R st {y = 0}\n    witness exist! y R st {y = 0} from 0\n").unwrap().success);
    assert!(
        !rt.run_litex_code(
            "have fn selected by exist!:\n    ? forall x R:\n        exist! z R st {z = 0}\n"
        )
        .unwrap()
        .success
    );
}

#[test]
fn forall_source_replay_stable_tracer_succeeds_without_trust() {
    let run = runtime()
        .run_litex_code(include_str!(
            "../../../../examples/stmt_nodes/definition/forall_source_replay.lit"
        ))
        .unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success);
}

#[test]
fn proved_forall_replay_renames_nested_builders_and_cites_the_whole_source() {
    use crate::ast::fact::Fact;
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::verify_forall_fact::{
        VerifyForallFactProof, VerifyForallFactResult,
    };
    use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
    use crate::tokenize::Tokenizer;
    let mut rt = runtime();
    assert!(rt.run_litex_code("have first, second set\nclaim:\n    ? forall element {x first: x = x}:\n        element $in {y first: y = y}\n    release thm set_builder_member(element, {y first: y = y})\n").unwrap().success);
    let sizes = |rt: &Runtime| {
        rt.execution_environments_stack
            .iter()
            .map(|e| {
                (
                    e.facts.facts_by_id.len(),
                    e.well_defined_objects.object_to_wd_id.len(),
                )
            })
            .collect::<Vec<_>>()
    };
    let before = sizes(&rt);
    for (code, expected) in [
        (
            "forall object {z first: z = z}:\n    object $in {w first: w = w}\n",
            true,
        ),
        (
            "forall object {z second: z = z}:\n    object $in {w first: w = w}\n",
            false,
        ),
        (
            "forall object {z first: z = z}:\n    object $in {w second: w = w}\n",
            false,
        ),
        (
            "forall object {z first: z = z}:\n    object $in {w first: w != w}\n",
            false,
        ),
        (
            "forall object {z first: z = z}:\n    not object $in {w first: w = w}\n",
            false,
        ),
    ] {
        let tokens = Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(Fact::ForallFact(goal)) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("forall")
        };
        let matched = rt.match_known_forall_source(&goal);
        assert_eq!(matched.is_some(), expected, "{code}");
        if let Some((cite, renamings)) = matched {
            assert!(matches!(
                rt.fact_by_id_in_stack(cite),
                Some(Fact::ForallFact(_))
            ));
            assert_eq!(renamings.len(), 1);
            let result = rt
                .verify_fact(
                    &Fact::ForallFact(goal),
                    VerifyState::new(VerifyStateLevel::Direct),
                )
                .unwrap();
            let VerifyFactResult::ForallFact(result) = result else {
                panic!("forall result")
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) =
                result.as_ref()
            else {
                panic!("whole-source citation")
            };
            assert_eq!(proof.cite_fact_id, cite);
        }
        assert_eq!(before, sizes(&rt));
    }
}


#[test]
fn whole_forall_exist_replay_renames_nested_function_binders_without_search() {
    use crate::ast::fact::Fact;
    use crate::ast::stmt::Stmt;
    use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState, VerifyStateLevel};
    use crate::execute::execute_fact_stmt::verify_forall_fact::{VerifyForallFactProof, VerifyForallFactResult};
    let mut rt = runtime();
    let prefix = "have fn identity(x R) R=x\nclaim:\n    ? forall a R:\n        exist f fn(x R) R st {f(a)=a}\n    witness exist f fn(x R) R st {f(a)=a} from identity:\n        f(a)=identity(a)=a\n";
    assert!(rt.run_litex_code(prefix).unwrap().success);
    let parse = |rt: &mut Runtime, source: &str| {
        let tokens = crate::tokenize::Tokenizer::new().tokenize(source,rt.current_file.clone()).unwrap();
        let mut stmts = rt.parse(&tokens).unwrap();
        let Stmt::Fact(Fact::ForallFact(fact)) = stmts.remove(0) else { panic!("forall goal"); };
        fact
    };
    let goal = parse(&mut rt,"forall b R:\n    exist g fn(y R) R st {g(b)=b}\n");
    let before: Vec<_> = rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).collect();
    let (cite, renamings) = rt.match_known_forall_source(&goal).expect("nested alpha replay");
    assert_eq!(renamings.len(),1);
    for bad in [
        "forall b R:\n    exist g fn(y R) Z st {g(b)=b}\n",
        "forall b R:\n    exist g fn(y R: y>0) R st {g(b)=b}\n",
        "forall b R:\n    exist g fn(y R) R st {g(b)=g(b)+1}\n",
        "forall b R:\n    exist! g fn(y R) R st {g(b)=b}\n",
        "forall b R:\n    not exist g fn(y R) R st {g(b)=b}\n",
    ] {
        let altered = parse(&mut rt,bad);
        assert!(rt.match_known_forall_source(&altered).is_none(),"{bad}");
    }
    let after: Vec<_> = rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).collect();
    assert_eq!(before,after);
    let result = rt.verify_fact(&Fact::ForallFact(goal),VerifyState::new(VerifyStateLevel::Direct)).unwrap();
    let VerifyFactResult::ForallFact(result) = result else { panic!("forall result"); };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) = result.as_ref() else { panic!("source citation at Direct"); };
    assert_eq!(proof.cite_fact_id,cite);
}
