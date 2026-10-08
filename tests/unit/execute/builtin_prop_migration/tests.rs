use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{ExecFactStmtResult, VerifyState};
use crate::execute::ExecStmtResult;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

#[test]
fn builtin_choice_definition_reuses_checked_pointwise_source() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have fn g_choice(alpha {1}) power_set({1}) = {1}\nhave fn f_choice(alpha {1}) {1} = 1\nforall alpha {1}:\n    f_choice(alpha) $in g_choice(alpha)\n").unwrap();
    assert!(run.success);
    let tokens = Tokenizer::new()
        .tokenize(
            "$is_choice_function_for({1}, power_set({1}), g_choice, f_choice)",
            rt.current_file.clone(),
        )
        .unwrap();
    let goal = rt.parse(&tokens).unwrap().remove(0);
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::IsChoiceFunctionForFact(goal))) = goal else {
        panic!("choice fact");
    };
    let requirements = rt.choice_definition_requirements(&goal).unwrap();
    for requirement in requirements {
        let proof = rt
            .verify_fact(&requirement, VerifyState::top_level())
            .unwrap();
        if proof.is_failed() {
            let result = ExecStmtResult::Fact(ExecFactStmtResult::Failed(proof));
            panic!(
                "{}\n{}",
                requirement.ir(),
                crate::json_output::project_stmt_detailed(&result, &rt).stringify()
            );
        }
    }
    let fact = AtomicFact::IsChoiceFunctionForFact(goal);
    let proof = rt
        .verify_fact(&Fact::AtomicFact(fact), VerifyState::top_level())
        .unwrap();
    if proof.is_failed() {
        let result = ExecStmtResult::Fact(ExecFactStmtResult::Failed(proof));
        panic!(
            "choice predicate\n{}",
            crate::json_output::project_stmt_detailed(&result, &rt).stringify()
        );
    }
    let run = rt
        .run_litex_code("by def $is_choice_function_for({1}, power_set({1}), g_choice, f_choice)\n")
        .unwrap();
    assert!(
        run.success,
        "{}",
        crate::json_output::emit_run_detailed(&run, &rt, "test", None)
    );
}

#[test]
fn builtin_mapping_assumptions_publish_quantified_definitions() {
    for code in [
        "forall f fn(t R) R, a, b R:\n    $injective(R, R, f)\n    f(a) = f(b)\n    =>:\n        a = b\n",
        "forall f fn(t R) R, y R:\n    $surjective(R, R, f)\n    =>:\n        exist x R st {y = f(x)}\n",
        "forall f fn(k N+: k <= 2) R, a, b closed_range(1, 2):\n    $injective(closed_range(1, 2), R, f)\n    f(a) = f(b)\n    =>:\n        a = b\n",
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/finite_set_has_bijective_index.lit"),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(run.success, "{code}: {}", crate::json_output::emit_run_detailed(&run, &rt, "test", None));
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(!rt.run_litex_code("0 = 1\n").unwrap().success);
    }
    for code in [
        "forall f fn(t R) R, a, b R:\n    not $injective(R, R, f)\n    f(a) = f(b)\n    =>:\n        a = b\n",
        "forall f fn(t R) R, y R:\n    not $surjective(R, R, f)\n    =>:\n        exist x R st {y = f(x)}\n",
        "forall f fn(t R) R, y R:\n    $surjective(R, R, f)\n    =>:\n        exist x N st {y = f(x)}\n",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(!run.success, "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn positive_integer_intervals_publish_the_application_carrier() {
    for interval in ["range(1, 3)", "closed_range(1, 2)", "closed_range(2, 3)"] {
        let code = format!("forall k {interval}:\n    k $in N+\n");
        let run = runtime().run_litex_code(&code).unwrap();
        assert!(run.success, "{code}: {:?}", run.session_error);
    }
    for interval in ["range(0, 3)", "closed_range(-1, 2)", "closed_range(0, 2)"] {
        let code = format!("forall k {interval}:\n    k $in N+\n");
        let run = runtime().run_litex_code(&code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "{code}");
    }
}

#[test]
fn builtin_choice_carrier_routes_keep_both_callable_obligations() {
    for code in [
        "have I set = {1}\nhave S set = {{1}}\nhave fn g(x I) S = {1}\nhave fn f(x I) {1} = 1\nforall alpha {1}:\n    $is_choice_function_for({1}, {{1}}, g, f)\n    =>:\n        $is_choice_function_for({1}, {{1}}, g, f)\n",
        "have fn g(x {1}) R = 0\nhave fn f(x {1}) {1} = 1\nforall alpha {1}:\n    $is_choice_function_for({1}, {{1}}, g, f)\n    =>:\n        $is_choice_function_for({1}, {{1}}, g, f)\n",
        "have fn g(x {1}) {{1}} = {1}\nhave fn f(x {1}) R = 1\nforall alpha {1}:\n    $is_choice_function_for({1}, {{1}}, g, f)\n    =>:\n        $is_choice_function_for({1}, {{1}}, g, f)\n",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert_eq!(run.success, code.starts_with("have I"), "{code}: {}", crate::json_output::emit_run_detailed(&run, &rt, "test", None));
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn builtin_family_union_identities_keep_wd_false_and_stage_boundaries() {
    use crate::execute::execute_fact_stmt::VerifyStateLevel;
    for (goal, rule) in [
        ("family_union({A}) = A", "FamilyUnionOfSingleton"),
        ("family_union(power_set(A)) = A", "FamilyUnionOfPowerSet"),
    ] {
        let mut rt = runtime();
        assert!(rt.run_litex_code("have A set\n").unwrap().success);
        let run = rt.run_litex_code(&format!("{goal}\n")).unwrap();
        assert!(run.success);
        let detail = crate::json_output::emit_run_detailed(&run, &rt, "test", None);
        assert!(detail.contains(rule), "{detail}");
        let mut rt = runtime();
        assert!(rt.run_litex_code("have A set\n").unwrap().success);
        let tokens = Tokenizer::new()
            .tokenize(goal, rt.current_file.clone())
            .unwrap();
        let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
            panic!("fact");
        };
        assert!(!rt
            .verify_fact_well_definedness(&fact, VerifyState::top_level())
            .unwrap()
            .is_failed());
        assert!(rt
            .verify_fact(
                &fact,
                VerifyState::new(VerifyStateLevel::KnownSpecialProperty)
            )
            .unwrap()
            .is_failed());
        assert!(!rt
            .verify_fact(&fact, VerifyState::new(VerifyStateLevel::BuiltinRule))
            .unwrap()
            .is_failed());
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(!rt.run_litex_code("0 = 1\n").unwrap().success);
    }
    for code in [
        "have A, B set\nfamily_union({A, B}) = A\n",
        "family_union(power_set({1})) = {2}\n",
        "family_union({{1}}) = {2}\n",
        "family_union(power_set(1 / 0)) = 1 / 0\n",
        "have fn f(x R) R = 0\nby def $surjective(R, R, f)\n",
        "have fn f(x R) R = 0\nby def $injective(R, R, f)\n",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn checked_mapping_definitions_retain_source_and_derived_fact_ids() {
    use crate::execute::execute_by_stmt::{ExecByDefStmtResult, ExecByStmtResult};
    use crate::store_fact_and_infer::{
        InferAtomicExceptEqualityResult, InferAtomicFactResult, InferBuiltinDefinitionResult,
        InferFactResult,
    };
    for property in ["injective", "surjective"] {
        let mut rt = runtime();
        let setup = "have fn identity(x R) R = x\nclaim:\n    ? forall y R:\n        exist x R st {y = identity(x)}\n    witness exist x R st {y = identity(x)} from y\n";
        assert!(rt.run_litex_code(setup).unwrap().success);
        if property == "injective" {
            let source = "claim:\n    ? forall a, b R:\n        identity(a) = identity(b)\n        =>:\n            a = b\n    identity(a) = a\n    identity(b) = b\n    a = b\n";
            let run = rt.run_litex_code(source).unwrap();
            assert!(
                run.success,
                "{}",
                crate::json_output::emit_run_detailed(&run, &rt, "test", None)
            );
        }
        let source = format!("by def ${property}(R, R, identity)\n");
        let run = rt.run_litex_code(&source).unwrap();
        assert!(run.success, "{source}");
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(result))) =
            &run.statement_results[0]
        else {
            panic!("checked definition");
        };
        let InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) =
            &result.stored.infer
        else {
            panic!("atomic inference");
        };
        let [InferAtomicExceptEqualityResult::BuiltinDefinition(definition)] = rules.as_slice()
        else {
            panic!("mapping inference");
        };
        let (source_id, derived) = match definition {
            InferBuiltinDefinitionResult::Injective(result) => {
                (result.source_fact_id, &result.derived)
            }
            InferBuiltinDefinitionResult::Surjective(result) => {
                (result.source_fact_id, &result.derived)
            }
            _ => panic!("matching mapping branch"),
        };
        assert_eq!(source_id, result.stored.primary_fact_id());
        assert_eq!(derived.len(), 1);
        let derived_id = derived[0].primary_fact_id();
        assert_ne!(source_id, derived_id);
        assert!(matches!(
            rt.fact_by_id_in_stack(derived_id),
            Some(Fact::ForallFact(_))
        ));
        let detail = crate::json_output::emit_run_detailed(&run, &rt, "test", None);
        assert!(
            detail.contains(&source_id.to_string()) && detail.contains(&derived_id.to_string()),
            "{detail}"
        );
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}
