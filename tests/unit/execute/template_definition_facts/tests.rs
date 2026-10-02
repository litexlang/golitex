use crate::ast::fact::Fact;
use crate::execute::execute_def_template_stmt::ExecDefTemplateStmtResult;
use crate::execute::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::{CodeSource, Runtime};

#[test]
fn run_examples_member_definition_exports_a_known_forall_with_body_evidence() {
    let mut rt = runtime(true);
    let code = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/stmt_nodes/definition/template_definition_facts.lit"
    ));
    let result = rt.run_litex_code(code).unwrap();
    assert!(result.success, "{:?}", result.session_error);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(template),
    )) = &result.statement_results[0]
    else {
        panic!("successful template");
    };
    assert!(!template.definition_facts.is_empty());
    for published in &template.definition_facts {
        assert!(template
            .local_env
            .facts
            .facts_by_id
            .contains_key(&published.source_fact_id));
        let Fact::ForallFact(forall) = rt
            .fact_by_id_in_stack(published.store_and_infer.primary_fact_id())
            .unwrap()
        else {
            panic!("published definition must be quantified");
        };
        assert_eq!(forall.typed_parameters, template.statement.template_arg_def);
        assert!(forall.dom_facts.is_empty());
        assert_ne!(published.source_fact_id, forall.fact_id);
    }
    let json = crate::json_output::project_stmt_normal(&result.statement_results[1], &rt);
    assert!(
        json.stringify().contains("cite_forall"),
        "{}",
        json.stringify()
    );
}

#[test]
fn set_kinds_and_dependent_object_definitions_export_facts() {
    check("template<S nonempty_set>:\n    have nonempty nonempty_set = S\n$is_nonempty_set(\\nonempty<R>)\ntemplate<n N>:\n    have finite finite_set = {n}\n$is_finite_set(\\finite<2>)\ntemplate<S set>:\n    have carrier set = S\n\\carrier<R> = R\ntemplate<S nonempty_set, a S>:\n    have selected S = a\n\\selected<R, 2> $in R\n\\selected<R, 2> = 2\n", &[true; 9]);
}

#[test]
fn existential_object_and_both_obtain_forms_export_the_selected_properties() {
    check("witness exist x R st {x = 2} from 2\ntemplate<S set>:\n    have existing R:\n        existing = 2\n\\existing<R> = 2\ntemplate<S set>:\n    obtain obtained from exist x R st {x = 2}\n\\obtained<R> = 2\nprop has_copy(a R):\n    exist x R st {x = a}\nwitness $has_copy(4) from 4\ntemplate<S set>:\n    obtain atomic from $has_copy(4)\n\\atomic<R> = 4\n", &[true; 9]);
}

#[test]
fn replacement_exports_membership_and_its_existential_elimination() {
    check("prop image_rel(x, y set):\n    x = y\nforall x {1}, y, z set:\n    $image_rel(x, y)\n    $image_rel(x, z)\n    =>:\n        y = z\ntemplate<S set>:\n    have by replacement_axiom: image from prop image_rel, set {1}\nby def $image_rel(1, 1)\n1 $in \\image<R>\nforall y \\image<R>:\n    exist x {1} st {$image_rel(x, y)}\n", &[true; 6]);
}

#[test]
fn formula_piecewise_and_recursive_function_definitions_export_guarded_facts() {
    check("template<S set>:\n    have fn ident(x S) S = x\n\\ident<R> $in fn(x R) R\n\\ident<R>(4) = 4\n", &[true; 3]);
    check("template<T set>:\n    have fn flag(x R) N by cases:\n        case x = 0: 0\n        case x != 0: 1\n\\flag<R> $in fn(x R) N\n\\flag<R>(0) = 0\n\\flag<R>(1) = 1\n\\flag<R>(0) = 1\n", &[true, true, true, true, false]);
    check("template<b N>:\n    have fn count(n N) N by induc n from 0:\n        case n = 0: b\n        case n >= 1: count(n - 1) + 1\n\\count<2> $in fn(n N) N\n\\count<2>(1 - 1) = 2\n\\count<2>(1) = \\count<2>(1 - 1) + 1 = 3\n\\count<7>(1 - 1) = 7\n\\count<7>(1) = \\count<7>(1 - 1) + 1 = 8\n\\count<7>(1) = 3\n", &[true, true, true, true, true, true, false]);
}

#[test]
fn unique_function_exports_property_and_uniqueness() {
    check("prop successor_rel(x, y R):\n    y = x + 1\nclaim:\n    ? forall x R:\n        exist! y R st {$successor_rel(x, y)}\n    witness exist! y R st {$successor_rel(x, y)} from x + 1:\n        by def $successor_rel(x, x + 1)\ntemplate<S set>:\n    have fn chosen by exist!:\n        ? forall x R:\n            exist! y R st {$successor_rel(x, y)}\n\\chosen<R> $in fn(x R) R\n$successor_rel(2, \\chosen<R>(2))\nforall x, y R:\n    $successor_rel(x, y)\n    =>:\n        y = \\chosen<R>(x)\n$successor_rel(3, \\chosen<R>(2))\n", &[true, true, true, true, true, true, false]);
}

#[test]
fn trust_body_exports_quantified_facts_and_still_requires_nonstrict_mode() {
    let code = "template<S set>:\n    trust have assumed R:\n        assumed = 5\n        forall x R:\n            assumed + x = x + 5\n\\assumed<R> = 5\n\\assumed<R> + 2 = 7\n";
    check(code, &[true; 3]);
    let mut strict = runtime(true);
    let result = strict
        .run_litex_code("template<S set>:\n    trust have assumed R:\n        assumed = 5\n")
        .unwrap();
    assert!(!result.success);
    assert!(!strict
        .top_exec_env()
        .definitions
        .template_definitions
        .contains_key("assumed"));
}

#[test]
fn template_domains_are_retained_and_do_not_become_ambient_assumptions() {
    let mut rt = runtime(false);
    let result = rt.run_litex_code("template<S set: $is_nonempty_set(S)>:\n    have positive S\n\\positive<R> $in R\n$is_nonempty_set({})\n").unwrap();
    assert!(result.session_error.is_none(), "{:?}", result.session_error);
    assert_eq!(
        result
            .statement_results
            .iter()
            .map(|r| !r.is_failed())
            .collect::<Vec<_>>(),
        vec![true, true, false]
    );
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(
        ExecDefTemplateStmtResult::Success(template),
    )) = &result.statement_results[0]
    else {
        panic!("successful template");
    };
    for published in &template.definition_facts {
        let Fact::ForallFact(forall) = rt
            .fact_by_id_in_stack(published.store_and_infer.primary_fact_id())
            .unwrap()
        else {
            panic!("forall");
        };
        assert_eq!(forall.dom_facts.len(), 1);
    }
    let bad = rt.run_litex_code("\\positive<{}> $in R\n").unwrap();
    assert!(
        !bad.success,
        "invalid template argument must remain rejected"
    );
}

#[test]
fn failed_template_and_failed_enclosing_claim_discard_published_facts() {
    check("template<S set>:\n    have member S\ntemplate<T nonempty_set>:\n    have member T\n\\member<R> $in R\n\\member<{1, 2}> = 1\n\\member<{1}> $in {2}\n", &[false, true, true, false, false]);
    let mut rt = runtime(false);
    let result = rt.run_litex_code("claim:\n    ? 0 = 1\n    template<S nonempty_set>:\n        have member S\n    \\member<R> $in R\nlet member = 0\nmember = 0\n0 = 1\n").unwrap();
    assert!(result.session_error.is_none(), "{:?}", result.session_error);
    assert_eq!(
        result
            .statement_results
            .iter()
            .map(|r| !r.is_failed())
            .collect::<Vec<_>>(),
        vec![false, true, true, false]
    );
    assert!(rt
        .top_exec_env()
        .definitions
        .template_definitions
        .is_empty());
    assert!(rt
        .top_exec_env()
        .facts
        .known_forall_conclusions
        .by_atomic_prop
        .is_empty());
}

#[test]
fn template_definition_stores_are_visible_in_normal_and_detailed_json() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut rt = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
            language,
        });
        let result = rt
            .run_litex_code("template<S nonempty_set>:\n    have member S\n")
            .unwrap();
        assert!(result.success);
        for json in [
            crate::json_output::project_stmt_normal(&result.statement_results[0], &rt),
            crate::json_output::project_stmt_detailed(&result.statement_results[0], &rt),
        ] {
            let text = json.stringify();
            assert!(text.contains("member<S>"), "{text}");
            assert!(!text.contains("local_env"));
        }
    }
}

fn runtime(strict: bool) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict,
        language: OutputLanguage::English,
    })
}

fn check(code: &str, expected: &[bool]) {
    for source in [
        CodeSource::Eval,
        CodeSource::RootExport { export_file_id: 2 },
        CodeSource::ImportedExport {
            global_mod_id: 3,
            export_file_id: 2,
        },
    ] {
        let mut rt = runtime(false);
        rt.set_code_source(source);
        let result = rt.run_litex_code(code).unwrap();
        assert!(
            result.session_error.is_none(),
            "{:?}\n{code}",
            result.session_error
        );
        let actual: Vec<_> = result
            .statement_results
            .iter()
            .map(|r| !r.is_failed())
            .collect();
        assert_eq!(actual, expected, "{code}");
    }
}
