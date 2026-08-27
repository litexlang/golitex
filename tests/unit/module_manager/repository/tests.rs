use super::*;
use crate::test_support::with_standard_library_root;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn exported_symbol_keeps_its_definition_owned_struct_view() {
    run_repository_test_with_large_stack("exported-symbol-struct-view", || {
        let fixture = Fixture::new("exported-symbol-struct-view");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
main = "./main.lit"
consumer = "./consumer.lit"
"#,
        );
        write_file(
            &root.join("main.lit"),
            r#"struct Pair:
    first R
    second R

have pair_value &Pair = (1, 2)
"#,
        );
        write_file(&root.join("consumer.lit"), "main::pair_value.second = 2\n");

        let (ok, output) = run_repository(&root);
        assert!(
            ok,
            "an exported symbol must carry its declaration-owned struct view by SymbolId:\n{output}"
        );
    });
}

#[test]
fn allow_bare_export_collects_recursive_public_symbols_once_per_file() {
    run_repository_test_with_large_stack("allow-bare-recursive-export", || {
        let fixture = Fixture::new("allow-bare-recursive-export");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
A = "./A"
B = "./B"
main = "./main.lit"

[allow bare export]
A
"#,
        );
        write_file(
            &root.join("A/litex.config"),
            r#"[hierarchy]
submodule

[export]
chap2 = "./chap2.lit"
chap3 = "./chap3.lit"
"#,
        );
        write_file(&root.join("A/chap2.lit"), "have x R = 1\n");
        write_file(&root.join("A/chap3.lit"), "A::chap2::x = 1\nhave z R = 1\n");
        write_file(
            &root.join("B/litex.config"),
            "[hierarchy]\nsubmodule\n\n[export]\nconsumer = \"./consumer.lit\"\n",
        );
        write_file(
            &root.join("B/consumer.lit"),
            "z = 1\nhave inherited R = 1\n",
        );
        write_file(
                &root.join("main.lit"),
                "z = 1\nA::chap3::z = 1\nB::consumer::inherited = 1\nhave A R = 1\nA = 1\nstruct Holder:\n    z R\nhave answer R = 1\n",
            );

        let (ok, output) = run_repository(&root);
        assert!(ok, "{output}");
        assert!(output.contains("answer"), "{output}");
    });
}

#[test]
fn allow_bare_import_resolves_flattened_package_symbols() {
    run_repository_test_with_large_stack("allow-bare-flattened-import", || {
        let fixture = Fixture::new("allow-bare-flattened-import");
        let package = fixture.path("package");
        write_file(
            &package.join("litex.config"),
            r#"[hierarchy]
module

[module]
flatten = true

[export]
main = "./main.lit"
"#,
        );
        write_file(
            &package.join("main.lit"),
            "have b R = 1\nhave fn f(x R) R = x + 1\nhave algo for f(x):\n    x + 1\n",
        );

        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import]
A = "../package"

[export]
main = "./main.lit"

[allow bare import]
A
"#,
        );
        write_file(
            &root.join("main.lit"),
            "b = 1\nA::b = 1\neval f(1)\nhave answer R = 1\n",
        );

        let (ok, output) = run_repository(&root);
        assert!(ok, "{output}");

        let python = crate::to_python::to_python_from_repository(
            root.to_str().expect("temporary repository path is UTF-8"),
        )
        .expect("Python project traversal should share allow-bare resolution");
        assert!(python.contains("def f(x):"), "{python}");
    });
}

#[test]
fn allow_bare_standard_import_uses_its_own_opt_in_table() {
    run_repository_test_with_large_stack("allow-bare-standard-import", || {
        let fixture = Fixture::new("allow-bare-standard-import");
        let std_root = fixture.path("std");
        write_file(
            &std_root.join("demo/litex.config"),
            r#"[hierarchy]
module

[module]
flatten = true

[export]
main = "./main.lit"
"#,
        );
        write_file(&std_root.join("demo/main.lit"), "have std_value R = 1\n");

        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import std]
demo

[export]
main = "./main.lit"

[allow bare import std]
demo
"#,
        );
        write_file(
            &root.join("main.lit"),
            "std_value = 1\ndemo::std_value = 1\n",
        );

        with_standard_library_root(&std_root, || {
            let (ok, output) = run_repository(&root);
            assert!(ok, "{output}");
        });
    });
}

#[test]
fn allow_bare_rejects_ambiguous_terminals_and_source_name_reuse() {
    run_repository_test_with_large_stack("allow-bare-conflicts", || {
        let fixture = Fixture::new("allow-bare-conflicts");

        let ambiguous = fixture.path("ambiguous");
        write_file(
            &ambiguous.join("litex.config"),
            r#"[hierarchy]
module

[export]
A = "./A"
main = "./main.lit"

[allow bare export]
A
"#,
        );
        write_file(
            &ambiguous.join("A/litex.config"),
            "[hierarchy]\nsubmodule\n\n[export]\none = \"./one.lit\"\ntwo = \"./two.lit\"\n",
        );
        write_file(&ambiguous.join("A/one.lit"), "have same R = 1\n");
        write_file(&ambiguous.join("A/two.lit"), "have same R = 2\n");
        write_file(&ambiguous.join("main.lit"), "have answer R = 1\n");
        let (ok, output) = run_repository(&ambiguous);
        assert!(!ok, "ambiguous bare names must fail");
        assert!(output.contains("ambiguous bare symbol `same`"), "{output}");
        assert!(output.contains("[allow bare export]"), "{output}");

        let reserved = fixture.path("reserved");
        write_file(
            &reserved.join("litex.config"),
            r#"[hierarchy]
module

[export]
A = "./A"
main = "./main.lit"

[allow bare export]
A
"#,
        );
        write_file(
            &reserved.join("A/litex.config"),
            "[hierarchy]\nsubmodule\n\n[export]\nvalue = \"./value.lit\"\n",
        );
        write_file(&reserved.join("A/value.lit"), "have z R = 1\n");
        write_file(&reserved.join("main.lit"), "have z R = 1\n");
        let (ok, output) = run_repository(&reserved);
        assert!(
            !ok,
            "local declaration must not shadow an allowed bare symbol"
        );
        assert!(output.contains("name `z` is reserved"), "{output}");

        let binder = fixture.path("binder");
        write_file(
            &binder.join("litex.config"),
            r#"[hierarchy]
module

[export]
A = "./A"
main = "./main.lit"

[allow bare export]
A
"#,
        );
        write_file(
            &binder.join("A/litex.config"),
            "[hierarchy]\nsubmodule\n\n[export]\nvalue = \"./value.lit\"\n",
        );
        write_file(&binder.join("A/value.lit"), "have z R = 1\n");
        write_file(&binder.join("main.lit"), "forall z R:\n    z = z\n");
        let (ok, output) = run_repository(&binder);
        assert!(!ok, "source binders must not shadow an allowed bare symbol");
        assert!(output.contains("name `z` is reserved"), "{output}");
    });
}

#[test]
fn allow_bare_export_does_not_reveal_a_later_target_to_an_earlier_file() {
    run_repository_test_with_large_stack("allow-bare-export-boundary", || {
        let fixture = Fixture::new("allow-bare-export-boundary");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
before = "./before.lit"
A = "./A"

[allow bare export]
A
"#,
        );
        write_file(&root.join("before.lit"), "z = 1\n");
        write_file(
            &root.join("A/litex.config"),
            "[hierarchy]\nsubmodule\n\n[export]\nvalue = \"./value.lit\"\n",
        );
        write_file(&root.join("A/value.lit"), "have z R = 1\n");

        let (ok, output) = run_repository(&root);
        assert!(!ok, "a later export must not leak into an earlier file");
        assert!(!output.contains("A::value::z = 1"), "{output}");
    });
}

#[test]
fn full_module_run_follows_recursive_export_order() {
    run_repository_test_with_large_stack("full-recursive-order", || {
        let fixture = Fixture::new("full-recursive-order");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
root_first = "./root_first.lit"
B = "./B"
root_last = "./root_last.lit"
"#,
        );
        write_file(&root.join("root_first.lit"), "have root_value R = 1\n");
        write_file(
            &root.join("root_last.lit"),
            "B::b_last::b_last_value = 1\nhave answer R = 1\n",
        );
        write_file(
            &root.join("B/litex.config"),
            r#"[hierarchy]
submodule

[export]
b_first = "./b_first.lit"
c = "./c"
b_last = "./b_last.lit"
"#,
        );
        write_file(
            &root.join("B/b_first.lit"),
            "root_first::root_value = 1\nhave b_value R = 1\n",
        );
        write_file(
            &root.join("B/b_last.lit"),
            "B::c::tail::tail_value = 1\nhave b_last_value R = 1\n",
        );
        write_file(
            &root.join("B/c/litex.config"),
            r#"[hierarchy]
submodule

[export]
target = "./target.lit"
tail = "./tail.lit"
"#,
        );
        write_file(
            &root.join("B/c/target.lit"),
            "B::b_first::b_value = 1\nhave c_value R = 1\n",
        );
        write_file(
            &root.join("B/c/tail.lit"),
            "B::c::target::c_value = 1\nhave tail_value R = 1\n",
        );

        let (ok, output) = run_repository(&root);
        assert!(ok, "{output}");
        assert!(output.contains("answer"), "{output}");
    });
}

#[test]
fn submodule_run_traces_to_root_and_runs_the_selected_subtree() {
    run_repository_test_with_large_stack("submodule-prefix", || {
        let fixture = Fixture::new("submodule-prefix");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
root_first = "./root_first.lit"
B = "./B"
root_after = "./root_after.lit"
"#,
        );
        write_file(&root.join("root_first.lit"), "have root_value R = 1\n");
        write_file(&root.join("root_after.lit"), "1 = 0\n");
        write_file(
            &root.join("B/litex.config"),
            r#"[hierarchy]
submodule

[export]
b_first = "./b_first.lit"
c = "./c"
b_after = "./b_after.lit"
"#,
        );
        write_file(
            &root.join("B/b_first.lit"),
            "root_first::root_value = 1\nhave b_value R = 1\n",
        );
        write_file(&root.join("B/b_after.lit"), "1 = 0\n");
        write_file(
            &root.join("B/c/litex.config"),
            r#"[hierarchy]
submodule

[export]
target = "./target.lit"
tail = "./tail.lit"
"#,
        );
        write_file(
            &root.join("B/c/target.lit"),
            "B::b_first::b_value = 1\nhave c_value R = 1\n",
        );
        write_file(&root.join("B/c/tail.lit"), "1 = 0\n");

        let target_path = path_string_for_test(&root.join("B/c"));
        let (tail_ok, _) = run_repository_for_test(
            target_path.as_str(),
            false,
            true,
            OutputLanguage::English,
            false,
        );
        assert!(
            !tail_ok,
            "running a submodule must run its complete subtree"
        );

        write_file(
            &root.join("B/c/tail.lit"),
            "B::c::target::c_value = 1\nhave tail_value R = 1\n",
        );
        let (ok, output) = run_repository_for_test(
            target_path.as_str(),
            false,
            true,
            OutputLanguage::English,
            false,
        );
        assert!(ok, "{output}");
        assert!(output.contains("tail_value"), "{output}");
    });
}

#[test]
fn registered_file_run_stops_at_that_file_in_recursive_order() {
    run_repository_test_with_large_stack("file-prefix", || {
        let fixture = Fixture::new("file-prefix");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
root_first = "./root_first.lit"
B = "./B"
root_after = "./root_after.lit"
"#,
        );
        write_file(
            &root.join("root_first.lit"),
            "have root_value R = 1\n1 = 0\n",
        );
        write_file(&root.join("root_after.lit"), "1 = 0\n");
        write_file(
            &root.join("B/litex.config"),
            r#"[hierarchy]
submodule

[export]
before = "./before.lit"
target = "./target.lit"
after = "./after.lit"
"#,
        );
        write_file(
            &root.join("B/before.lit"),
            "root_first::root_value = 1\nhave before_value R = 1\n",
        );
        write_file(
            &root.join("B/target.lit"),
            "B::before::before_value = 1\nhave target_value R = 1\n",
        );
        write_file(&root.join("B/after.lit"), "1 = 0\n");

        let target = path_string_for_test(&root.join("B/target.lit"));
        let (ok, output) = run_file_for_test(target.as_str());
        assert!(ok, "{output}");
        assert!(output.contains("target_value"), "{output}");
        assert!(output.contains("project_export"), "{output}");

        let (project_ok, project_output) = run_repository(&root);
        assert!(
            !project_ok,
            "a complete project run must verify the earlier export: {project_output}"
        );
        assert!(project_output.contains("1 = 0"), "{project_output}");

        let mut strict_runtime = Runtime::default();
        strict_runtime.options.strict_mode = true;
        let (_, strict_error) = execute_file_in_runtime(
            target.as_str(),
            &mut strict_runtime,
            FileExecutionOptions::default(),
        );
        let strict_error = strict_error.expect("strict -f must verify its export prefix");
        assert!(format!("{strict_error:?}").contains("1 = 0"));
    });
}

#[test]
fn file_without_a_direct_parent_config_requires_isolated_flag() {
    run_repository_test_with_large_stack("isolated-direct-parent", || {
        let fixture = Fixture::new("isolated-direct-parent");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
        );
        write_file(&root.join("main.lit"), "have configured R = 1\n");
        write_file(
            &root.join("unconfigured/deep.lit"),
            "have isolated_value R = 1\n",
        );

        let file = path_string_for_test(&root.join("unconfigured/deep.lit"));
        let (ok, output) = run_file_for_test(file.as_str());
        assert!(!ok, "{output}");
        assert!(
            output.contains("requires a litex.config in the same folder"),
            "{output}"
        );
    });
}

#[test]
fn configured_imported_qualified_values_participate_in_calculation() {
    run_repository_test_with_large_stack("configured-import-qualified-calculation", || {
        let fixture = Fixture::new("configured-import-qualified-calculation");
        let module_root = fixture.path("geometry-foundation");
        let root = fixture.path("root");
        write_file(
            &module_root.join("litex.config"),
            r#"[hierarchy]
module

[export]
main = "./main.lit"
main2 = "./main2.lit"
"#,
        );
        write_file(
            &module_root.join("main.lit"),
            "have a R = 1\nhave pair cart(R, R) = (3, 4)\nhave ProductSet set = cart(R, R)\n",
        );
        write_file(
            &module_root.join("main2.lit"),
            "have b R = 2\nhave pair cart(R, R) = (8, 9)\n",
        );
        write_file(
            &root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[import]\ngf = \"../geometry-foundation\"\n\n[export]\nmain = \"./main.lit\"\n",
        );
        write_file(
            &root.join("main.lit"),
            "gf::main::a + gf::main::a = gf::main2::b\ngf::main::pair[1] = 3\ngf::main2::pair[1] = 8\ncart_dim(gf::main::ProductSet) = 2\n",
        );
        let (ok, output) = run_repository(&root);
        assert!(ok, "{output}");
    });
}

#[test]
fn configured_imported_qualified_direct_cached_properties_remain_usable() {
    run_repository_test_with_large_stack("configured-import-qualified-properties", || {
        let fixture = Fixture::new("configured-import-qualified-properties");
        let module_root = fixture.path("property-library");
        let root = fixture.path("root");
        write_file(
            &module_root.join("litex.config"),
            r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
        );
        write_file(
            &module_root.join("main.lit"),
            r#"have entries finite_seq(R, 2) = [5, 6]
have fn inc(x R) R = x + 1
have positives power_set(R) = {x R: x > 0}
have mat matrix(R, 2, 2) = [[1, 2], [3, 4]]
have pair cart(R, R) = (3, 4)
have ProductSet set = cart(R, R)
"#,
        );
        write_file(
            &root.join("litex.config"),
            "[hierarchy]\nmodule\n\n[import]\nlib = \"../property-library\"\n\n[export]\nmain = \"./main.lit\"\n",
        );
        write_file(
            &root.join("main.lit"),
            "lib::main::entries(2) = 6\nlib::main::inc(2) = 3\n1 $in lib::main::positives\nlib::main::mat(1, 2) = 2\nlib::main::pair[1] = 3\ncart_dim(lib::main::ProductSet) = 2\n",
        );
        let outcome = run(RunRequest::new(
            RunTarget::repository(path_string_for_test(&root).as_str()),
            RunOptions::default(),
        ));
        assert!(outcome.ok, "{}", outcome.output);
        let runtime = outcome.runtime;

        let imported_environment = runtime
            .imported_module_environments("lib::main")
            .into_iter()
            .next()
            .expect("imported main environment should exist");
        let pair_symbol = imported_environment
            .definitions
            .symbols
            .get("pair")
            .map(|definition| definition.binding().as_ref())
            .expect("imported pair binding should exist");
        let pair_symbol_id = pair_symbol.id().value();
        let local_pair: Obj = Identifier::new_bound("pair".to_string(), pair_symbol.clone()).into();
        let qualified_pair: Obj =
            IdentifierWithMod::new_bound("lib::main".to_string(), "pair".to_string(), pair_symbol)
                .into();
        let canonical_pair_key = qualified_pair.to_string();
        assert_eq!(
            canonical_pair_key,
            format!("lib::main::#{}#pair", pair_symbol_id),
            "the symbol identity must follow its canonical module owner"
        );
        let local_dim: Obj = TupleDim::new(local_pair).into();
        let qualified_dim: Obj = TupleDim::new(qualified_pair).into();
        assert_eq!(local_dim.to_string(), qualified_dim.to_string());
        assert_eq!(
            strip_free_param_numeric_tags_in_display(&qualified_dim.to_string()),
            "tuple_dim(lib::main::pair)",
            "the canonical compound key must retain its module owner"
        );
        assert!(
            imported_environment
                .facts
                .known_equality
                .get(&qualified_dim.to_string())
                .is_some(),
            "the module environment must store the fully canonical tuple_dim key"
        );
        assert!(
            imported_environment
                .objects
                .knowledge(&canonical_pair_key)
                .is_some_and(|knowledge| knowledge.tuple_equality.is_some()),
            "the module environment must store the fully canonical pair key"
        );
        assert!(
            !imported_environment
                .objects
                .knowledge("pair")
                .is_some_and(|knowledge| knowledge.tuple_equality.is_some()),
            "module lookup must not rely on a stripped local cache alias"
        );
        assert_eq!(
            runtime
                .resolve_obj_to_number(&qualified_dim)
                .map(|number| number.to_string()),
            Some("2".to_string()),
            "qualified tuple dimension should use the module's canonical cache key"
        );
    });
}

#[test]
fn module_source_rejects_terminal_import_syntax() {
    let fixture = Fixture::new("module-source-import");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "import std basics\n");

    let (ok, output) = run_repository(&root);
    assert!(!ok, "{output}");
    assert!(
        output.contains("`import` is a terminal command, not a Litex statement"),
        "{output}"
    );
}

#[test]
fn configured_folder_allows_non_litex_artifacts() {
    let fixture = Fixture::new("unexported-child");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");
    write_file(&root.join("README.md"), "not exported\n");

    let (ok, output) = run_repository(&root);
    assert!(ok, "{output}");
}

#[test]
fn configured_folder_allows_comment_only_todo_sidecar() {
    let fixture = Fixture::new("todo-sidecar");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");
    write_file(&root.join("todo.lit"), "# Missing mathematical result.\n");

    let (ok, output) = run_repository(&root);
    assert!(ok, "{output}");
}

#[test]
fn configured_folder_allows_documentation_only_todo_sidecar() {
    let fixture = Fixture::new("documentation-todo-sidecar");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");
    write_file(
        &root.join("todo.lit"),
        "\"\"\"\nMissing mathematical result.\n\"\"\"\n",
    );

    let (ok, output) = run_repository(&root);
    assert!(ok, "{output}");
}

#[test]
fn configured_folder_rejects_executable_todo_sidecar() {
    let fixture = Fixture::new("executable-todo-sidecar");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");
    write_file(
        &root.join("todo.lit"),
        "\"\"\"\nDocumentation only.\n\"\"\"\nhave hidden R = 2\n",
    );

    let (ok, output) = run_repository(&root);
    assert!(!ok, "{output}");
    assert!(output.contains("todo.lit must be comment-only"), "{output}");
}

#[test]
fn export_paths_must_name_exactly_one_direct_child() {
    let fixture = Fixture::new("direct-child-export");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./nested/main.lit"
"#,
    );
    write_file(&root.join("nested/main.lit"), "have value R = 1\n");

    let (ok, output) = run_repository(&root);
    assert!(!ok);
    assert!(
        output.contains("[export] paths must name exactly one direct child"),
        "{output}"
    );
}

#[test]
fn exported_folders_must_be_submodules() {
    let fixture = Fixture::new("folder-hierarchy");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
Child = "./Child"
"#,
    );
    write_file(
        &root.join("Child/litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("Child/main.lit"), "have value R = 1\n");

    let (ok, output) = run_repository(&root);
    assert!(!ok);
    assert!(
        output.contains("folder target must declare `submodule`"),
        "{output}"
    );
}

#[test]
fn imports_only_accept_external_module_folders() {
    let fixture = Fixture::new("module-only-import");
    let root = fixture.path("root");
    let dependency = fixture.path("dependency");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[import]
Dependency = "../dependency"

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");
    write_file(
        &dependency.join("litex.config"),
        r#"[hierarchy]
submodule

[export]
main = "./main.lit"
"#,
    );
    write_file(&dependency.join("main.lit"), "have value R = 1\n");

    let (ok, output) = run_repository(&root);
    assert!(!ok);
    assert!(
        output.contains("[import] target must declare `module`"),
        "{output}"
    );

    write_file(
        &dependency.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[import]
Dependency = "./Dependency"

[export]
DependencyFolder = "./Dependency"
main = "./main.lit"
"#,
    );
    write_file(
        &root.join("Dependency/litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("Dependency/main.lit"), "have value R = 1\n");

    let (descendant_ok, descendant_output) = run_repository(&root);
    assert!(!descendant_ok);
    assert!(
        descendant_output.contains("not a descendant of the current module"),
        "{descendant_output}"
    );
}

#[test]
fn imports_reject_file_targets() {
    let fixture = Fixture::new("file-import");
    let root = fixture.path("root");
    write_file(&fixture.path("dependency.lit"), "have value R = 1\n");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[import]
Dependency = "../dependency.lit"

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");

    let (ok, output) = run_repository(&root);
    assert!(!ok);
    assert!(output.contains("is not a directory"), "{output}");
}

#[test]
fn file_in_a_configured_folder_must_be_exported() {
    let fixture = Fixture::new("unexported-file-target");
    let root = fixture.path("root");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have value R = 1\n");
    write_file(&root.join("extra.lit"), "have extra R = 1\n");

    let extra = path_string_for_test(&root.join("extra.lit"));
    let (ok, output) = run_file_for_test(extra.as_str());
    assert!(!ok);
    assert!(
        output.contains("unexported Litex module path `extra.lit`"),
        "{output}"
    );
}

#[test]
fn two_aliases_of_one_physical_module_are_rejected() {
    run_repository_test_with_large_stack("duplicate-physical-import", || {
        let fixture = Fixture::new("duplicate-physical-import");
        let root = fixture.path("root");
        let dependency = fixture.path("dependency");
        write_file(
            &dependency.join("litex.config"),
            r#"[hierarchy]
module

[export]
implementation = "./main.lit"
"#,
        );
        write_file(&dependency.join("main.lit"), "have value R = 1\n");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import]
First = "../dependency"
Second = "../dependency"

[export]
main = "./main.lit"
"#,
        );
        write_file(&root.join("main.lit"), "have answer R = 1\n");

        let (ok, output) = run_repository(&root);
        assert!(!ok, "{output}");
        assert!(output.contains("duplicate alias `Second`"), "{output}");
    });
}

#[test]
fn diamond_imports_share_one_physical_module() {
    run_repository_test_with_large_stack("shared-diamond-import", || {
        let fixture = Fixture::new("shared-diamond-import");
        let root = fixture.path("root");
        let left = fixture.path("left");
        let right = fixture.path("right");
        let shared = fixture.path("shared");
        write_file(
            &shared.join("litex.config"),
            r#"[hierarchy]
module

[export]
implementation = "./main.lit"
"#,
        );
        write_file(&shared.join("main.lit"), "have token R = 1\n");
        for (module, object_name) in [(&left, "left_value"), (&right, "right_value")] {
            write_file(
                &module.join("litex.config"),
                r#"[hierarchy]
module

[import]
Shared = "../shared"

[export]
implementation = "./main.lit"
"#,
            );
            write_file(
                &module.join("main.lit"),
                &format!(
                    "Shared::implementation::token = 1\nhave {} R = 1\n",
                    object_name
                ),
            );
        }
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import]
Left = "../left"
Right = "../right"

[export]
main = "./main.lit"
"#,
        );
        write_file(
            &root.join("main.lit"),
            "Left::implementation::left_value = 1\nRight::implementation::right_value = 1\n",
        );

        let root_string = path_string_for_test(&root);
        let mut runtime = Runtime::default();
        discover_repository(&mut runtime, root_string.as_str()).expect("discover diamond");
        let left_id = runtime.module_manager.module_id_by_name("Left").unwrap();
        let right_id = runtime.module_manager.module_id_by_name("Right").unwrap();
        let left_shared = runtime
            .module_manager
            .module(left_id)
            .unwrap()
            .config_imports[0]
            .module_id;
        let right_shared = runtime
            .module_manager
            .module(right_id)
            .unwrap()
            .config_imports[0]
            .module_id;
        assert_eq!(left_shared, right_shared);

        let (ok, output) = run_repository(&root);
        assert!(ok, "{output}");
    });
}

#[test]
fn imported_modules_keep_their_own_imports_private() {
    let fixture = Fixture::new("private-imports");
    let root = fixture.path("root");
    let dependency = fixture.path("dependency");
    let support = fixture.path("support");
    write_file(
        &support.join("litex.config"),
        r#"[hierarchy]
module

[export]
implementation = "./main.lit"
"#,
    );
    write_file(&support.join("main.lit"), "have value R = 1\n");
    write_file(
        &dependency.join("litex.config"),
        r#"[hierarchy]
module

[import]
Support = "../support"

[export]
implementation = "./main.lit"
"#,
    );
    write_file(
        &dependency.join("main.lit"),
        "Support::implementation::value = 1\nhave value R = 1\n",
    );
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[import]
Dependency = "../dependency"

[export]
main = "./main.lit"
"#,
    );
    write_file(
        &root.join("main.lit"),
        "Dependency::Support::implementation::value = 1\n",
    );

    let (ok, output) = run_repository(&root);
    assert!(!ok);
    assert!(output.contains("not authorized"), "{output}");
}

#[test]
fn config_import_cycles_are_rejected_by_physical_module_path() {
    let fixture = Fixture::new("import-cycle");
    let root = fixture.path("root");
    let dependency = fixture.path("dependency");
    write_file(
        &root.join("litex.config"),
        r#"[hierarchy]
module

[import]
Dependency = "../dependency"

[export]
main = "./main.lit"
"#,
    );
    write_file(&root.join("main.lit"), "have root_value R = 1\n");
    write_file(
        &dependency.join("litex.config"),
        r#"[hierarchy]
module

[import]
RootAgain = "../root"

[export]
main = "./main.lit"
"#,
    );
    write_file(
        &dependency.join("main.lit"),
        "have dependency_value R = 1\n",
    );

    let (ok, output) = run_repository(&root);
    assert!(!ok);
    assert!(output.contains("cyclic config import"), "{output}");
}

#[test]
fn standard_imports_expose_flattened_package_names() {
    run_repository_test_with_large_stack("standard-import", || {
        let fixture = Fixture::new("standard-import");
        let root = fixture.path("root");
        let std_root = fixture.path("std");
        write_file(
            &std_root.join("basics/litex.config"),
            r#"[hierarchy]
module

[module]
flatten = true

[export]
main = "./main.lit"
"#,
        );
        write_file(&std_root.join("basics/main.lit"), "have value R = 1\n");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import std]
basics

[export]
main = "./main.lit"
"#,
        );
        write_file(
            &root.join("main.lit"),
            "basics::value = 1\nhave answer R = 1\n",
        );

        with_standard_library_root(&std_root, || {
            let (ok, output) = run_repository(&root);
            assert!(ok, "{output}");
        });
    });
}

#[test]
fn exports_are_verified_by_default_and_strict_mode_rejects_user_trust() {
    run_repository_test_with_large_stack("verified-export", || {
        let fixture = Fixture::new("verified-export");
        let root = fixture.path("root");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[export]
assumption = "./assumption.lit"
main = "./main.lit"
"#,
        );
        write_file(&root.join("assumption.lit"), "1 = 0\n");
        write_file(&root.join("main.lit"), "have value R = 1\n");

        let root_string = path_string_for_test(&root);
        let (ordinary_ok, ordinary_output) = run_repository_for_test(
            root_string.as_str(),
            false,
            false,
            OutputLanguage::English,
            true,
        );
        assert!(!ordinary_ok, "{ordinary_output}");
        assert!(ordinary_output.contains("1 = 0"), "{ordinary_output}");
        assert!(
            !ordinary_output.contains("project_export"),
            "ordinary project runs must not trust [export] entries: {ordinary_output}"
        );

        write_file(&root.join("assumption.lit"), "trust 1 = 1\n");
        let (ordinary_trust_ok, ordinary_trust_output) = run_repository_for_test(
            root_string.as_str(),
            false,
            false,
            OutputLanguage::English,
            true,
        );
        assert!(ordinary_trust_ok, "{ordinary_trust_output}");
        let (strict_ok, strict_output) = run_repository_for_test(
            root_string.as_str(),
            false,
            true,
            OutputLanguage::English,
            false,
        );
        assert!(!strict_ok);
        assert!(
            strict_output.contains("strict mode rejects user trust"),
            "{strict_output}"
        );
    });
}

#[test]
fn imports_are_trusted_by_default_and_strict_mode_verifies_them() {
    run_repository_test_with_large_stack("default-trusted-import", || {
        let fixture = Fixture::new("default-trusted-import");
        let root = fixture.path("root");
        let dependency = fixture.path("dependency");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import]
Dependency = "../dependency"

[export]
main = "./main.lit"
"#,
        );
        write_file(&root.join("main.lit"), "have value R = 1\n");
        write_file(
            &dependency.join("litex.config"),
            r#"[hierarchy]
module

[export]
assumption = "./assumption.lit"
"#,
        );
        write_file(&dependency.join("assumption.lit"), "1 = 0\n");

        let root_string = path_string_for_test(&root);
        let (ordinary_ok, ordinary_output) = run_repository_for_test(
            root_string.as_str(),
            false,
            false,
            OutputLanguage::English,
            true,
        );
        assert!(ordinary_ok, "{ordinary_output}");
        assert!(ordinary_output.contains("\"kind\": \"project_import\""));
        assert!(ordinary_output.contains("\"name\": \"Dependency\""));
        let (strict_ok, strict_output) = run_repository_for_test(
            root_string.as_str(),
            false,
            true,
            OutputLanguage::English,
            false,
        );
        assert!(!strict_ok);
        assert!(strict_output.contains("1 = 0"), "{strict_output}");
    });
}

#[test]
fn strict_mode_rejects_user_trust_in_project_imports() {
    run_repository_test_with_large_stack("strict-project-import-trust", || {
        let fixture = Fixture::new("strict-project-import-trust");
        let root = fixture.path("root");
        let dependency = fixture.path("dependency");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import]
Dependency = "../dependency"

[export]
main = "./main.lit"
"#,
        );
        write_file(&root.join("main.lit"), "have value R = 1\n");
        write_file(
            &dependency.join("litex.config"),
            r#"[hierarchy]
module

[export]
main = "./main.lit"
"#,
        );
        write_file(&dependency.join("main.lit"), "trust 1 = 1\n");

        let root_string = path_string_for_test(&root);
        let (strict_ok, strict_output) = run_repository_for_test(
            root_string.as_str(),
            false,
            true,
            OutputLanguage::English,
            false,
        );
        assert!(!strict_ok, "{strict_output}");
        assert!(
            strict_output.contains("strict mode rejects user trust"),
            "{strict_output}"
        );
    });
}

#[test]
fn strict_mode_preserves_standard_library_trust_boundary() {
    run_repository_test_with_large_stack("strict-standard-trust", || {
        let fixture = Fixture::new("strict-standard-trust");
        let root = fixture.path("root");
        let std_root = fixture.path("std");
        write_file(
            &std_root.join("basics/litex.config"),
            r#"[hierarchy]
module

[module]
flatten = true

[export]
main = "./main.lit"
"#,
        );
        write_file(&std_root.join("basics/main.lit"), "trust 1 = 0\n");
        write_file(
            &root.join("litex.config"),
            r#"[hierarchy]
module

[import std]
basics

[export]
main = "./main.lit"
"#,
        );
        write_file(&root.join("main.lit"), "have value R = 1\n");

        with_standard_library_root(&std_root, || {
            let root_string = path_string_for_test(&root);
            let (strict_ok, strict_output) = run_repository_for_test(
                root_string.as_str(),
                false,
                true,
                OutputLanguage::English,
                false,
            );
            assert!(strict_ok, "{strict_output}");
        });
    });
}

#[test]
fn standard_library_root_candidates_cover_installed_layouts() {
    let configured = PathBuf::from("/configured/std");
    let current = PathBuf::from("/workspace/project");
    let executable = PathBuf::from("/install/bin/litex");
    let candidates =
        standard_library_root_candidates(Some(configured.clone()), Some(current), Some(executable));

    assert_eq!(candidates.first(), Some(&configured));
    assert!(candidates.contains(&PathBuf::from("/workspace/project/std")));
    assert!(candidates.contains(&PathBuf::from("/install/bin/../std")));
    assert!(candidates.contains(&PathBuf::from("/install/bin/../share/litex/std")));
}

fn run_repository(path: &Path) -> (bool, String) {
    let path = path_string_for_test(path);
    run_repository_for_test(path.as_str(), false, false, OutputLanguage::English, false)
}

fn run_repository_for_test(
    repository_path: &str,
    detailed_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    let outcome = run(RunRequest::new(
        RunTarget::repository(repository_path),
        RunOptions {
            output_style: if detailed_output {
                OutputStyle::Detailed
            } else {
                OutputStyle::Normal
            },
            strict_mode,
            output_language,
            summarize,
            ..RunOptions::default()
        },
    ));
    (outcome.ok, outcome.output)
}

fn run_file_for_test(file_path: &str) -> (bool, String) {
    let outcome = run(RunRequest::new(
        RunTarget::file(file_path),
        RunOptions::default(),
    ));
    (outcome.ok, outcome.output)
}

fn path_string_for_test(path: &Path) -> String {
    path.to_str().expect("fixture path is UTF-8").to_string()
}

fn write_file(path: &Path, source: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("create fixture directory");
    }
    fs::write(path, source).expect("write fixture file");
}

fn run_repository_test_with_large_stack(name: &str, test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(name.to_string())
        .stack_size(8 * 1024 * 1024)
        .spawn(test)
        .expect("spawn repository test")
        .join()
        .unwrap();
}

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn new(name: &str) -> Self {
        static NEXT_ID: AtomicUsize = AtomicUsize::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-hierarchy-{name}-{}-{id}",
            std::process::id()
        ));
        if root.exists() {
            fs::remove_dir_all(&root).expect("remove stale fixture");
        }
        fs::create_dir_all(&root).expect("create fixture root");
        Fixture { root }
    }

    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
