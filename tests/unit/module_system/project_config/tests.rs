use super::*;

#[test]
fn parses_an_ordered_export_plan() {
    let config = parse_project_config(
            "[hierarchy]\nmodule\n\n[export]\nchapter1 = \"./chapter01.lit\"\nAlgebra = \"./Algebra\"\n",
            "litex.config",
        )
        .expect("parse ordered export plan");
    assert_eq!(config.hierarchy, ProjectHierarchy::Module);
    assert_eq!(config.exports.len(), 2);
    assert_eq!(config.exports[0].name, "chapter1");
    assert_eq!(config.exports[1].name, "Algebra");
}

#[test]
fn parses_module_imports() {
    let config = parse_project_config(
            "[hierarchy]\nmodule\n\n[import]\nAlgebra = \"../algebra\"\n\n[export]\nchap3 = \"./chap3.lit\"\nchap7 = \"./chap7.lit\"\n",
            "litex.config",
        )
        .expect("parse dependency configuration");
    assert_eq!(config.imports.len(), 1);
    assert_eq!(config.imports[0].name, "Algebra");
}

#[test]
fn parses_standard_imports_separately_from_path_imports() {
    let config = parse_project_config(
            "[hierarchy]\nmodule\n\n[import std]\nbasics\nnumber_theory # standard package\n\n[import]\nAlgebra = \"../algebra\"\n\n[export]\nmain = \"./main.lit\"\n",
            "litex.config",
        )
        .expect("parse standard and path imports");
    assert_eq!(config.std_imports.len(), 2);
    assert_eq!(config.std_imports[0].name, "basics");
    assert_eq!(config.std_imports[0].line, 5);
    assert_eq!(config.std_imports[1].name, "number_theory");
    assert_eq!(config.std_imports[1].line, 6);
    assert_eq!(config.imports.len(), 1);
    assert_eq!(config.imports[0].name, "Algebra");
}

#[test]
fn removed_allow_bare_tables_are_rejected() {
    for table in [
        "[allow bare export]",
        "[allow bare import std]",
        "[allow bare import]",
    ] {
        let source =
            format!("[hierarchy]\nmodule\n\n[export]\nmain = \"./main.lit\"\n\n{table}\nA\n");
        let Err(error) = parse_project_config(&source, "litex.config") else {
            panic!("removed configuration table must be rejected: {table}");
        };
        let output = format!("{error:?}");
        assert!(output.contains("only supports"), "{output}");
        assert!(!output.contains(table), "{output}");
    }
}

#[test]
fn module_alias_namespace_includes_standard_imports_and_exports() {
    let result = parse_project_config(
        "[hierarchy]\nmodule\n\n[import std]\nbasics\n\n[export]\nbasics = \"./basics\"\n",
        "litex.config",
    );
    let Err(error) = result else {
        panic!("standard import and export aliases must not collide");
    };
    assert!(format!("{error:?}").contains("both a standard import and an export"));
}

#[test]
fn standard_imports_require_one_unique_package_name_per_line() {
    for (source, expected) in [
            (
                "[hierarchy]\nmodule\n\n[import std]\nbasics = \"./basics\"\n\n[export]\nmain = \"./main.lit\"\n",
                "expects exactly one standard package name",
            ),
            (
                "[hierarchy]\nmodule\n\n[import std]\nbasics number_theory\n\n[export]\nmain = \"./main.lit\"\n",
                "expects exactly one standard package name",
            ),
            (
                "[hierarchy]\nmodule\n\n[import std]\n1basics\n\n[export]\nmain = \"./main.lit\"\n",
                "name first character cannot be a number or symbol",
            ),
            (
                "[hierarchy]\nmodule\n\n[import std]\nbasics\nbasics\n\n[export]\nmain = \"./main.lit\"\n",
                "duplicate standard import name `basics`",
            ),
        ] {
            let Err(error) = parse_project_config(source, "litex.config") else {
                panic!("invalid standard imports must be rejected");
            };
            assert!(format!("{error:?}").contains(expected), "{error:?}");
        }
}

#[test]
fn standard_package_names_cannot_collide_with_path_imports() {
    let result = parse_project_config(
            "[hierarchy]\nmodule\n\n[import]\nbasics = \"../local-basics\"\n\n[import std]\nbasics\n\n[export]\nmain = \"./main.lit\"\n",
            "litex.config",
        );
    let Err(error) = result else {
        panic!("standard package and path import names must not collide");
    };
    assert!(format!("{error:?}").contains("conflicts with an [import std] package name"));
}

#[test]
fn parses_submodule_hierarchy() {
    let config = parse_project_config(
        "[hierarchy]\nsubmodule\n\n[export]\nimplementation = \"./implementation.lit\"\n",
        "litex.config",
    )
    .expect("parse submodule configuration");
    assert_eq!(config.hierarchy, ProjectHierarchy::Submodule);
    assert_eq!(config.hierarchy_line, 2);
}

#[test]
fn hierarchy_configuration_is_strict() {
    for (source, expected) in [
            (
                "[export]\nimplementation = \"./implementation.lit\"\n",
                "must declare `module` or `submodule`",
            ),
            (
                "[hierarchy]\nmodule\nsubmodule\n\n[export]\nimplementation = \"./implementation.lit\"\n",
                "exactly one declaration",
            ),
            (
                "[hierarchy]\nroot\n\n[export]\nimplementation = \"./implementation.lit\"\n",
                "exactly `module` or `submodule`",
            ),
            (
                "[hierarchy]\nsubmodule\n\n[import]\nA = \"../A\"\n\n[export]\nimplementation = \"./implementation.lit\"\n",
                "only a [hierarchy] module may declare [import]",
            ),
        ] {
            let Err(error) = parse_project_config(source, "litex.config") else {
                panic!("invalid hierarchy configuration must be rejected");
            };
            assert!(format!("{error:?}").contains(expected), "{error:?}");
        }
}

#[test]
fn module_flatten_requires_one_module_file_export() {
    let config = parse_project_config(
        "[hierarchy]\nmodule\n\n[module]\nflatten = true\n\n[export]\nmain = \"./main.lit\"\n",
        "litex.config",
    )
    .expect("module flatten configuration");
    assert!(config.module_flatten);

    for (source, expected) in [
            (
                "[hierarchy]\nsubmodule\n\n[module]\nflatten = true\n\n[export]\nmain = \"./main.lit\"\n",
                "only available for [hierarchy] module",
            ),
            (
                "[hierarchy]\nmodule\n\n[module]\nflatten = true\n\n[export]\na = \"./a.lit\"\nb = \"./b.lit\"\n",
                "exactly one [export] entry",
            ),
            (
                "[hierarchy]\nmodule\n\n[module]\nflatten = true\n\n[export]\nchild = \"./child\"\n",
                "to be a .lit file",
            ),
        ] {
            let Err(error) = parse_project_config(source, "litex.config") else {
                panic!("invalid module flatten configuration must be rejected");
            };
            assert!(format!("{error:?}").contains(expected), "{error:?}");
        }
}

#[test]
fn submodule_cannot_import_standard_modules() {
    let result = parse_project_config(
        "[hierarchy]\nsubmodule\n\n[import std]\nbasics\n\n[export]\nmain = \"./main.lit\"\n",
        "litex.config",
    );
    let Err(error) = result else {
        panic!("submodule standard import must be rejected");
    };
    assert!(format!("{error:?}")
        .contains("only a [hierarchy] module may declare [import] or [import std]"));
}
