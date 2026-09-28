use crate::new_pipeline::module_manager::parse_litex_config;
use std::path::{Path, PathBuf};

#[test]
fn parses_import_std_and_export() {
    let source = r#"
[import]
Algebra = "../Algebra"

[import std]
basics
myB = basics

[export]
chap1 = "./chapter01.lit"
"#;
    let cfg = parse_litex_config(source, Path::new("/proj/root"), Path::new("/std")).unwrap();
    assert_eq!(cfg.imports.len(), 3);
    assert_eq!(cfg.imports[0].alias, "Algebra");
    assert_eq!(cfg.imports[1].alias, "basics");
    assert_eq!(cfg.imports[1].path, PathBuf::from("/std/basics"));
    assert_eq!(cfg.imports[2].alias, "myB");
    assert_eq!(cfg.imports[2].path, PathBuf::from("/std/basics"));
    assert_eq!(cfg.exports.len(), 1);
    assert_eq!(cfg.exports[0].name, "chap1");
}

#[test]
fn rejects_hierarchy() {
    let result = parse_litex_config(
        "[hierarchy]\nmodule\n[export]\na = \"./a.lit\"\n",
        Path::new("/proj"),
        Path::new("/std"),
    );
    assert!(result.is_err());
    assert!(result.err().unwrap().contains("hierarchy"));
}

#[test]
fn allows_export_alias_same_as_import() {
    let source = r#"
[import]
chap1 = "../Other"

[export]
chap1 = "./chapter01.lit"
"#;
    parse_litex_config(source, Path::new("/proj"), Path::new("/std")).unwrap();
}
