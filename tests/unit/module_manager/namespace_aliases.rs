use crate::module_manager::{parse_litex_config, GlobalModuleManager, LitexConfig};
use crate::prelude::*;
use std::path::Path;

fn config(source: &str) -> Result<LitexConfig, String> {
    parse_litex_config(source, Path::new("/alias-root"), Path::new("/std"))
}

#[test]
fn namespace_alias_config_accepts_order_comments_and_import_name_reuse() {
    let config = config("[alias]\nLib = Lib::defs # explicit export\nC = Lib::other\n[export]\nmain = \"main.lit\"\n[import]\nLib = \"library\"\n").unwrap();
    assert_eq!(config.aliases.len(), 2);
    assert_eq!(config.aliases[0].name, "Lib");
    assert_eq!(config.aliases[0].import_alias, "Lib");
    assert_eq!(config.aliases[1].export_name, "other");
    assert!(LitexConfig::new().aliases.is_empty());
    let std = config_std();
    assert_eq!(std.aliases[0].import_alias, "basics");
}

fn config_std() -> LitexConfig {
    config("[import std]\nbasics\n[alias]\nB = basics::main\n[export]\nmain = \"main.lit\"\n")
        .unwrap()
}

#[test]
fn namespace_alias_config_rejects_duplicates_collisions_chains_and_malformed_targets() {
    let prefix = "[import]\nLib = \"library\"\n[export]\nmain = \"main.lit\"\n[alias]\n";
    for (rows, message) in [
        (
            "C = Lib::defs\nC = Lib::other\n",
            "duplicate namespace alias",
        ),
        ("main = Lib::defs\n", "conflicts with a local export"),
        ("C = Missing::defs\n", "unknown import"),
        ("C = Lib::defs\nD = C::other\n", "alias chains"),
        ("C = C::defs\n", "unknown import"),
        ("C = Lib\n", "direct `Import::export`"),
        ("C = Lib::defs::v\n", "direct `Import::export`"),
        ("C = \"Lib::defs\"\n", "invalid name"),
        ("C = Lib:::defs\n", "invalid name"),
        ("C = Lib::\n", "empty name"),
        ("C::D = Lib::defs\n", "invalid name"),
    ] {
        let error = config(&format!("{prefix}{rows}")).unwrap_err();
        assert!(error.contains(message), "{rows}: {error}");
        assert!(error.starts_with("litex.config:"));
    }
}

#[test]
fn namespace_alias_resolution_preserves_identity_export_selection_and_package_scope() {
    let root = config(
        "[import]\nLib = \"library\"\n[alias]\nC = Lib::defs\n[export]\nlocal = \"local.lit\"\n",
    )
    .unwrap();
    let mut manager = GlobalModuleManager::new_with_root_config(root);
    let library = config("[export]\nother = \"other.lit\"\ndefs = \"defs.lit\"\n").unwrap();
    let lib = manager
        .record_import("Lib".into(), "/alias-root/library".into(), library)
        .unwrap();
    let parts = |names: &[&str]| names.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    let short = manager.elaborate_name_parts(&parts(&["C", "v"])).unwrap();
    assert_eq!(
        short,
        manager
            .elaborate_name_parts(&parts(&["Lib", "defs", "v"]))
            .unwrap()
    );
    assert_ne!(
        short,
        manager
            .elaborate_name_parts(&parts(&["Lib", "other", "v"]))
            .unwrap()
    );
    assert_eq!(
        manager.elaborate_name_parts(&parts(&["C"])).unwrap(),
        AtomicName::Plain { name: "C".into() }
    );
    manager
        .validate_alias_targets(manager.litex_config())
        .unwrap();
    // An alias in one package neither leaks into nor re-exports through another.
    manager.set_current_mod_id(Some(lib)).unwrap();
    assert!(manager.elaborate_name_parts(&parts(&["C", "v"])).is_err());
    manager.set_current_mod_id(None).unwrap();
    let nested = config(
        "[import]\nDep = \"library\"\n[alias]\nC = Dep::other\n[export]\nmain = \"main.lit\"\n",
    )
    .unwrap();
    let nested_id = manager
        .record_import("Nested".into(), "/alias-root/nested".into(), nested)
        .unwrap();
    manager.set_current_mod_id(Some(nested_id)).unwrap();
    assert_eq!(
        manager.elaborate_name_parts(&parts(&["C", "v"])).unwrap(),
        AtomicName::WithModAndExportFileId {
            global_mod_id: lib,
            export_file_id: 0,
            name: "v".into()
        }
    );
    manager
        .validate_alias_targets(manager.current_litex_config().unwrap())
        .unwrap();
}

#[test]
fn namespace_alias_validation_rejects_unused_unknown_export_and_unmounted_import() {
    let cfg = config(
        "[import]\nLib = \"library\"\n[alias]\nC = Lib::ghost\n[export]\nmain = \"main.lit\"\n",
    )
    .unwrap();
    let mut manager = GlobalModuleManager::new_with_root_config(cfg);
    assert!(manager
        .validate_alias_targets(manager.litex_config())
        .unwrap_err()
        .contains("not on the global module table"));
    manager
        .record_import(
            "Lib".into(),
            "/alias-root/library".into(),
            config("[export]\ndefs = \"defs.lit\"\n").unwrap(),
        )
        .unwrap();
    let message = manager
        .validate_alias_targets(manager.litex_config())
        .unwrap_err();
    assert!(
        message.contains("C") && message.contains("ghost"),
        "{message}"
    );
    assert!(manager
        .elaborate_flat_import("Lib", "v".into())
        .unwrap_err()
        .contains("`:::` has been removed"));
}
