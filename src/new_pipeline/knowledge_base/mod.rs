//! Persist and restore imported-module products (fingerprint, serialize, load).
//!
//! On-disk artifacts live under each module's `__litex_knowledge_base__/`.
//! See `README.md` in this package.

mod axiom_codec;
mod def_abstract_prop_codec;
mod def_prop_codec;
mod def_struct_codec;
mod def_thm_codec;
mod definitions_memory_codec;
mod fingerprint;
mod import_cache;
mod json_mini;
pub use json_mini::{JsonError, JsonValue};
mod manifest;
mod mount;
mod paths;
mod remap;
mod stored_identifier_codec;

pub use axiom_codec::{load_axiom, read_axiom, store_axiom, write_axiom};
pub use def_abstract_prop_codec::{
    load_def_abstract_prop, read_def_abstract_prop, store_def_abstract_prop,
    write_def_abstract_prop,
};
pub use def_prop_codec::{
    load_def_prop, read_def_prop, store_def_prop, write_def_prop, KbCodecError,
};
pub use def_struct_codec::{
    load_def_struct, read_def_struct, store_def_struct, write_def_struct,
};
pub use def_thm_codec::{load_def_thm, read_def_thm, store_def_thm, write_def_thm};
pub use definitions_memory_codec::{
    load_definition_memory, read_definition_memory, store_definition_memory,
    write_definition_memory,
};
pub use fingerprint::{compute_fingerprint, FingerprintInputs};
pub use import_cache::{
    exec_env_from_mounted_export, fingerprint_module_recursive, global_ids_from_snapshot,
    mounted_matches_config, path_key, snapshot_from_global_ids, try_hit_import_cache,
    write_import_cache_after_cold,
};
pub use manifest::{
    GlobalIdsDeltas, GlobalIdsSnapshot, KbManifest, ManifestExportEntry,
};
pub use mount::{
    try_mount_module, write_module_kb, ExportKbWrite, KbMountMiss, MountedExport, MountedModule,
};
pub use paths::{
    export_definitions_path, kb_dir, manifest_path, KB_ABI, KB_DIR_NAME,
};
pub use remap::{remap_definition_memory, RemapPlan};
pub use stored_identifier_codec::{
    load_stored_identifier, read_stored_identifier, store_stored_identifier,
    write_stored_identifier,
};

#[cfg(test)]
#[path = "../../../tests/unit/new_pipeline/knowledge_base/mod.rs"]
mod unit_tests;
