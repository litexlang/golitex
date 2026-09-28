//! Import-module cache helpers used by `run_module/import_kb.rs`.
//!
//! Why this file exists
//! --------------------
//! Rebuilding an imported package with `exec_stmt` is expensive. After a cold
//! success we snapshot each export's **definitions** under
//! `__litex_knowledge_base__/`. A later import with a matching fingerprint can
//! restore that product (with id remap) and skip re-running the export `.lit`.
//!
//! Ownership split
//! ---------------
//! - `run_module/import_kb.rs`: when to try hit / cold-run / write-back, and how
//!   to install remapped exports into `GlobalModuleManager`.
//! - **This file**: fingerprint a module tree, load+remap from disk, build an
//!   `ExecEnv` from a mounted export, write the cache after cold success.
//!
//! Product: definitions-only MVP. A hit must look like a cold import for
//! `by def` / `release thm` / `by thm` / `release obj def` consumers.
//! Full design: `knowledge_base/README.md`.

use super::def_prop_codec::KbCodecError;
use super::fingerprint::{compute_fingerprint, FingerprintInputs};
use super::manifest::GlobalIdsSnapshot;
use super::mount::{
    try_mount_module, write_module_kb, ExportKbWrite, KbMountMiss, MountedExport, MountedModule,
};
use super::paths::kb_dir;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::exec_env::session_view::ExecEnvSessionView;
use crate::new_pipeline::module_manager::{
    parse_litex_config, ExportFileAndItsExecEnv, LitexConfig,
};
use crate::new_pipeline::runtime::{CodeSource, GlobalIds};
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};

// --- GlobalIds bridges (KB stores u64 watermarks; Runtime owns typed counters) ---

// Copy live Runtime counters into a KB snapshot for remapping / manifest IO.
pub fn snapshot_from_global_ids(ids: &GlobalIds) -> GlobalIdsSnapshot {
    let (fact, wd, prp, ident) = ids.to_u64s();
    GlobalIdsSnapshot::new(fact, wd, prp, ident)
}

// Rebuild Runtime counters after a successful KB hit (advance past remapped leave).
pub fn global_ids_from_snapshot(snapshot: &GlobalIdsSnapshot) -> GlobalIds {
    GlobalIds::from_u64s(
        snapshot.next_fact_id,
        snapshot.next_well_definedness_id,
        snapshot.next_prop_rewrite_property_id,
        snapshot.next_identifier_id,
    )
}

// Stable string key for mod_id ↔ path tables (canonicalize when possible).
pub fn path_key(path: &Path) -> String {
    match path.canonicalize() {
        Ok(canonical) => canonical.to_string_lossy().to_string(),
        Err(_) => path.to_string_lossy().to_string(),
    }
}

// --- Fingerprint (cache validity; content-addressed, not mtime) ---

// Fingerprint this module and every transitive import (deps first, then self).
// Used both to decide hit/miss and as the value stored in manifest.json.
pub fn fingerprint_module_recursive(
    module_dir: &Path,
    config: &LitexConfig,
    std_root: &Path,
) -> Result<String, KbCodecError> {
    let mut dep_fps = Vec::new();
    for import in &config.imports {
        let dep_config = read_module_config(&import.path, std_root)?;
        dep_fps.push(fingerprint_module_recursive(
            &import.path,
            &dep_config,
            std_root,
        )?);
    }
    dep_fps.sort();
    fingerprint_self(module_dir, config, &dep_fps)
}

// Hash litex.config + ordered export file bytes + already-computed dep fingerprints.
fn fingerprint_self(
    module_dir: &Path,
    config: &LitexConfig,
    dep_fingerprints: &[String],
) -> Result<String, KbCodecError> {
    let config_path = module_dir.join("litex.config");
    let litex_config_bytes = fs::read(&config_path).map_err(|error| KbCodecError::Io {
        path: config_path,
        message: error.to_string(),
    })?;
    let mut export_files = Vec::new();
    for export in &config.exports {
        let rel = match export.path.strip_prefix(module_dir) {
            Ok(rel) => rel.to_string_lossy().to_string(),
            Err(_) => export
                .path
                .file_name()
                .map(|n| n.to_string_lossy().to_string())
                .unwrap_or_else(|| export.name.clone()),
        };
        let bytes = fs::read(&export.path).map_err(|error| KbCodecError::Io {
            path: export.path.clone(),
            message: error.to_string(),
        })?;
        export_files.push((rel, bytes));
    }
    Ok(compute_fingerprint(&FingerprintInputs {
        litex_config_bytes: &litex_config_bytes,
        export_files: &export_files,
        dep_fingerprints,
    }))
}

fn read_module_config(module_dir: &Path, std_root: &Path) -> Result<LitexConfig, KbCodecError> {
    let path = module_dir.join("litex.config");
    let source = fs::read_to_string(&path).map_err(|error| KbCodecError::Io {
        path: path.clone(),
        message: error.to_string(),
    })?;
    parse_litex_config(&source, module_dir, std_root).map_err(KbCodecError::Shape)
}

// --- Hit path ---

// Load `__litex_knowledge_base__/` for an already-mounted module.
// On success: definitions are remapped (GlobalIds deltas + global_mod_id path table)
// so they look like a cold build in *this* session. On miss/corrupt: KbMountMiss
// and the caller cold-runs exports instead.
pub fn try_hit_import_cache(
    module_dir: &Path,
    fingerprint: &str,
    now: &GlobalIds,
    path_to_mod_id: &HashMap<PathBuf, usize>,
) -> Result<MountedModule, KbMountMiss> {
    let mut path_to_new = HashMap::new();
    for (path, mod_id) in path_to_mod_id {
        path_to_new.insert(path_key(path), *mod_id as u64);
    }
    try_mount_module(
        module_dir,
        fingerprint,
        &snapshot_from_global_ids(now),
        &path_to_new,
    )
}

// Turn one remapped export into a finished-export ExecEnv ready for
// `record_imported_export`. Facts/WD stay empty (definitions-only MVP);
// session_view carries remapped enter/leave watermarks.
pub fn exec_env_from_mounted_export(export: &MountedExport, global_mod_id: usize) -> ExecEnv {
    let mut view = ExecEnvSessionView::new(
        global_ids_from_snapshot(&export.global_ids_at_enter),
        CodeSource::ImportedExport {
            global_mod_id,
            export_file_id: export.export_file_id,
        },
    );
    view.stamp_leave(global_ids_from_snapshot(&export.global_ids_at_leave));
    let mut env = ExecEnv::new(Some(view));
    env.definitions = export.definitions.clone();
    env
}

// --- Miss / cold write-back ---

// After a successful cold import, persist definitions under
// `__litex_knowledge_base__/`. Best-effort: if some def shapes are not yet
// encodable, clear/skip the cache and return Ok so import itself still succeeds.
pub fn write_import_cache_after_cold(
    module_dir: &Path,
    fingerprint: &str,
    self_mod_id: usize,
    path_to_mod_id: &HashMap<PathBuf, usize>,
    recorded_exports: &[ExportFileAndItsExecEnv],
) -> Result<(), KbCodecError> {
    let mut mod_id_to_path = BTreeMap::new();
    for (path, mod_id) in path_to_mod_id {
        mod_id_to_path.insert(*mod_id as u64, path_key(path));
    }

    let mut exports = Vec::new();
    for (export_file_id, recorded) in recorded_exports.iter().enumerate() {
        let (enter, leave) = match &recorded.exec_env.session_view {
            Some(view) => {
                let enter = snapshot_from_global_ids(&view.global_ids_at_enter);
                let leave = match &view.global_ids_at_leave {
                    Some(leave) => snapshot_from_global_ids(leave),
                    None => enter.clone(),
                };
                (enter, leave)
            }
            None => {
                return Err(KbCodecError::Shape(
                    "cold export missing session_view; cannot write kb".into(),
                ));
            }
        };
        let relative_path = match recorded.path.strip_prefix(module_dir) {
            Ok(rel) => rel.to_string_lossy().to_string(),
            Err(_) => recorded
                .path
                .file_name()
                .map(|n| n.to_string_lossy().to_string())
                .unwrap_or_else(|| recorded.name.clone()),
        };
        exports.push(ExportKbWrite {
            export_file_id,
            name: recorded.name.clone(),
            relative_path,
            definitions: recorded.exec_env.definitions.clone(),
            global_ids_at_enter: enter,
            global_ids_at_leave: leave,
        });
    }

    match write_module_kb(
        module_dir,
        fingerprint,
        self_mod_id as u64,
        &mod_id_to_path,
        &exports,
    ) {
        Ok(()) => Ok(()),
        Err(KbCodecError::Unsupported(_)) => {
            // Cannot encode this module's defs yet — drop stale cache if any.
            let dir = kb_dir(module_dir);
            if dir.exists() {
                let _ = fs::remove_dir_all(&dir);
            }
            Ok(())
        }
        Err(error) => Err(error),
    }
}

// Guard: refuse a hit whose export count does not match litex.config [export].
pub fn mounted_matches_config(mounted: &MountedModule, config: &LitexConfig) -> bool {
    mounted.exports.len() == config.exports.len()
}
