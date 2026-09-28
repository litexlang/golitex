//! Import-module KB hit and cold write-back (always on).
//!
//! Why this file exists
//! --------------------
//! Keep `__litex_knowledge_base__` load/write **out of** the main
//! `run_import_module` control flow. That file stays: recurse deps → mount →
//! run exports. This file is the only place that decides hit vs miss and
//! records remapped exports or writes the cache after cold success.
//!
//! Heavy lifting (fingerprint, disk codecs, id remap) lives in
//! `knowledge_base/import_cache.rs`.

use crate::knowledge_base::{
    exec_env_from_mounted_export, fingerprint_module_recursive, global_ids_from_snapshot,
    mounted_matches_config, try_hit_import_cache, write_import_cache_after_cold,
};
use crate::module_manager::{
    ExportFileAndItsExecEnv, LitexConfig, LitexConfigExport,
};
use crate::run::run_command_outcome::RunSessionError;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use std::path::Path;

// Outcome of trying to finish one imported module from on-disk KB.
pub enum ImportKbHit {
    // Remapped exports recorded; caller must skip cold export exec.
    Applied,
    // Miss / fingerprint fail / shape mismatch — caller cold-runs exports.
    Miss,
    // Hit matched disk but failed while installing into the module manager.
    SessionError(RunSessionError),
}

// After deps + mount_module: try load `__litex_knowledge_base__/`.
// On Applied: finished exports are already recorded and global_ids advanced.
pub fn try_finish_import_from_kb(
    runtime: &mut Runtime,
    module_dir: &Path,
    config: &LitexConfig,
    std_root: &Path,
    mod_id: usize,
    exports: &[LitexConfigExport],
) -> RuntimeResult<ImportKbHit> {
    let fingerprint = match fingerprint_module_recursive(module_dir, config, std_root) {
        Ok(fingerprint) => fingerprint,
        Err(_) => return Ok(ImportKbHit::Miss),
    };
    let mounted = match try_hit_import_cache(
        module_dir,
        &fingerprint,
        &runtime.global_ids,
        runtime.global_module_manager.path_to_mod_id(),
    ) {
        Ok(mounted) => mounted,
        Err(_) => return Ok(ImportKbHit::Miss),
    };
    if !mounted_matches_config(&mounted, config) {
        return Ok(ImportKbHit::Miss);
    }

    let mut recorded = Vec::new();
    for export in &mounted.exports {
        let path = exports
            .get(export.export_file_id)
            .map(|row| row.path.clone())
            .unwrap_or_else(|| module_dir.join(&export.relative_path));
        let env = exec_env_from_mounted_export(export, mod_id);
        recorded.push(ExportFileAndItsExecEnv::new(
            export.name.clone(),
            path,
            Box::new(env),
        ));
    }
    for item in recorded {
        if let Err(message) = runtime
            .global_module_manager
            .record_imported_export(mod_id, item)
        {
            return Ok(ImportKbHit::SessionError(RunSessionError::Runtime(
                RuntimeError::InternalBug(format!("kb hit record_imported_export: {message}")),
            )));
        }
    }
    runtime.global_ids = global_ids_from_snapshot(&mounted.remapped_global_ids_leave);
    Ok(ImportKbHit::Applied)
}

// After successful cold export run: best-effort write `__litex_knowledge_base__/`.
// Failures here must not fail the import (next run simply cold-builds again).
pub fn write_kb_after_cold_import(
    runtime: &Runtime,
    module_dir: &Path,
    config: &LitexConfig,
    std_root: &Path,
    mod_id: usize,
) {
    let Ok(fingerprint) = fingerprint_module_recursive(module_dir, config, std_root) else {
        return;
    };
    let recorded = &runtime.global_module_manager.imports()[mod_id].export_files_and_their_env;
    let _ = write_import_cache_after_cold(
        module_dir,
        &fingerprint,
        mod_id,
        runtime.global_module_manager.path_to_mod_id(),
        recorded,
    );
}
