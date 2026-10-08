//! Write / try-mount imported-module knowledge_base artifacts (definitions MVP).
//!
//! Does not touch Runtime or ExecEnv ownership. Caller supplies watermarks and
//! later inserts remapped `DefinitionMemory` into the live module manager.

use super::def_prop_codec::KbCodecError;
use super::definitions_memory_codec::{read_definition_memory, write_definition_memory};
use super::json_mini::JsonValue;
use super::manifest::{
    decode_manifest, encode_manifest, GlobalIdsDeltas, GlobalIdsSnapshot, KbManifest,
    ManifestExportEntry,
};
use super::paths::{export_definitions_path, kb_dir, manifest_path, KB_ABI, KB_DIR_NAME};
use super::remap::{remap_definition_memory, RemapPlan};
use crate::exec_env::exec_env::DefinitionMemory;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
pub enum KbMountMiss {
    MissingDir {
        path: PathBuf,
    },
    MissingManifest {
        path: PathBuf,
    },
    FingerprintMismatch {
        expected: String,
        found: String,
    },
    AbiMismatch {
        file_abi: String,
    },
    Corrupt(KbCodecError),
    ExportCountMismatch {
        manifest: usize,
        on_disk_hint: String,
    },
}

impl std::fmt::Display for KbMountMiss {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KbMountMiss::MissingDir { path } => {
                write!(f, "kb missing dir {}", path.display())
            }
            KbMountMiss::MissingManifest { path } => {
                write!(f, "kb missing manifest {}", path.display())
            }
            KbMountMiss::FingerprintMismatch { expected, found } => {
                write!(
                    f,
                    "kb fingerprint mismatch expected={expected} found={found}"
                )
            }
            KbMountMiss::AbiMismatch { file_abi } => {
                write!(f, "kb abi mismatch file={file_abi} code={KB_ABI}")
            }
            KbMountMiss::Corrupt(err) => write!(f, "kb corrupt: {err}"),
            KbMountMiss::ExportCountMismatch {
                manifest,
                on_disk_hint,
            } => write!(
                f,
                "kb export layout mismatch manifest_count={manifest} ({on_disk_hint})"
            ),
        }
    }
}

/// One export after a successful mount (definitions remapped into this session).
#[derive(Clone)]
pub struct MountedExport {
    pub export_file_id: usize,
    pub name: String,
    pub relative_path: String,
    pub definitions: DefinitionMemory,
    pub global_ids_at_enter: GlobalIdsSnapshot,
    pub global_ids_at_leave: GlobalIdsSnapshot,
}

/// Successful mount product for one imported module.
#[derive(Clone)]
pub struct MountedModule {
    pub fingerprint: String,
    pub self_mod_id_old: u64,
    pub exports: Vec<MountedExport>,
    /// Remapped leave watermark of the last export (caller may advance live counters past this).
    pub remapped_global_ids_leave: GlobalIdsSnapshot,
}

/// One export to persist after a successful cold build.
pub struct ExportKbWrite {
    pub export_file_id: usize,
    pub name: String,
    pub relative_path: String,
    pub definitions: DefinitionMemory,
    pub global_ids_at_enter: GlobalIdsSnapshot,
    pub global_ids_at_leave: GlobalIdsSnapshot,
}

/// Write `__litex_knowledge_base__/` for module_root (create or overwrite).
pub fn write_module_kb(
    module_root: &Path,
    fingerprint: &str,
    self_mod_id: u64,
    mod_id_to_path: &BTreeMap<u64, String>,
    exports: &[ExportKbWrite],
) -> Result<(), KbCodecError> {
    let dir = kb_dir(module_root);
    if dir.exists() {
        fs::remove_dir_all(&dir).map_err(|error| KbCodecError::Io {
            path: dir.clone(),
            message: error.to_string(),
        })?;
    }
    fs::create_dir_all(&dir).map_err(|error| KbCodecError::Io {
        path: dir.clone(),
        message: error.to_string(),
    })?;

    let mut manifest_exports = Vec::new();
    for export in exports {
        let path = export_definitions_path(module_root, export.export_file_id);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|error| KbCodecError::Io {
                path: parent.to_path_buf(),
                message: error.to_string(),
            })?;
        }
        write_definition_memory(&path, &export.definitions)?;
        manifest_exports.push(ManifestExportEntry {
            export_file_id: export.export_file_id,
            name: export.name.clone(),
            relative_path: export.relative_path.clone(),
            global_ids_at_enter: export.global_ids_at_enter.clone(),
            global_ids_at_leave: export.global_ids_at_leave.clone(),
        });
    }

    let manifest = KbManifest::new(
        fingerprint.to_string(),
        self_mod_id,
        mod_id_to_path.clone(),
        manifest_exports,
    );
    let mut body = encode_manifest(&manifest)?.stringify_pretty();
    if !body.ends_with('\n') {
        body.push('\n');
    }
    let mpath = manifest_path(module_root);
    fs::write(&mpath, body).map_err(|error| KbCodecError::Io {
        path: mpath,
        message: error.to_string(),
    })?;
    Ok(())
}

/// Try to load + remap a module KB. Miss → rebuild outside this package.
///
/// `now` is the caller's current GlobalIds watermark (KB-owned snapshot).
/// `path_to_new_mod_id` maps module path strings (as stored in the manifest)
/// to this session's `global_mod_id`.
pub fn try_mount_module(
    module_root: &Path,
    expected_fingerprint: &str,
    now: &GlobalIdsSnapshot,
    path_to_new_mod_id: &HashMap<String, u64>,
) -> Result<MountedModule, KbMountMiss> {
    let dir = kb_dir(module_root);
    if !dir.is_dir() {
        return Err(KbMountMiss::MissingDir { path: dir });
    }
    let mpath = manifest_path(module_root);
    if !mpath.is_file() {
        return Err(KbMountMiss::MissingManifest { path: mpath });
    }
    let text = fs::read_to_string(&mpath).map_err(|error| {
        KbMountMiss::Corrupt(KbCodecError::Io {
            path: mpath.clone(),
            message: error.to_string(),
        })
    })?;
    let manifest = decode_manifest(
        &JsonValue::parse(&text).map_err(|e| KbMountMiss::Corrupt(KbCodecError::Json(e.0)))?,
    )
    .map_err(KbMountMiss::Corrupt)?;

    if manifest.abi != KB_ABI {
        return Err(KbMountMiss::AbiMismatch {
            file_abi: manifest.abi,
        });
    }
    if manifest.fingerprint != expected_fingerprint {
        return Err(KbMountMiss::FingerprintMismatch {
            expected: expected_fingerprint.to_string(),
            found: manifest.fingerprint,
        });
    }

    let old_mod_id_to_new = build_old_mod_id_to_new(&manifest.mod_id_to_path, path_to_new_mod_id)
        .map_err(KbMountMiss::Corrupt)?;

    let mut mounted_exports = Vec::new();
    // Advance like cold build: each export remaps against the live cursor, then
    // cursor becomes that export's remapped leave.
    let mut cursor = now.clone();
    let mut remapped_leave = now.clone();

    for entry in &manifest.exports {
        let def_path = export_definitions_path(module_root, entry.export_file_id);
        let mut definitions = read_definition_memory(&def_path).map_err(KbMountMiss::Corrupt)?;

        let deltas = GlobalIdsDeltas::from_enter_and_now(&entry.global_ids_at_enter, &cursor);
        let plan = RemapPlan::new(deltas, old_mod_id_to_new.clone());
        remap_definition_memory(&mut definitions, &plan).map_err(KbMountMiss::Corrupt)?;

        let remapped_enter = entry.global_ids_at_enter.apply_deltas(&plan.deltas);
        let remapped_leave_export = entry.global_ids_at_leave.apply_deltas(&plan.deltas);
        cursor = remapped_leave_export.clone();
        remapped_leave = remapped_leave_export.clone();

        mounted_exports.push(MountedExport {
            export_file_id: entry.export_file_id,
            name: entry.name.clone(),
            relative_path: entry.relative_path.clone(),
            definitions,
            global_ids_at_enter: remapped_enter,
            global_ids_at_leave: remapped_leave_export,
        });
    }

    if mounted_exports.is_empty() && !manifest.exports.is_empty() {
        return Err(KbMountMiss::ExportCountMismatch {
            manifest: manifest.exports.len(),
            on_disk_hint: format!("under {}", KB_DIR_NAME),
        });
    }

    Ok(MountedModule {
        fingerprint: expected_fingerprint.to_string(),
        self_mod_id_old: manifest.self_mod_id,
        exports: mounted_exports,
        remapped_global_ids_leave: remapped_leave,
    })
}

fn build_old_mod_id_to_new(
    old_mod_id_to_path: &BTreeMap<u64, String>,
    path_to_new_mod_id: &HashMap<String, u64>,
) -> Result<HashMap<u64, u64>, KbCodecError> {
    let mut out = HashMap::new();
    for (old_id, path) in old_mod_id_to_path {
        let Some(new_id) = path_to_new_mod_id.get(path) else {
            return Err(KbCodecError::Shape(format!(
                "mount remap: no new mod_id for path `{path}`"
            )));
        };
        out.insert(*old_id, *new_id);
    }
    Ok(out)
}
