//! KB-owned GlobalIds watermark snapshot (u64s; does not read Runtime privates).

use super::def_prop_codec::KbCodecError;
use super::json_mini::JsonValue;
use super::paths::KB_ABI;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalIdsSnapshot {
    pub next_fact_id: u64,
    pub next_well_definedness_id: u64,
    pub next_prop_rewrite_property_id: u64,
    pub next_identifier_id: u64,
}

impl GlobalIdsSnapshot {
    pub fn new(
        next_fact_id: u64,
        next_well_definedness_id: u64,
        next_prop_rewrite_property_id: u64,
        next_identifier_id: u64,
    ) -> Self {
        Self {
            next_fact_id,
            next_well_definedness_id,
            next_prop_rewrite_property_id,
            next_identifier_id,
        }
    }

    pub fn apply_deltas(&self, deltas: &GlobalIdsDeltas) -> Self {
        Self {
            next_fact_id: self.next_fact_id + deltas.fact_delta,
            next_well_definedness_id: self.next_well_definedness_id + deltas.wd_delta,
            next_prop_rewrite_property_id: self.next_prop_rewrite_property_id
                + deltas.prop_rewrite_delta,
            next_identifier_id: self.next_identifier_id + deltas.identifier_delta,
        }
    }
}

/// Per-counter deltas: `runtime.now - cached_enter` for each kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlobalIdsDeltas {
    pub fact_delta: u64,
    pub wd_delta: u64,
    pub prop_rewrite_delta: u64,
    pub identifier_delta: u64,
}

impl GlobalIdsDeltas {
    pub fn from_enter_and_now(enter: &GlobalIdsSnapshot, now: &GlobalIdsSnapshot) -> Self {
        Self {
            fact_delta: now.next_fact_id.saturating_sub(enter.next_fact_id),
            wd_delta: now
                .next_well_definedness_id
                .saturating_sub(enter.next_well_definedness_id),
            prop_rewrite_delta: now
                .next_prop_rewrite_property_id
                .saturating_sub(enter.next_prop_rewrite_property_id),
            identifier_delta: now
                .next_identifier_id
                .saturating_sub(enter.next_identifier_id),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ManifestExportEntry {
    pub export_file_id: usize,
    pub name: String,
    pub relative_path: String,
    pub global_ids_at_enter: GlobalIdsSnapshot,
    pub global_ids_at_leave: GlobalIdsSnapshot,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KbManifest {
    pub abi: String,
    pub fingerprint: String,
    pub self_mod_id: u64,
    /// Old `global_mod_id` → module path string (stable key for remap table).
    pub mod_id_to_path: BTreeMap<u64, String>,
    pub exports: Vec<ManifestExportEntry>,
}

impl KbManifest {
    pub fn new(
        fingerprint: String,
        self_mod_id: u64,
        mod_id_to_path: BTreeMap<u64, String>,
        exports: Vec<ManifestExportEntry>,
    ) -> Self {
        Self {
            abi: KB_ABI.to_string(),
            fingerprint,
            self_mod_id,
            mod_id_to_path,
            exports,
        }
    }
}

pub fn encode_manifest(manifest: &KbManifest) -> Result<JsonValue, KbCodecError> {
    let mod_map = manifest
        .mod_id_to_path
        .iter()
        .map(|(id, path)| {
            JsonValue::Array(vec![
                JsonValue::Number(*id as f64),
                JsonValue::String(path.clone()),
            ])
        })
        .collect::<Vec<_>>();
    let exports = manifest
        .exports
        .iter()
        .map(encode_manifest_export)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("litex_kb_manifest".into())),
        ("abi".into(), JsonValue::String(manifest.abi.clone())),
        (
            "fingerprint".into(),
            JsonValue::String(manifest.fingerprint.clone()),
        ),
        (
            "self_mod_id".into(),
            JsonValue::Number(manifest.self_mod_id as f64),
        ),
        ("mod_id_to_path".into(), JsonValue::Array(mod_map)),
        ("exports".into(), JsonValue::Array(exports)),
    ]))
}

pub fn decode_manifest(value: &JsonValue) -> Result<KbManifest, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "litex_kb_manifest" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `litex_kb_manifest`, got `{kind}`"
        )));
    }
    let abi = JsonValue::get(map, "abi")?.as_str()?.to_string();
    if abi != KB_ABI {
        return Err(KbCodecError::Shape(format!(
            "kb abi mismatch: file `{abi}`, code `{KB_ABI}`"
        )));
    }
    let mut mod_id_to_path = BTreeMap::new();
    for entry in JsonValue::get(map, "mod_id_to_path")?.as_array()? {
        let pair = entry.as_array()?;
        if pair.len() != 2 {
            return Err(KbCodecError::Shape(
                "mod_id_to_path entry must be [id, path]".into(),
            ));
        }
        mod_id_to_path.insert(pair[0].as_u64()?, pair[1].as_str()?.to_string());
    }
    let exports = JsonValue::get(map, "exports")?
        .as_array()?
        .iter()
        .map(decode_manifest_export)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(KbManifest {
        abi,
        fingerprint: JsonValue::get(map, "fingerprint")?.as_str()?.to_string(),
        self_mod_id: JsonValue::get(map, "self_mod_id")?.as_u64()?,
        mod_id_to_path,
        exports,
    })
}

fn encode_manifest_export(entry: &ManifestExportEntry) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        (
            "export_file_id".into(),
            JsonValue::Number(entry.export_file_id as f64),
        ),
        ("name".into(), JsonValue::String(entry.name.clone())),
        (
            "relative_path".into(),
            JsonValue::String(entry.relative_path.clone()),
        ),
        (
            "global_ids_at_enter".into(),
            encode_ids_snapshot(&entry.global_ids_at_enter),
        ),
        (
            "global_ids_at_leave".into(),
            encode_ids_snapshot(&entry.global_ids_at_leave),
        ),
    ]))
}

fn decode_manifest_export(value: &JsonValue) -> Result<ManifestExportEntry, KbCodecError> {
    let map = value.as_object()?;
    Ok(ManifestExportEntry {
        export_file_id: JsonValue::get(map, "export_file_id")?.as_u64()? as usize,
        name: JsonValue::get(map, "name")?.as_str()?.to_string(),
        relative_path: JsonValue::get(map, "relative_path")?.as_str()?.to_string(),
        global_ids_at_enter: decode_ids_snapshot(JsonValue::get(map, "global_ids_at_enter")?)?,
        global_ids_at_leave: decode_ids_snapshot(JsonValue::get(map, "global_ids_at_leave")?)?,
    })
}

fn encode_ids_snapshot(ids: &GlobalIdsSnapshot) -> JsonValue {
    JsonValue::object_from(vec![
        (
            "next_fact_id".into(),
            JsonValue::Number(ids.next_fact_id as f64),
        ),
        (
            "next_well_definedness_id".into(),
            JsonValue::Number(ids.next_well_definedness_id as f64),
        ),
        (
            "next_prop_rewrite_property_id".into(),
            JsonValue::Number(ids.next_prop_rewrite_property_id as f64),
        ),
        (
            "next_identifier_id".into(),
            JsonValue::Number(ids.next_identifier_id as f64),
        ),
    ])
}

fn decode_ids_snapshot(value: &JsonValue) -> Result<GlobalIdsSnapshot, KbCodecError> {
    let map = value.as_object()?;
    Ok(GlobalIdsSnapshot {
        next_fact_id: JsonValue::get(map, "next_fact_id")?.as_u64()?,
        next_well_definedness_id: JsonValue::get(map, "next_well_definedness_id")?.as_u64()?,
        next_prop_rewrite_property_id: JsonValue::get(map, "next_prop_rewrite_property_id")?
            .as_u64()?,
        next_identifier_id: JsonValue::get(map, "next_identifier_id")?.as_u64()?,
    })
}
