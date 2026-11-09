//! Persist registered predicate laws alongside an export's definitions.
use super::def_prop_codec::{decode_identifier_obj, encode_identifier_obj, KbCodecError};
use super::json_mini::JsonValue;
use super::remap::RemapPlan;
use crate::ast::names::AtomicName;
use crate::ast::obj::IdentifierObj;
use crate::exec_env::exec_env::PropRewriteProperty;
use crate::runtime::IdentifierId;
use std::collections::HashMap;

pub(super) fn encode(
    properties: &HashMap<AtomicName, Vec<PropRewriteProperty>>,
) -> Result<String, KbCodecError> {
    let mut entries: Vec<_> = properties.iter().collect();
    entries.sort_by_key(|(name, _)| name.to_string());
    let mut rows = Vec::new();
    for (name, laws) in entries {
        let identifier = match name {
            AtomicName::Plain { name } => IdentifierObj::plain(IdentifierId::new(0), name.clone()),
            AtomicName::WithExportFileId {
                export_file_id,
                name,
            } => IdentifierObj::with_export_file_id(*export_file_id, name.clone()),
            AtomicName::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => IdentifierObj::with_mod_and_export_file_id(
                *global_mod_id,
                *export_file_id,
                name.clone(),
            ),
        };
        let laws = laws
            .iter()
            .map(|law| match law {
                PropRewriteProperty::Reflexive => JsonValue::String("reflexive".into()),
                PropRewriteProperty::Transitive => JsonValue::String("transitive".into()),
                PropRewriteProperty::SymmetricArgumentPermutate(permutations) => JsonValue::Array(
                    permutations
                        .iter()
                        .map(|p| {
                            JsonValue::Array(
                                p.iter().map(|n| JsonValue::Number(*n as f64)).collect(),
                            )
                        })
                        .collect(),
                ),
            })
            .collect();
        rows.push(JsonValue::object_from(vec![
            ("name".into(), encode_identifier_obj(&identifier)?),
            ("laws".into(), JsonValue::Array(laws)),
        ]));
    }
    Ok(JsonValue::Array(rows).stringify_pretty())
}

pub(super) fn decode(
    text: &str,
    plan: &RemapPlan,
) -> Result<HashMap<AtomicName, Vec<PropRewriteProperty>>, KbCodecError> {
    let value = JsonValue::parse(text)?;
    let mut result = HashMap::new();
    for row in value.as_array()? {
        let row = row.as_object()?;
        let identifier = decode_identifier_obj(JsonValue::get(row, "name")?)?;
        let name = match identifier {
            IdentifierObj::Plain { name, .. } => AtomicName::Plain { name },
            IdentifierObj::WithExportFileId {
                export_file_id,
                name,
            } => AtomicName::WithExportFileId {
                export_file_id,
                name,
            },
            IdentifierObj::WithModAndExportFileId {
                global_mod_id,
                export_file_id,
                name,
            } => {
                let mapped = plan
                    .old_mod_id_to_new
                    .get(&(global_mod_id as u64))
                    .ok_or_else(|| KbCodecError::Shape("unmapped predicate module".into()))?;
                AtomicName::WithModAndExportFileId {
                    global_mod_id: *mapped as usize,
                    export_file_id,
                    name,
                }
            }
        };
        let mut laws = Vec::new();
        for law in JsonValue::get(row, "laws")?.as_array()? {
            laws.push(match law {
                JsonValue::String(name) if name == "reflexive" => PropRewriteProperty::Reflexive,
                JsonValue::String(name) if name == "transitive" => PropRewriteProperty::Transitive,
                JsonValue::Array(rows) => PropRewriteProperty::SymmetricArgumentPermutate(
                    rows.iter()
                        .map(|p| {
                            p.as_array()?
                                .iter()
                                .map(|n| Ok(n.as_u64()? as usize))
                                .collect::<Result<Vec<_>, KbCodecError>>()
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                _ => return Err(KbCodecError::Shape("unknown predicate law".into())),
            });
        }
        if result.insert(name, laws).is_some() {
            return Err(KbCodecError::Shape("duplicate predicate laws".into()));
        }
    }
    Ok(result)
}
