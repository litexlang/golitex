//! Store / load one `DefAbstractPropStmt` as JSON.

use super::def_prop_codec::{
    decode_line_file, encode_line_file, KbCodecError,
};
use super::json_mini::JsonValue;
use crate::new_pipeline::ast::stmt::DefAbstractPropStmt;
use std::fs;
use std::path::Path;

/// Encode one `DefAbstractPropStmt` to pretty JSON.
pub fn store_def_abstract_prop(stmt: &DefAbstractPropStmt) -> Result<String, KbCodecError> {
    Ok(encode_def_abstract_prop(stmt)?.stringify_pretty())
}

pub fn load_def_abstract_prop(text: &str) -> Result<DefAbstractPropStmt, KbCodecError> {
    decode_def_abstract_prop(&JsonValue::parse(text)?)
}

pub fn write_def_abstract_prop(
    path: &Path,
    stmt: &DefAbstractPropStmt,
) -> Result<(), KbCodecError> {
    let mut body = store_def_abstract_prop(stmt)?;
    if !body.ends_with('\n') {
        body.push('\n');
    }
    fs::write(path, body).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

pub fn read_def_abstract_prop(path: &Path) -> Result<DefAbstractPropStmt, KbCodecError> {
    let text = fs::read_to_string(path).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })?;
    load_def_abstract_prop(&text)
}

fn encode_def_abstract_prop(stmt: &DefAbstractPropStmt) -> Result<JsonValue, KbCodecError> {
    let params = stmt
        .params
        .iter()
        .map(|p| JsonValue::String(p.clone()))
        .collect();
    Ok(JsonValue::object_from(vec![
        (
            "kind".into(),
            JsonValue::String("def_abstract_prop".into()),
        ),
        ("name".into(), JsonValue::String(stmt.name.clone())),
        ("params".into(), JsonValue::Array(params)),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_def_abstract_prop(value: &JsonValue) -> Result<DefAbstractPropStmt, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "def_abstract_prop" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `def_abstract_prop`, got `{kind}`"
        )));
    }
    let name = JsonValue::get(map, "name")?.as_str()?.to_string();
    let params = JsonValue::get(map, "params")?
        .as_array()?
        .iter()
        .map(|p| Ok(p.as_str()?.to_string()))
        .collect::<Result<Vec<_>, KbCodecError>>()?;
    let line_file = decode_line_file(JsonValue::get(map, "line_file")?)?;
    Ok(DefAbstractPropStmt {
        name,
        params,
        line_file,
    })
}
