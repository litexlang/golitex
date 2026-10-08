//! Store / load one `AxiomStmt` as JSON.

use super::def_prop_codec::{
    decode_forall_fact, decode_line_file, encode_forall_fact, encode_line_file, KbCodecError,
};
use super::json_mini::JsonValue;
use crate::ast::stmt::AxiomStmt;
use std::fs;
use std::path::Path;

pub fn store_axiom(stmt: &AxiomStmt) -> Result<String, KbCodecError> {
    Ok(encode_axiom(stmt)?.stringify_pretty())
}

pub fn load_axiom(text: &str) -> Result<AxiomStmt, KbCodecError> {
    decode_axiom(&JsonValue::parse(text)?)
}

pub fn write_axiom(path: &Path, stmt: &AxiomStmt) -> Result<(), KbCodecError> {
    let mut body = store_axiom(stmt)?;
    if !body.ends_with('\n') {
        body.push('\n');
    }
    fs::write(path, body).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

pub fn read_axiom(path: &Path) -> Result<AxiomStmt, KbCodecError> {
    let text = fs::read_to_string(path).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })?;
    load_axiom(&text)
}

fn encode_axiom(stmt: &AxiomStmt) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("axiom".into())),
        ("name".into(), JsonValue::String(stmt.name.clone())),
        ("forall_fact".into(), encode_forall_fact(&stmt.forall_fact)?),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_axiom(value: &JsonValue) -> Result<AxiomStmt, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "axiom" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `axiom`, got `{kind}`"
        )));
    }
    Ok(AxiomStmt {
        name: JsonValue::get(map, "name")?.as_str()?.to_string(),
        forall_fact: decode_forall_fact(JsonValue::get(map, "forall_fact")?)?,
        line_file: decode_line_file(JsonValue::get(map, "line_file")?)?,
    })
}
