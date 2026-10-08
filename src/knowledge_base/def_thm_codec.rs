//! Store / load one `DefThmStmt` as JSON.
//!
//! MVP: stores `name` + `fact` + `line_file`. `prove_process` must be empty
//! (Stmt-tree codec deferred). Importer `by thm` only needs the theorem fact.

use super::def_prop_codec::{
    decode_fact, decode_line_file, encode_fact, encode_line_file, KbCodecError,
};
use super::json_mini::JsonValue;
use crate::ast::stmt::DefThmStmt;
use std::fs;
use std::path::Path;

pub fn store_def_thm(stmt: &DefThmStmt) -> Result<String, KbCodecError> {
    Ok(encode_def_thm(stmt)?.stringify_pretty())
}

pub fn load_def_thm(text: &str) -> Result<DefThmStmt, KbCodecError> {
    decode_def_thm(&JsonValue::parse(text)?)
}

pub fn write_def_thm(path: &Path, stmt: &DefThmStmt) -> Result<(), KbCodecError> {
    let mut body = store_def_thm(stmt)?;
    if !body.ends_with('\n') {
        body.push('\n');
    }
    fs::write(path, body).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

pub fn read_def_thm(path: &Path) -> Result<DefThmStmt, KbCodecError> {
    let text = fs::read_to_string(path).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })?;
    load_def_thm(&text)
}

fn encode_def_thm(stmt: &DefThmStmt) -> Result<JsonValue, KbCodecError> {
    if !stmt.prove_process.is_empty() {
        return Err(KbCodecError::Unsupported(
            "DefThmStmt.prove_process Stmt codec deferred; store theorems with empty proof body"
                .to_string(),
        ));
    }
    Ok(JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("def_thm".into())),
        ("name".into(), JsonValue::String(stmt.name.clone())),
        ("fact".into(), encode_fact(&stmt.fact)?),
        ("prove_process".into(), JsonValue::Array(Vec::new())),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_def_thm(value: &JsonValue) -> Result<DefThmStmt, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "def_thm" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `def_thm`, got `{kind}`"
        )));
    }
    let name = JsonValue::get(map, "name")?.as_str()?.to_string();
    let fact = decode_fact(JsonValue::get(map, "fact")?)?;
    let prove = JsonValue::get(map, "prove_process")?.as_array()?;
    if !prove.is_empty() {
        return Err(KbCodecError::Unsupported(
            "DefThmStmt.prove_process non-empty in wire; Stmt codec deferred".to_string(),
        ));
    }
    let line_file = decode_line_file(JsonValue::get(map, "line_file")?)?;
    Ok(DefThmStmt {
        name,
        fact,
        prove_process: Vec::new(),
        line_file,
    })
}
