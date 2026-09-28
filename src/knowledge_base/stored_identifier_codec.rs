//! Store / load one `StoredIdentifierDefinition` entry as JSON.
//!
//! Supported tags: `LetObj`, `HaveObjEqual`, `HaveObjInNonemptySetOrParamType`,
//! `HaveFnEqual`. Other have-fn / obtain / trust variants → Unsupported.

use super::def_prop_codec::{
    decode_anonymous_fn, decode_bound_name, decode_line_file, decode_obj,
    decode_typed_parameter_list, encode_anonymous_fn, encode_bound_name, encode_line_file,
    encode_obj, encode_typed_parameter_list, KbCodecError,
};
use super::json_mini::JsonValue;
use crate::ast::stmt::{
    HaveFnEqualStmt, HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt, LetObjStmt,
};
use crate::exec_env::StoredIdentifierDefinition;
use std::fs;
use std::path::Path;
use std::rc::Rc;

pub fn store_stored_identifier(
    entry: &StoredIdentifierDefinition,
) -> Result<String, KbCodecError> {
    Ok(encode_stored_identifier(entry)?.stringify_pretty())
}

pub fn load_stored_identifier(text: &str) -> Result<StoredIdentifierDefinition, KbCodecError> {
    decode_stored_identifier(&JsonValue::parse(text)?)
}

pub fn write_stored_identifier(
    path: &Path,
    entry: &StoredIdentifierDefinition,
) -> Result<(), KbCodecError> {
    let mut body = store_stored_identifier(entry)?;
    if !body.ends_with('\n') {
        body.push('\n');
    }
    fs::write(path, body).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

pub fn read_stored_identifier(path: &Path) -> Result<StoredIdentifierDefinition, KbCodecError> {
    let text = fs::read_to_string(path).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })?;
    load_stored_identifier(&text)
}

fn encode_stored_identifier(
    entry: &StoredIdentifierDefinition,
) -> Result<JsonValue, KbCodecError> {
    match entry {
        StoredIdentifierDefinition::LetObj((plain, stmt)) => Ok(JsonValue::object_from(vec![
            (
                "kind".into(),
                JsonValue::String("stored_identifier".into()),
            ),
            ("tag".into(), JsonValue::String("LetObj".into())),
            ("plain_name".into(), JsonValue::String(plain.clone())),
            ("stmt".into(), encode_let_obj(stmt)?),
        ])),
        StoredIdentifierDefinition::HaveObjEqual((plain, stmt)) => {
            Ok(JsonValue::object_from(vec![
                (
                    "kind".into(),
                    JsonValue::String("stored_identifier".into()),
                ),
                ("tag".into(), JsonValue::String("HaveObjEqual".into())),
                ("plain_name".into(), JsonValue::String(plain.clone())),
                ("stmt".into(), encode_have_obj_equal(stmt)?),
            ]))
        }
        StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((plain, stmt)) => {
            Ok(JsonValue::object_from(vec![
                (
                    "kind".into(),
                    JsonValue::String("stored_identifier".into()),
                ),
                (
                    "tag".into(),
                    JsonValue::String("HaveObjInNonemptySetOrParamType".into()),
                ),
                ("plain_name".into(), JsonValue::String(plain.clone())),
                ("stmt".into(), encode_have_obj_in(stmt)?),
            ]))
        }
        StoredIdentifierDefinition::HaveFnEqual((plain, stmt)) => Ok(JsonValue::object_from(vec![
            (
                "kind".into(),
                JsonValue::String("stored_identifier".into()),
            ),
            ("tag".into(), JsonValue::String("HaveFnEqual".into())),
            ("plain_name".into(), JsonValue::String(plain.clone())),
            ("stmt".into(), encode_have_fn_equal(stmt)?),
        ])),
        other => Err(KbCodecError::Unsupported(format!(
            "StoredIdentifierDefinition variant `{other:?}` (kb identifier subset)"
        ))),
    }
}

fn decode_stored_identifier(
    value: &JsonValue,
) -> Result<StoredIdentifierDefinition, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "stored_identifier" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `stored_identifier`, got `{kind}`"
        )));
    }
    let plain = JsonValue::get(map, "plain_name")?.as_str()?.to_string();
    let stmt_v = JsonValue::get(map, "stmt")?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "LetObj" => Ok(StoredIdentifierDefinition::LetObj((
            plain,
            Rc::new(decode_let_obj(stmt_v)?),
        ))),
        "HaveObjEqual" => Ok(StoredIdentifierDefinition::HaveObjEqual((
            plain,
            Rc::new(decode_have_obj_equal(stmt_v)?),
        ))),
        "HaveObjInNonemptySetOrParamType" => Ok(
            StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((
                plain,
                Rc::new(decode_have_obj_in(stmt_v)?),
            )),
        ),
        "HaveFnEqual" => Ok(StoredIdentifierDefinition::HaveFnEqual((
            plain,
            Rc::new(decode_have_fn_equal(stmt_v)?),
        ))),
        other => Err(KbCodecError::Unsupported(format!(
            "stored_identifier tag `{other}` (kb identifier subset)"
        ))),
    }
}

fn encode_let_obj(stmt: &LetObjStmt) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("name".into(), encode_bound_name(&stmt.name)?),
        ("value".into(), encode_obj(&stmt.value)?),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_let_obj(value: &JsonValue) -> Result<LetObjStmt, KbCodecError> {
    let map = value.as_object()?;
    Ok(LetObjStmt {
        name: decode_bound_name(JsonValue::get(map, "name")?)?,
        value: decode_obj(JsonValue::get(map, "value")?)?,
        line_file: decode_line_file(JsonValue::get(map, "line_file")?)?,
    })
}

fn encode_have_obj_equal(stmt: &HaveObjEqualStmt) -> Result<JsonValue, KbCodecError> {
    let objs = stmt
        .objs_equal_to
        .iter()
        .map(encode_obj)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![
        (
            "param_def".into(),
            encode_typed_parameter_list(&stmt.param_def)?,
        ),
        ("objs_equal_to".into(), JsonValue::Array(objs)),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_have_obj_equal(value: &JsonValue) -> Result<HaveObjEqualStmt, KbCodecError> {
    let map = value.as_object()?;
    let objs = JsonValue::get(map, "objs_equal_to")?
        .as_array()?
        .iter()
        .map(decode_obj)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(HaveObjEqualStmt {
        param_def: decode_typed_parameter_list(JsonValue::get(map, "param_def")?)?,
        objs_equal_to: objs,
        line_file: decode_line_file(JsonValue::get(map, "line_file")?)?,
    })
}

fn encode_have_obj_in(
    stmt: &HaveObjInNonemptySetOrParamTypeStmt,
) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        (
            "param_def".into(),
            encode_typed_parameter_list(&stmt.param_def)?,
        ),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_have_obj_in(
    value: &JsonValue,
) -> Result<HaveObjInNonemptySetOrParamTypeStmt, KbCodecError> {
    let map = value.as_object()?;
    Ok(HaveObjInNonemptySetOrParamTypeStmt {
        param_def: decode_typed_parameter_list(JsonValue::get(map, "param_def")?)?,
        line_file: decode_line_file(JsonValue::get(map, "line_file")?)?,
    })
}

fn encode_have_fn_equal(stmt: &HaveFnEqualStmt) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("name".into(), JsonValue::String(stmt.name.clone())),
        (
            "equal_to_anonymous_fn".into(),
            encode_anonymous_fn(&stmt.equal_to_anonymous_fn)?,
        ),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_have_fn_equal(value: &JsonValue) -> Result<HaveFnEqualStmt, KbCodecError> {
    let map = value.as_object()?;
    Ok(HaveFnEqualStmt {
        name: JsonValue::get(map, "name")?.as_str()?.to_string(),
        equal_to_anonymous_fn: decode_anonymous_fn(JsonValue::get(
            map,
            "equal_to_anonymous_fn",
        )?)?,
        line_file: decode_line_file(JsonValue::get(map, "line_file")?)?,
    })
}
