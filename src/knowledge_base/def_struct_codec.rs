//! Store / load one `DefStructStmt` as JSON.
//!
//! MVP: fields + `equivalent_facts` via existing Fact wire (atomic / forall).
//! Optional `param_def_with_dom` supported when present.

use super::def_prop_codec::{
    decode_bound_name, decode_fact, decode_line_file, decode_obj, decode_quantifier_free_fact,
    decode_typed_parameter_list, encode_bound_name, encode_fact, encode_line_file, encode_obj,
    encode_quantifier_free_fact, encode_typed_parameter_list, KbCodecError,
};
use super::json_mini::JsonValue;
use crate::ast::stmt::{DefStructStmt, StructFieldDef};
use std::fs;
use std::path::Path;

pub fn store_def_struct(stmt: &DefStructStmt) -> Result<String, KbCodecError> {
    Ok(encode_def_struct(stmt)?.stringify_pretty())
}

pub fn load_def_struct(text: &str) -> Result<DefStructStmt, KbCodecError> {
    decode_def_struct(&JsonValue::parse(text)?)
}

pub fn write_def_struct(path: &Path, stmt: &DefStructStmt) -> Result<(), KbCodecError> {
    let mut body = store_def_struct(stmt)?;
    if !body.ends_with('\n') {
        body.push('\n');
    }
    fs::write(path, body).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

pub fn read_def_struct(path: &Path) -> Result<DefStructStmt, KbCodecError> {
    let text = fs::read_to_string(path).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })?;
    load_def_struct(&text)
}

fn encode_def_struct(stmt: &DefStructStmt) -> Result<JsonValue, KbCodecError> {
    let fields = stmt
        .fields
        .iter()
        .map(encode_struct_field)
        .collect::<Result<Vec<_>, _>>()?;
    let laws = stmt
        .equivalent_facts
        .iter()
        .map(encode_fact)
        .collect::<Result<Vec<_>, _>>()?;
    let param = match &stmt.param_def_with_dom {
        None => JsonValue::Null,
        Some((params, dom)) => {
            let dom_v = dom
                .iter()
                .map(encode_quantifier_free_fact)
                .collect::<Result<Vec<_>, _>>()?;
            JsonValue::object_from(vec![
                (
                    "typed_parameters".into(),
                    encode_typed_parameter_list(params)?,
                ),
                ("dom_facts".into(), JsonValue::Array(dom_v)),
            ])
        }
    };
    Ok(JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("def_struct".into())),
        ("name".into(), JsonValue::String(stmt.name.clone())),
        ("param_def_with_dom".into(), param),
        ("fields".into(), JsonValue::Array(fields)),
        ("equivalent_facts".into(), JsonValue::Array(laws)),
        ("line_file".into(), encode_line_file(&stmt.line_file)?),
    ]))
}

fn decode_def_struct(value: &JsonValue) -> Result<DefStructStmt, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "def_struct" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `def_struct`, got `{kind}`"
        )));
    }
    let param_def_with_dom = match JsonValue::get(map, "param_def_with_dom")? {
        JsonValue::Null => None,
        other => {
            let pmap = other.as_object()?;
            let params = decode_typed_parameter_list(JsonValue::get(pmap, "typed_parameters")?)?;
            let dom = JsonValue::get(pmap, "dom_facts")?
                .as_array()?
                .iter()
                .map(decode_quantifier_free_fact)
                .collect::<Result<Vec<_>, _>>()?;
            Some((params, dom))
        }
    };
    let fields = JsonValue::get(map, "fields")?
        .as_array()?
        .iter()
        .map(decode_struct_field)
        .collect::<Result<Vec<_>, _>>()?;
    let equivalent_facts = JsonValue::get(map, "equivalent_facts")?
        .as_array()?
        .iter()
        .map(decode_fact)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(DefStructStmt {
        name: JsonValue::get(map, "name")?.as_str()?.to_string(),
        param_def_with_dom,
        fields,
        equivalent_facts,
        line_file: decode_line_file(JsonValue::get(map, "line_file")?)?,
    })
}

fn encode_struct_field(field: &StructFieldDef) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("binding".into(), encode_bound_name(&field.binding)?),
        ("field_type".into(), encode_obj(&field.field_type)?),
    ]))
}

fn decode_struct_field(value: &JsonValue) -> Result<StructFieldDef, KbCodecError> {
    let map = value.as_object()?;
    Ok(StructFieldDef {
        binding: decode_bound_name(JsonValue::get(map, "binding")?)?,
        field_type: decode_obj(JsonValue::get(map, "field_type")?)?,
    })
}
