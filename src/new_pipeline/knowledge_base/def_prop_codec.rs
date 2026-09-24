//! Store / load one `DefPropStmt` as JSON (hand-written codec, no serde on AST).
//!
//! Wire shape matches `knowledge_base/README.md` (kind `def_prop`).
//! Obj / Fact coverage is a growing subset; unsupported variants return
//! `KbCodecError::Unsupported`.

use super::json_mini::{JsonError, JsonValue};
use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, Fact, GreaterEqualFact, GreaterFact, InFact, LessEqualFact, LessFact,
    NotEqualFact, NotGreaterEqualFact, NotGreaterFact, NotInFact, NotLessEqualFact, NotLessFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{
    IdentifierObj, Literal, Number, Obj, StandardSet,
};
use crate::new_pipeline::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::ast::stmt::DefPropStmt;
use crate::new_pipeline::runtime::runtime_ids::{FactId, IdentifierId};
use crate::new_pipeline::runtime::RealOrVirtualPath;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KbCodecError {
    Unsupported(String),
    Json(String),
    Shape(String),
    Io { path: PathBuf, message: String },
}

impl fmt::Display for KbCodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KbCodecError::Unsupported(msg) => write!(f, "unsupported kb wire shape: {msg}"),
            KbCodecError::Json(msg) => write!(f, "kb json error: {msg}"),
            KbCodecError::Shape(msg) => write!(f, "kb shape error: {msg}"),
            KbCodecError::Io { path, message } => {
                write!(f, "kb io error at {}: {message}", path.display())
            }
        }
    }
}

impl From<JsonError> for KbCodecError {
    fn from(err: JsonError) -> Self {
        KbCodecError::Json(err.0)
    }
}

/// Encode one `DefPropStmt` to pretty JSON text (2-space indent).
pub fn store_def_prop(prop: &DefPropStmt) -> Result<String, KbCodecError> {
    Ok(encode_def_prop(prop)?.stringify_pretty())
}

/// Decode one `DefPropStmt` from JSON text.
pub fn load_def_prop(text: &str) -> Result<DefPropStmt, KbCodecError> {
    let value = JsonValue::parse(text)?;
    decode_def_prop(&value)
}

/// Write one `DefPropStmt` JSON file (pretty, trailing newline).
pub fn write_def_prop(path: &Path, prop: &DefPropStmt) -> Result<(), KbCodecError> {
    let text = store_def_prop(prop)?;
    let mut body = text;
    if !body.ends_with('\n') {
        body.push('\n');
    }
    fs::write(path, body).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

/// Read one `DefPropStmt` JSON file.
pub fn read_def_prop(path: &Path) -> Result<DefPropStmt, KbCodecError> {
    let text = fs::read_to_string(path).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })?;
    load_def_prop(&text)
}

fn encode_def_prop(prop: &DefPropStmt) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("def_prop".into())),
        ("name".into(), JsonValue::String(prop.name.clone())),
        (
            "typed_parameters".into(),
            encode_typed_parameter_list(&prop.typed_parameters)?,
        ),
        (
            "iff_facts".into(),
            JsonValue::Array(
                prop.iff_facts
                    .iter()
                    .map(encode_fact)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        ),
        ("line_file".into(), encode_line_file(&prop.line_file)?),
    ]))
}

fn decode_def_prop(value: &JsonValue) -> Result<DefPropStmt, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "def_prop" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `def_prop`, got `{kind}`"
        )));
    }
    let name = JsonValue::get(map, "name")?.as_str()?.to_string();
    let typed_parameters =
        decode_typed_parameter_list(JsonValue::get(map, "typed_parameters")?)?;
    let iff_facts = JsonValue::get(map, "iff_facts")?
        .as_array()?
        .iter()
        .map(decode_fact)
        .collect::<Result<Vec<_>, _>>()?;
    let line_file = decode_line_file(JsonValue::get(map, "line_file")?)?;
    Ok(DefPropStmt {
        name,
        typed_parameters,
        iff_facts,
        line_file,
    })
}

fn encode_typed_parameter_list(list: &TypedParameterList) -> Result<JsonValue, KbCodecError> {
    let groups = list
        .groups
        .iter()
        .map(encode_typed_parameter_group)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![(
        "groups".into(),
        JsonValue::Array(groups),
    )]))
}

fn decode_typed_parameter_list(value: &JsonValue) -> Result<TypedParameterList, KbCodecError> {
    let map = value.as_object()?;
    let groups = JsonValue::get(map, "groups")?
        .as_array()?
        .iter()
        .map(decode_typed_parameter_group)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(TypedParameterList { groups })
}

fn encode_typed_parameter_group(group: &TypedParameterGroup) -> Result<JsonValue, KbCodecError> {
    let params = group
        .params
        .iter()
        .map(encode_bound_name)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![
        ("params".into(), JsonValue::Array(params)),
        ("param_type".into(), encode_param_type(&group.param_type)?),
    ]))
}

fn decode_typed_parameter_group(value: &JsonValue) -> Result<TypedParameterGroup, KbCodecError> {
    let map = value.as_object()?;
    let params = JsonValue::get(map, "params")?
        .as_array()?
        .iter()
        .map(decode_bound_name)
        .collect::<Result<Vec<_>, _>>()?;
    let param_type = decode_param_type(JsonValue::get(map, "param_type")?)?;
    Ok(TypedParameterGroup { params, param_type })
}

fn encode_bound_name(name: &BoundName) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("id".into(), JsonValue::Number(name.id.value() as f64)),
        ("name".into(), JsonValue::String(name.name.clone())),
    ]))
}

fn decode_bound_name(value: &JsonValue) -> Result<BoundName, KbCodecError> {
    let map = value.as_object()?;
    let id = IdentifierId::new(JsonValue::get(map, "id")?.as_u64()?);
    let name = JsonValue::get(map, "name")?.as_str()?.to_string();
    Ok(BoundName::new(id, name))
}

fn encode_param_type(param_type: &ParamType) -> Result<JsonValue, KbCodecError> {
    match param_type {
        ParamType::Set(_) => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("Set".into()),
        )])),
        ParamType::NonemptySet(_) => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("NonemptySet".into()),
        )])),
        ParamType::FiniteSet(_) => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("FiniteSet".into()),
        )])),
        ParamType::Obj(obj) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("Obj".into())),
            ("obj".into(), encode_obj(obj)?),
        ])),
    }
}

fn decode_param_type(value: &JsonValue) -> Result<ParamType, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "Set" => Ok(ParamType::Set(Set {})),
        "NonemptySet" => Ok(ParamType::NonemptySet(NonemptySet {})),
        "FiniteSet" => Ok(ParamType::FiniteSet(FiniteSet {})),
        "Obj" => Ok(ParamType::Obj(decode_obj(JsonValue::get(map, "obj")?)?)),
        other => Err(KbCodecError::Unsupported(format!(
            "ParamType tag `{other}`"
        ))),
    }
}

fn encode_line_file(line_file: &LineFile) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        (
            "line".into(),
            JsonValue::Number(line_file.line as f64),
        ),
        ("path".into(), encode_path(&line_file.path)?),
    ]))
}

fn decode_line_file(value: &JsonValue) -> Result<LineFile, KbCodecError> {
    let map = value.as_object()?;
    let line = JsonValue::get(map, "line")?.as_u64()? as usize;
    let path = decode_path(JsonValue::get(map, "path")?)?;
    Ok(LineFile::new(line, path))
}

fn encode_path(path: &RealOrVirtualPath) -> Result<JsonValue, KbCodecError> {
    match path {
        RealOrVirtualPath::Real(p) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("Real".into())),
            (
                "path".into(),
                JsonValue::String(p.to_string_lossy().into_owned()),
            ),
        ])),
        RealOrVirtualPath::Eval => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("Eval".into()),
        )])),
        RealOrVirtualPath::Repl => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("Repl".into()),
        )])),
    }
}

fn decode_path(value: &JsonValue) -> Result<RealOrVirtualPath, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "Real" => Ok(RealOrVirtualPath::Real(PathBuf::from(
            JsonValue::get(map, "path")?.as_str()?,
        ))),
        "Eval" => Ok(RealOrVirtualPath::Eval),
        "Repl" => Ok(RealOrVirtualPath::Repl),
        other => Err(KbCodecError::Unsupported(format!(
            "RealOrVirtualPath tag `{other}`"
        ))),
    }
}

fn encode_optional_line_file(
    line_file: &Option<LineFile>,
) -> Result<JsonValue, KbCodecError> {
    match line_file {
        None => Ok(JsonValue::Null),
        Some(lf) => encode_line_file(lf),
    }
}

fn decode_optional_line_file(value: &JsonValue) -> Result<Option<LineFile>, KbCodecError> {
    match value {
        JsonValue::Null => Ok(None),
        other => Ok(Some(decode_line_file(other)?)),
    }
}

fn encode_fact(fact: &Fact) -> Result<JsonValue, KbCodecError> {
    match fact {
        Fact::AtomicFact(atomic) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("AtomicFact".into())),
            ("atomic".into(), encode_atomic_fact(atomic)?),
        ])),
        other => Err(KbCodecError::Unsupported(format!(
            "Fact variant `{other:?}` (def_prop codec subset)"
        ))),
    }
}

fn decode_fact(value: &JsonValue) -> Result<Fact, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "AtomicFact" => Ok(Fact::AtomicFact(decode_atomic_fact(JsonValue::get(
            map, "atomic",
        )?)?)),
        other => Err(KbCodecError::Unsupported(format!(
            "Fact tag `{other}` (def_prop codec subset)"
        ))),
    }
}

fn encode_atomic_fact(atomic: &AtomicFact) -> Result<JsonValue, KbCodecError> {
    match atomic {
        AtomicFact::GreaterFact(f) => encode_binary_compare(
            "GreaterFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::LessFact(f) => {
            encode_binary_compare("LessFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
        AtomicFact::GreaterEqualFact(f) => encode_binary_compare(
            "GreaterEqualFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::LessEqualFact(f) => encode_binary_compare(
            "LessEqualFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::EqualFact(f) => {
            encode_binary_compare("EqualFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
        AtomicFact::NotGreaterFact(f) => encode_binary_compare(
            "NotGreaterFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::NotLessFact(f) => encode_binary_compare(
            "NotLessFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::NotGreaterEqualFact(f) => encode_binary_compare(
            "NotGreaterEqualFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::NotLessEqualFact(f) => encode_binary_compare(
            "NotLessEqualFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::NotEqualFact(f) => encode_binary_compare(
            "NotEqualFact",
            f.fact_id,
            &f.left,
            &f.right,
            &f.line_file,
        ),
        AtomicFact::InFact(f) => encode_in_like(
            "InFact",
            f.fact_id,
            &f.element,
            &f.set,
            &f.line_file,
        ),
        AtomicFact::NotInFact(f) => encode_in_like(
            "NotInFact",
            f.fact_id,
            &f.element,
            &f.set,
            &f.line_file,
        ),
        other => Err(KbCodecError::Unsupported(format!(
            "AtomicFact variant `{other:?}` (def_prop codec subset)"
        ))),
    }
}

fn encode_binary_compare(
    tag: &str,
    fact_id: FactId,
    left: &Obj,
    right: &Obj,
    line_file: &Option<LineFile>,
) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("tag".into(), JsonValue::String(tag.into())),
        (
            "fact_id".into(),
            JsonValue::Number(fact_id.value() as f64),
        ),
        ("left".into(), encode_obj(left)?),
        ("right".into(), encode_obj(right)?),
        (
            "line_file".into(),
            encode_optional_line_file(line_file)?,
        ),
    ]))
}

fn encode_in_like(
    tag: &str,
    fact_id: FactId,
    element: &Obj,
    set: &Obj,
    line_file: &Option<LineFile>,
) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("tag".into(), JsonValue::String(tag.into())),
        (
            "fact_id".into(),
            JsonValue::Number(fact_id.value() as f64),
        ),
        ("element".into(), encode_obj(element)?),
        ("set".into(), encode_obj(set)?),
        (
            "line_file".into(),
            encode_optional_line_file(line_file)?,
        ),
    ]))
}

fn decode_atomic_fact(value: &JsonValue) -> Result<AtomicFact, KbCodecError> {
    let map = value.as_object()?;
    let tag = JsonValue::get(map, "tag")?.as_str()?;
    match tag {
        "GreaterFact"
        | "LessFact"
        | "GreaterEqualFact"
        | "LessEqualFact"
        | "EqualFact"
        | "NotGreaterFact"
        | "NotLessFact"
        | "NotGreaterEqualFact"
        | "NotLessEqualFact"
        | "NotEqualFact" => {
            let fact_id = FactId::new(JsonValue::get(map, "fact_id")?.as_u64()?);
            let left = decode_obj(JsonValue::get(map, "left")?)?;
            let right = decode_obj(JsonValue::get(map, "right")?)?;
            let line_file = decode_optional_line_file(JsonValue::get(map, "line_file")?)?;
            Ok(match tag {
                "GreaterFact" => AtomicFact::GreaterFact(GreaterFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "LessFact" => AtomicFact::LessFact(LessFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "GreaterEqualFact" => AtomicFact::GreaterEqualFact(GreaterEqualFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "LessEqualFact" => AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "EqualFact" => AtomicFact::EqualFact(EqualFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "NotGreaterFact" => AtomicFact::NotGreaterFact(NotGreaterFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "NotLessFact" => AtomicFact::NotLessFact(NotLessFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "NotGreaterEqualFact" => AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "NotLessEqualFact" => AtomicFact::NotLessEqualFact(NotLessEqualFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                "NotEqualFact" => AtomicFact::NotEqualFact(NotEqualFact {
                    fact_id,
                    left,
                    right,
                    line_file,
                }),
                _ => unreachable!(),
            })
        }
        "InFact" | "NotInFact" => {
            let fact_id = FactId::new(JsonValue::get(map, "fact_id")?.as_u64()?);
            let element = decode_obj(JsonValue::get(map, "element")?)?;
            let set = decode_obj(JsonValue::get(map, "set")?)?;
            let line_file = decode_optional_line_file(JsonValue::get(map, "line_file")?)?;
            Ok(match tag {
                "InFact" => AtomicFact::InFact(InFact {
                    fact_id,
                    element,
                    set,
                    line_file,
                }),
                "NotInFact" => AtomicFact::NotInFact(NotInFact {
                    fact_id,
                    element,
                    set,
                    line_file,
                }),
                _ => unreachable!(),
            })
        }
        other => Err(KbCodecError::Unsupported(format!(
            "AtomicFact tag `{other}` (def_prop codec subset)"
        ))),
    }
}

fn encode_obj(obj: &Obj) -> Result<JsonValue, KbCodecError> {
    match obj {
        Obj::Identifier(id) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("Identifier".into())),
            ("identifier".into(), encode_identifier_obj(id)?),
        ])),
        Obj::Literal(lit) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("Literal".into())),
            ("literal".into(), encode_literal(lit)?),
        ])),
        Obj::StandardSet(set) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("StandardSet".into())),
            ("set".into(), JsonValue::String(standard_set_name(set).into())),
        ])),
        other => Err(KbCodecError::Unsupported(format!(
            "Obj variant `{other:?}` (def_prop codec subset)"
        ))),
    }
}

fn decode_obj(value: &JsonValue) -> Result<Obj, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "Identifier" => Ok(Obj::Identifier(decode_identifier_obj(JsonValue::get(
            map,
            "identifier",
        )?)?)),
        "Literal" => Ok(Obj::Literal(decode_literal(JsonValue::get(
            map, "literal",
        )?)?)),
        "StandardSet" => Ok(Obj::StandardSet(decode_standard_set(
            JsonValue::get(map, "set")?.as_str()?,
        )?)),
        other => Err(KbCodecError::Unsupported(format!(
            "Obj tag `{other}` (def_prop codec subset)"
        ))),
    }
}

fn encode_identifier_obj(id: &IdentifierObj) -> Result<JsonValue, KbCodecError> {
    match id {
        IdentifierObj::Plain { id, name } => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("Plain".into())),
            ("id".into(), JsonValue::Number(id.value() as f64)),
            ("name".into(), JsonValue::String(name.clone())),
        ])),
        IdentifierObj::WithExportFileId {
            export_file_id,
            name,
        } => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("WithExportFileId".into())),
            (
                "export_file_id".into(),
                JsonValue::Number(*export_file_id as f64),
            ),
            ("name".into(), JsonValue::String(name.clone())),
        ])),
        IdentifierObj::WithModAndExportFileId {
            global_mod_id,
            export_file_id,
            name,
        } => Ok(JsonValue::object_from(vec![
            (
                "tag".into(),
                JsonValue::String("WithModAndExportFileId".into()),
            ),
            (
                "global_mod_id".into(),
                JsonValue::Number(*global_mod_id as f64),
            ),
            (
                "export_file_id".into(),
                JsonValue::Number(*export_file_id as f64),
            ),
            ("name".into(), JsonValue::String(name.clone())),
        ])),
    }
}

fn decode_identifier_obj(value: &JsonValue) -> Result<IdentifierObj, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "Plain" => Ok(IdentifierObj::plain(
            IdentifierId::new(JsonValue::get(map, "id")?.as_u64()?),
            JsonValue::get(map, "name")?.as_str()?.to_string(),
        )),
        "WithExportFileId" => Ok(IdentifierObj::with_export_file_id(
            JsonValue::get(map, "export_file_id")?.as_u64()? as usize,
            JsonValue::get(map, "name")?.as_str()?.to_string(),
        )),
        "WithModAndExportFileId" => Ok(IdentifierObj::with_mod_and_export_file_id(
            JsonValue::get(map, "global_mod_id")?.as_u64()? as usize,
            JsonValue::get(map, "export_file_id")?.as_u64()? as usize,
            JsonValue::get(map, "name")?.as_str()?.to_string(),
        )),
        other => Err(KbCodecError::Unsupported(format!(
            "IdentifierObj tag `{other}`"
        ))),
    }
}

fn encode_literal(lit: &Literal) -> Result<JsonValue, KbCodecError> {
    match lit {
        Literal::Number(n) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("Number".into())),
            ("text".into(), JsonValue::String(n.normalized_value.clone())),
        ])),
        Literal::ImaginaryUnit(_) => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("ImaginaryUnit".into()),
        )])),
        Literal::EulerNumber(_) => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("EulerNumber".into()),
        )])),
        Literal::Pi(_) => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("Pi".into()),
        )])),
    }
}

fn decode_literal(value: &JsonValue) -> Result<Literal, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "Number" => Ok(Literal::Number(Number {
            normalized_value: JsonValue::get(map, "text")?.as_str()?.to_string(),
        })),
        "ImaginaryUnit" => Ok(Literal::ImaginaryUnit(
            crate::new_pipeline::ast::obj::ImaginaryUnit,
        )),
        "EulerNumber" => Ok(Literal::EulerNumber(
            crate::new_pipeline::ast::obj::EulerNumber,
        )),
        "Pi" => Ok(Literal::Pi(crate::new_pipeline::ast::obj::Pi)),
        other => Err(KbCodecError::Unsupported(format!(
            "Literal tag `{other}`"
        ))),
    }
}

fn standard_set_name(set: &StandardSet) -> &'static str {
    match set {
        StandardSet::NPos => "NPos",
        StandardSet::N => "N",
        StandardSet::Q => "Q",
        StandardSet::Z => "Z",
        StandardSet::R => "R",
        StandardSet::C => "C",
        StandardSet::QPos => "QPos",
        StandardSet::RPos => "RPos",
        StandardSet::QNeg => "QNeg",
        StandardSet::ZNeg => "ZNeg",
        StandardSet::RNeg => "RNeg",
        StandardSet::QStar => "QStar",
        StandardSet::ZStar => "ZStar",
        StandardSet::RStar => "RStar",
        StandardSet::CStar => "CStar",
    }
}

fn decode_standard_set(name: &str) -> Result<StandardSet, KbCodecError> {
    Ok(match name {
        "NPos" => StandardSet::NPos,
        "N" => StandardSet::N,
        "Q" => StandardSet::Q,
        "Z" => StandardSet::Z,
        "R" => StandardSet::R,
        "C" => StandardSet::C,
        "QPos" => StandardSet::QPos,
        "RPos" => StandardSet::RPos,
        "QNeg" => StandardSet::QNeg,
        "ZNeg" => StandardSet::ZNeg,
        "RNeg" => StandardSet::RNeg,
        "QStar" => StandardSet::QStar,
        "ZStar" => StandardSet::ZStar,
        "RStar" => StandardSet::RStar,
        "CStar" => StandardSet::CStar,
        other => {
            return Err(KbCodecError::Unsupported(format!(
                "StandardSet `{other}`"
            )))
        }
    })
}
