//! Store / load one `DefPropStmt` as JSON (hand-written codec, no serde on AST).
//!
//! Wire shape matches `knowledge_base/README.md` (kind `def_prop`).
//! Obj / Fact coverage is a growing subset; unsupported variants return
//! `KbCodecError::Unsupported`.

use super::json_mini::{JsonError, JsonValue};
use crate::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, GreaterEqualFact,
    GreaterFact, InFact, LessEqualFact, LessFact, NotEqualFact, NotGreaterEqualFact,
    NotGreaterFact, NotInFact, NotLessEqualFact, NotLessFact, QuantifierFreeFact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::names::BoundName;
use crate::ast::obj::{
    Add, AnonymousFn, ArithmeticOperator, Div, FnSet, FunctionSpace, IdentifierObj, Literal, Mul,
    Neg, Number, Obj, StandardSet, Sub,
};
use crate::ast::param::{
    FiniteSet, NonemptySet, ParamType, Set, SetBoundParameterGroup, SetBoundParameterList,
    TypedParameterGroup, TypedParameterList,
};
use crate::ast::stmt::DefPropStmt;
use crate::runtime::runtime_ids::{FactId, IdentifierId};
use crate::runtime::CodeSource;
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
    let typed_parameters = decode_typed_parameter_list(JsonValue::get(map, "typed_parameters")?)?;
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

pub(crate) fn encode_typed_parameter_list(
    list: &TypedParameterList,
) -> Result<JsonValue, KbCodecError> {
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

pub(crate) fn decode_typed_parameter_list(
    value: &JsonValue,
) -> Result<TypedParameterList, KbCodecError> {
    let map = value.as_object()?;
    let groups = JsonValue::get(map, "groups")?
        .as_array()?
        .iter()
        .map(decode_typed_parameter_group)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(TypedParameterList { groups })
}

pub(crate) fn encode_typed_parameter_group(
    group: &TypedParameterGroup,
) -> Result<JsonValue, KbCodecError> {
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

pub(crate) fn decode_typed_parameter_group(
    value: &JsonValue,
) -> Result<TypedParameterGroup, KbCodecError> {
    let map = value.as_object()?;
    let params = JsonValue::get(map, "params")?
        .as_array()?
        .iter()
        .map(decode_bound_name)
        .collect::<Result<Vec<_>, _>>()?;
    let param_type = decode_param_type(JsonValue::get(map, "param_type")?)?;
    Ok(TypedParameterGroup { params, param_type })
}

pub(crate) fn encode_bound_name(name: &BoundName) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("id".into(), JsonValue::Number(name.id.value() as f64)),
        ("name".into(), JsonValue::String(name.name.clone())),
    ]))
}

pub(crate) fn decode_bound_name(value: &JsonValue) -> Result<BoundName, KbCodecError> {
    let map = value.as_object()?;
    let id = IdentifierId::new(JsonValue::get(map, "id")?.as_u64()?);
    let name = JsonValue::get(map, "name")?.as_str()?.to_string();
    Ok(BoundName::new(id, name))
}

pub(crate) fn encode_param_type(param_type: &ParamType) -> Result<JsonValue, KbCodecError> {
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

pub(crate) fn decode_param_type(value: &JsonValue) -> Result<ParamType, KbCodecError> {
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

pub(crate) fn encode_line_file(line_file: &SourceLine) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("line".into(), JsonValue::Number(line_file.line as f64)),
        ("origin".into(), encode_code_source(&line_file.origin)?),
    ]))
}

pub(crate) fn decode_line_file(value: &JsonValue) -> Result<SourceLine, KbCodecError> {
    let map = value.as_object()?;
    let line = JsonValue::get(map, "line")?.as_u64()? as usize;
    let origin = decode_code_source(JsonValue::get(map, "origin")?)?;
    Ok(SourceLine::new(line, origin))
}

pub(crate) fn encode_code_source(origin: &CodeSource) -> Result<JsonValue, KbCodecError> {
    match origin {
        CodeSource::Eval => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("Eval".into()),
        )])),
        CodeSource::Repl => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("Repl".into()),
        )])),
        CodeSource::StandaloneFile => Ok(JsonValue::object_from(vec![(
            "tag".into(),
            JsonValue::String("StandaloneFile".into()),
        )])),
        CodeSource::RootExport { export_file_id } => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("RootExport".into())),
            (
                "export_file_id".into(),
                JsonValue::Number(*export_file_id as f64),
            ),
        ])),
        CodeSource::ImportedExport {
            global_mod_id,
            export_file_id,
        } => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("ImportedExport".into())),
            (
                "global_mod_id".into(),
                JsonValue::Number(*global_mod_id as f64),
            ),
            (
                "export_file_id".into(),
                JsonValue::Number(*export_file_id as f64),
            ),
        ])),
    }
}

pub(crate) fn decode_code_source(value: &JsonValue) -> Result<CodeSource, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "Eval" => Ok(CodeSource::Eval),
        "Repl" => Ok(CodeSource::Repl),
        "StandaloneFile" => Ok(CodeSource::StandaloneFile),
        "RootExport" => Ok(CodeSource::RootExport {
            export_file_id: JsonValue::get(map, "export_file_id")?.as_u64()? as usize,
        }),
        "ImportedExport" => Ok(CodeSource::ImportedExport {
            global_mod_id: JsonValue::get(map, "global_mod_id")?.as_u64()? as usize,
            export_file_id: JsonValue::get(map, "export_file_id")?.as_u64()? as usize,
        }),
        other => Err(KbCodecError::Unsupported(format!(
            "CodeSource tag `{other}`"
        ))),
    }
}

pub(crate) fn encode_optional_line_file(
    line_file: &Option<SourceLine>,
) -> Result<JsonValue, KbCodecError> {
    match line_file {
        None => Ok(JsonValue::Null),
        Some(lf) => encode_line_file(lf),
    }
}

pub(crate) fn decode_optional_line_file(
    value: &JsonValue,
) -> Result<Option<SourceLine>, KbCodecError> {
    match value {
        JsonValue::Null => Ok(None),
        other => Ok(Some(decode_line_file(other)?)),
    }
}

pub(crate) fn encode_fact(fact: &Fact) -> Result<JsonValue, KbCodecError> {
    match fact {
        Fact::AtomicFact(atomic) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("AtomicFact".into())),
            ("atomic".into(), encode_atomic_fact(atomic)?),
        ])),
        Fact::ForallFact(forall) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("ForallFact".into())),
            ("forall".into(), encode_forall_fact(forall)?),
        ])),
        other => Err(KbCodecError::Unsupported(format!(
            "Fact variant `{other:?}` (kb wire subset)"
        ))),
    }
}

pub(crate) fn decode_fact(value: &JsonValue) -> Result<Fact, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "AtomicFact" => Ok(Fact::AtomicFact(decode_atomic_fact(JsonValue::get(
            map, "atomic",
        )?)?)),
        "ForallFact" => Ok(Fact::ForallFact(decode_forall_fact(JsonValue::get(
            map, "forall",
        )?)?)),
        other => Err(KbCodecError::Unsupported(format!(
            "Fact tag `{other}` (kb wire subset)"
        ))),
    }
}

pub(crate) fn encode_atomic_fact(atomic: &AtomicFact) -> Result<JsonValue, KbCodecError> {
    match atomic {
        AtomicFact::GreaterFact(f) => {
            encode_binary_compare("GreaterFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
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
        AtomicFact::LessEqualFact(f) => {
            encode_binary_compare("LessEqualFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
        AtomicFact::EqualFact(f) => {
            encode_binary_compare("EqualFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
        AtomicFact::NotGreaterFact(f) => {
            encode_binary_compare("NotGreaterFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
        AtomicFact::NotLessFact(f) => {
            encode_binary_compare("NotLessFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
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
        AtomicFact::NotEqualFact(f) => {
            encode_binary_compare("NotEqualFact", f.fact_id, &f.left, &f.right, &f.line_file)
        }
        AtomicFact::InFact(f) => {
            encode_in_like("InFact", f.fact_id, &f.element, &f.set, &f.line_file)
        }
        AtomicFact::NotInFact(f) => {
            encode_in_like("NotInFact", f.fact_id, &f.element, &f.set, &f.line_file)
        }
        other => Err(KbCodecError::Unsupported(format!(
            "AtomicFact variant `{other:?}` (def_prop codec subset)"
        ))),
    }
}

pub(crate) fn encode_binary_compare(
    tag: &str,
    fact_id: FactId,
    left: &Obj,
    right: &Obj,
    line_file: &Option<SourceLine>,
) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("tag".into(), JsonValue::String(tag.into())),
        ("fact_id".into(), JsonValue::Number(fact_id.value() as f64)),
        ("left".into(), encode_obj(left)?),
        ("right".into(), encode_obj(right)?),
        ("line_file".into(), encode_optional_line_file(line_file)?),
    ]))
}

pub(crate) fn encode_in_like(
    tag: &str,
    fact_id: FactId,
    element: &Obj,
    set: &Obj,
    line_file: &Option<SourceLine>,
) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("tag".into(), JsonValue::String(tag.into())),
        ("fact_id".into(), JsonValue::Number(fact_id.value() as f64)),
        ("element".into(), encode_obj(element)?),
        ("set".into(), encode_obj(set)?),
        ("line_file".into(), encode_optional_line_file(line_file)?),
    ]))
}

pub(crate) fn decode_atomic_fact(value: &JsonValue) -> Result<AtomicFact, KbCodecError> {
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

pub(crate) fn encode_obj(obj: &Obj) -> Result<JsonValue, KbCodecError> {
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
            (
                "set".into(),
                JsonValue::String(standard_set_name(set).into()),
            ),
        ])),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("AnonymousFn".into())),
            ("anonymous_fn".into(), encode_anonymous_fn(anon)?),
        ])),
        Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("FnSet".into())),
            ("fn_set".into(), encode_fn_set(fn_set)?),
        ])),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            Ok(JsonValue::object_from(vec![
                ("tag".into(), JsonValue::String("Add".into())),
                ("left".into(), encode_obj(left)?),
                ("right".into(), encode_obj(right)?),
            ]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) => {
            Ok(JsonValue::object_from(vec![
                ("tag".into(), JsonValue::String("Sub".into())),
                ("left".into(), encode_obj(left)?),
                ("right".into(), encode_obj(right)?),
            ]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) => {
            Ok(JsonValue::object_from(vec![
                ("tag".into(), JsonValue::String("Mul".into())),
                ("left".into(), encode_obj(left)?),
                ("right".into(), encode_obj(right)?),
            ]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })) => {
            Ok(JsonValue::object_from(vec![
                ("tag".into(), JsonValue::String("Div".into())),
                ("left".into(), encode_obj(left)?),
                ("right".into(), encode_obj(right)?),
            ]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg })) => {
            Ok(JsonValue::object_from(vec![
                ("tag".into(), JsonValue::String("Neg".into())),
                ("arg".into(), encode_obj(arg)?),
            ]))
        }
        other => Err(KbCodecError::Unsupported(format!(
            "Obj variant `{other:?}` (kb wire subset)"
        ))),
    }
}

pub(crate) fn decode_obj(value: &JsonValue) -> Result<Obj, KbCodecError> {
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
        "AnonymousFn" => Ok(Obj::FunctionSpace(FunctionSpace::AnonymousFn(
            decode_anonymous_fn(JsonValue::get(map, "anonymous_fn")?)?,
        ))),
        "FnSet" => Ok(Obj::FunctionSpace(FunctionSpace::FnSet(decode_fn_set(
            JsonValue::get(map, "fn_set")?,
        )?))),
        "Add" => Ok(Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
            left: Box::new(decode_obj(JsonValue::get(map, "left")?)?),
            right: Box::new(decode_obj(JsonValue::get(map, "right")?)?),
        }))),
        "Sub" => Ok(Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
            left: Box::new(decode_obj(JsonValue::get(map, "left")?)?),
            right: Box::new(decode_obj(JsonValue::get(map, "right")?)?),
        }))),
        "Mul" => Ok(Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(decode_obj(JsonValue::get(map, "left")?)?),
            right: Box::new(decode_obj(JsonValue::get(map, "right")?)?),
        }))),
        "Div" => Ok(Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: Box::new(decode_obj(JsonValue::get(map, "left")?)?),
            right: Box::new(decode_obj(JsonValue::get(map, "right")?)?),
        }))),
        "Neg" => Ok(Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
            arg: Box::new(decode_obj(JsonValue::get(map, "arg")?)?),
        }))),
        other => Err(KbCodecError::Unsupported(format!(
            "Obj tag `{other}` (kb wire subset)"
        ))),
    }
}

pub(crate) fn encode_identifier_obj(id: &IdentifierObj) -> Result<JsonValue, KbCodecError> {
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

pub(crate) fn decode_identifier_obj(value: &JsonValue) -> Result<IdentifierObj, KbCodecError> {
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

pub(crate) fn encode_literal(lit: &Literal) -> Result<JsonValue, KbCodecError> {
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

pub(crate) fn decode_literal(value: &JsonValue) -> Result<Literal, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "Number" => Ok(Literal::Number(Number::new(
            JsonValue::get(map, "text")?.as_str()?.to_string(),
        ))),
        "ImaginaryUnit" => Ok(Literal::ImaginaryUnit(crate::ast::obj::ImaginaryUnit)),
        "EulerNumber" => Ok(Literal::EulerNumber(crate::ast::obj::EulerNumber)),
        "Pi" => Ok(Literal::Pi(crate::ast::obj::Pi)),
        other => Err(KbCodecError::Unsupported(format!("Literal tag `{other}`"))),
    }
}

pub(crate) fn standard_set_name(set: &StandardSet) -> &'static str {
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

pub(crate) fn decode_standard_set(name: &str) -> Result<StandardSet, KbCodecError> {
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
        other => return Err(KbCodecError::Unsupported(format!("StandardSet `{other}`"))),
    })
}

pub(crate) fn encode_set_bound_parameter_list(
    list: &SetBoundParameterList,
) -> Result<JsonValue, KbCodecError> {
    let groups = list
        .groups
        .iter()
        .map(encode_set_bound_parameter_group)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![(
        "groups".into(),
        JsonValue::Array(groups),
    )]))
}

pub(crate) fn decode_set_bound_parameter_list(
    value: &JsonValue,
) -> Result<SetBoundParameterList, KbCodecError> {
    let map = value.as_object()?;
    let groups = JsonValue::get(map, "groups")?
        .as_array()?
        .iter()
        .map(decode_set_bound_parameter_group)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SetBoundParameterList { groups })
}

fn encode_set_bound_parameter_group(
    group: &SetBoundParameterGroup,
) -> Result<JsonValue, KbCodecError> {
    let params = group
        .params
        .iter()
        .map(encode_bound_name)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![
        ("params".into(), JsonValue::Array(params)),
        ("param_type".into(), encode_obj(group.param_type.as_ref())?),
    ]))
}

fn decode_set_bound_parameter_group(
    value: &JsonValue,
) -> Result<SetBoundParameterGroup, KbCodecError> {
    let map = value.as_object()?;
    let params = JsonValue::get(map, "params")?
        .as_array()?
        .iter()
        .map(decode_bound_name)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SetBoundParameterGroup {
        params,
        param_type: Box::new(decode_obj(JsonValue::get(map, "param_type")?)?),
    })
}

pub(crate) fn encode_quantifier_free_fact(
    fact: &QuantifierFreeFact,
) -> Result<JsonValue, KbCodecError> {
    match fact {
        QuantifierFreeFact::AtomicFact(atomic) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("AtomicFact".into())),
            ("atomic".into(), encode_atomic_fact(atomic)?),
        ])),
        other => Err(KbCodecError::Unsupported(format!(
            "QuantifierFreeFact `{other:?}` (kb wire subset)"
        ))),
    }
}

pub(crate) fn decode_quantifier_free_fact(
    value: &JsonValue,
) -> Result<QuantifierFreeFact, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "AtomicFact" => Ok(QuantifierFreeFact::AtomicFact(decode_atomic_fact(
            JsonValue::get(map, "atomic")?,
        )?)),
        other => Err(KbCodecError::Unsupported(format!(
            "QuantifierFreeFact tag `{other}`"
        ))),
    }
}

pub(crate) fn encode_fn_set(fn_set: &FnSet) -> Result<JsonValue, KbCodecError> {
    let dom = fn_set
        .dom_facts
        .iter()
        .map(encode_quantifier_free_fact)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![
        (
            "set_bound_parameters".into(),
            encode_set_bound_parameter_list(&fn_set.set_bound_parameters)?,
        ),
        ("dom_facts".into(), JsonValue::Array(dom)),
        ("ret_set".into(), encode_obj(fn_set.ret_set.as_ref())?),
    ]))
}

pub(crate) fn decode_fn_set(value: &JsonValue) -> Result<FnSet, KbCodecError> {
    let map = value.as_object()?;
    let dom = JsonValue::get(map, "dom_facts")?
        .as_array()?
        .iter()
        .map(decode_quantifier_free_fact)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(FnSet {
        set_bound_parameters: decode_set_bound_parameter_list(JsonValue::get(
            map,
            "set_bound_parameters",
        )?)?,
        dom_facts: dom,
        ret_set: Box::new(decode_obj(JsonValue::get(map, "ret_set")?)?),
    })
}

pub(crate) fn encode_anonymous_fn(anon: &AnonymousFn) -> Result<JsonValue, KbCodecError> {
    Ok(JsonValue::object_from(vec![
        ("body".into(), encode_fn_set(&anon.body)?),
        ("equal_to".into(), encode_obj(anon.equal_to.as_ref())?),
    ]))
}

pub(crate) fn decode_anonymous_fn(value: &JsonValue) -> Result<AnonymousFn, KbCodecError> {
    let map = value.as_object()?;
    Ok(AnonymousFn {
        body: decode_fn_set(JsonValue::get(map, "body")?)?,
        equal_to: Box::new(decode_obj(JsonValue::get(map, "equal_to")?)?),
    })
}

pub(crate) fn encode_exist_or_and_chain(
    fact: &ExistOrAndChainAtomicFact,
) -> Result<JsonValue, KbCodecError> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(atomic) => Ok(JsonValue::object_from(vec![
            ("tag".into(), JsonValue::String("AtomicFact".into())),
            ("atomic".into(), encode_atomic_fact(atomic)?),
        ])),
        other => Err(KbCodecError::Unsupported(format!(
            "ExistOrAndChainAtomicFact `{other:?}` (kb wire subset)"
        ))),
    }
}

pub(crate) fn decode_exist_or_and_chain(
    value: &JsonValue,
) -> Result<ExistOrAndChainAtomicFact, KbCodecError> {
    let map = value.as_object()?;
    match JsonValue::get(map, "tag")?.as_str()? {
        "AtomicFact" => Ok(ExistOrAndChainAtomicFact::AtomicFact(decode_atomic_fact(
            JsonValue::get(map, "atomic")?,
        )?)),
        other => Err(KbCodecError::Unsupported(format!(
            "ExistOrAndChainAtomicFact tag `{other}`"
        ))),
    }
}

pub(crate) fn encode_forall_fact(forall: &ForallFact) -> Result<JsonValue, KbCodecError> {
    let dom = forall
        .dom_facts
        .iter()
        .map(encode_fact)
        .collect::<Result<Vec<_>, _>>()?;
    let then_facts = forall
        .then_facts
        .iter()
        .map(encode_exist_or_and_chain)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(JsonValue::object_from(vec![
        (
            "fact_id".into(),
            JsonValue::Number(forall.fact_id.value() as f64),
        ),
        (
            "typed_parameters".into(),
            encode_typed_parameter_list(&forall.typed_parameters)?,
        ),
        ("dom_facts".into(), JsonValue::Array(dom)),
        ("then_facts".into(), JsonValue::Array(then_facts)),
        (
            "line_file".into(),
            encode_optional_line_file(&forall.line_file)?,
        ),
    ]))
}

pub(crate) fn decode_forall_fact(value: &JsonValue) -> Result<ForallFact, KbCodecError> {
    let map = value.as_object()?;
    let dom = JsonValue::get(map, "dom_facts")?
        .as_array()?
        .iter()
        .map(decode_fact)
        .collect::<Result<Vec<_>, _>>()?;
    let then_facts = JsonValue::get(map, "then_facts")?
        .as_array()?
        .iter()
        .map(decode_exist_or_and_chain)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ForallFact {
        fact_id: FactId::new(JsonValue::get(map, "fact_id")?.as_u64()?),
        typed_parameters: decode_typed_parameter_list(JsonValue::get(map, "typed_parameters")?)?,
        dom_facts: dom,
        then_facts,
        line_file: decode_optional_line_file(JsonValue::get(map, "line_file")?)?,
    })
}
