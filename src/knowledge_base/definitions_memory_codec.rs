//! Store / load one export's `DefinitionMemory` (supported kind subset).

use super::axiom_codec::{load_axiom, store_axiom};
use super::def_abstract_prop_codec::{load_def_abstract_prop, store_def_abstract_prop};
use super::def_prop_codec::{load_def_prop, store_def_prop, KbCodecError};
use super::def_struct_codec::{load_def_struct, store_def_struct};
use super::def_thm_codec::{load_def_thm, store_def_thm};
use super::json_mini::JsonValue;
use super::stored_identifier_codec::{load_stored_identifier, store_stored_identifier};
use crate::exec_env::exec_env::DefinitionMemory;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

pub fn store_definition_memory(defs: &DefinitionMemory) -> Result<String, KbCodecError> {
    Ok(encode_definition_memory(defs)?.stringify_pretty())
}

pub fn load_definition_memory(text: &str) -> Result<DefinitionMemory, KbCodecError> {
    decode_definition_memory(&JsonValue::parse(text)?)
}

pub fn write_definition_memory(path: &Path, defs: &DefinitionMemory) -> Result<(), KbCodecError> {
    let mut body = store_definition_memory(defs)?;
    if !body.ends_with('\n') {
        body.push('\n');
    }
    fs::write(path, body).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })
}

pub fn read_definition_memory(path: &Path) -> Result<DefinitionMemory, KbCodecError> {
    let text = fs::read_to_string(path).map_err(|error| KbCodecError::Io {
        path: path.to_path_buf(),
        message: error.to_string(),
    })?;
    load_definition_memory(&text)
}

fn encode_definition_memory(defs: &DefinitionMemory) -> Result<JsonValue, KbCodecError> {
    reject_unsupported_maps(defs)?;
    let mut identifiers = Vec::new();
    let mut id_keys: Vec<_> = defs.identifiers.keys().cloned().collect();
    id_keys.sort();
    for name in id_keys {
        let entry = defs.identifiers.get(&name).expect("key present");
        identifiers.push(JsonValue::parse(&store_stored_identifier(entry)?)?);
    }
    let mut predicates = Vec::new();
    let mut pred_keys: Vec<_> = defs.predicate_definitions.keys().cloned().collect();
    pred_keys.sort();
    for name in pred_keys {
        let stmt = defs.predicate_definitions.get(&name).expect("key present");
        predicates.push(JsonValue::parse(&store_def_prop(stmt)?)?);
    }
    let mut abstracts = Vec::new();
    let mut abs_keys: Vec<_> = defs
        .abstract_predicate_definitions
        .keys()
        .cloned()
        .collect();
    abs_keys.sort();
    for name in abs_keys {
        let stmt = defs
            .abstract_predicate_definitions
            .get(&name)
            .expect("key present");
        abstracts.push(JsonValue::parse(&store_def_abstract_prop(stmt)?)?);
    }
    let mut structures = Vec::new();
    let mut struct_keys: Vec<_> = defs.structure_definitions.keys().cloned().collect();
    struct_keys.sort();
    for name in struct_keys {
        let stmt = defs.structure_definitions.get(&name).expect("key present");
        structures.push(JsonValue::parse(&store_def_struct(stmt)?)?);
    }
    let mut theorems = Vec::new();
    let mut thm_keys: Vec<_> = defs.theorem_definitions.keys().cloned().collect();
    thm_keys.sort();
    for name in thm_keys {
        let stmt = defs.theorem_definitions.get(&name).expect("key present");
        // Cache only the theorem interface; proof body is not needed to release / by thm.
        let mut for_store = stmt.clone();
        for_store.prove_process.clear();
        theorems.push(JsonValue::parse(&store_def_thm(&for_store)?)?);
    }
    let mut axioms = Vec::new();
    let mut ax_keys: Vec<_> = defs.axiom_definitions.keys().cloned().collect();
    ax_keys.sort();
    for name in ax_keys {
        let stmt = defs.axiom_definitions.get(&name).expect("key present");
        axioms.push(JsonValue::parse(&store_axiom(stmt)?)?);
    }
    Ok(JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("definition_memory".into())),
        ("identifiers".into(), JsonValue::Array(identifiers)),
        ("predicate_definitions".into(), JsonValue::Array(predicates)),
        (
            "abstract_predicate_definitions".into(),
            JsonValue::Array(abstracts),
        ),
        ("structure_definitions".into(), JsonValue::Array(structures)),
        ("theorem_definitions".into(), JsonValue::Array(theorems)),
        ("axiom_definitions".into(), JsonValue::Array(axioms)),
    ]))
}

fn decode_definition_memory(value: &JsonValue) -> Result<DefinitionMemory, KbCodecError> {
    let map = value.as_object()?;
    let kind = JsonValue::get(map, "kind")?.as_str()?;
    if kind != "definition_memory" {
        return Err(KbCodecError::Shape(format!(
            "expected kind `definition_memory`, got `{kind}`"
        )));
    }
    let mut defs = DefinitionMemory::new();
    for item in JsonValue::get(map, "identifiers")?.as_array()? {
        let entry = load_stored_identifier(&item.stringify())?;
        let plain = match &entry {
            crate::exec_env::StoredIdentifierDefinition::LetObj((n, _))
            | crate::exec_env::StoredIdentifierDefinition::HaveObjEqual((n, _))
            | crate::exec_env::StoredIdentifierDefinition::HaveObjInNonemptySetOrParamType((
                n,
                _,
            ))
            | crate::exec_env::StoredIdentifierDefinition::HaveFnEqual((n, _)) => n.clone(),
            other => {
                return Err(KbCodecError::Unsupported(format!(
                    "unexpected identifier after load: {other:?}"
                )));
            }
        };
        defs.identifiers.insert(plain, entry);
    }
    for item in JsonValue::get(map, "predicate_definitions")?.as_array()? {
        let stmt = load_def_prop(&item.stringify())?;
        defs.predicate_definitions.insert(stmt.name.clone(), stmt);
    }
    for item in JsonValue::get(map, "abstract_predicate_definitions")?.as_array()? {
        let stmt = load_def_abstract_prop(&item.stringify())?;
        defs.abstract_predicate_definitions
            .insert(stmt.name.clone(), stmt);
    }
    for item in JsonValue::get(map, "structure_definitions")?.as_array()? {
        let stmt = load_def_struct(&item.stringify())?;
        defs.structure_definitions.insert(stmt.name.clone(), stmt);
    }
    for item in JsonValue::get(map, "theorem_definitions")?.as_array()? {
        let stmt = load_def_thm(&item.stringify())?;
        defs.theorem_definitions.insert(stmt.name.clone(), stmt);
    }
    for item in JsonValue::get(map, "axiom_definitions")?.as_array()? {
        let stmt = load_axiom(&item.stringify())?;
        defs.axiom_definitions.insert(stmt.name.clone(), stmt);
    }
    Ok(defs)
}

fn reject_unsupported_maps(defs: &DefinitionMemory) -> Result<(), KbCodecError> {
    if defs
        .structure_definitions
        .values()
        .any(|definition| !definition.equivalent_facts.is_empty())
    {
        return Err(KbCodecError::Unsupported(
            "struct definition laws require source execution; definitions-only KB does not replay published foralls".into(),
        ));
    }
    if !defs.algorithm_definitions.is_empty() {
        return Err(KbCodecError::Unsupported(
            "algorithm_definitions not in kb definition_memory MVP".into(),
        ));
    }
    if !defs.template_definitions.is_empty() {
        return Err(KbCodecError::Unsupported(
            "template_definitions not in kb definition_memory MVP".into(),
        ));
    }
    if !defs.strategy_definitions.is_empty() {
        return Err(KbCodecError::Unsupported(
            "strategy_definitions not in kb definition_memory MVP".into(),
        ));
    }
    Ok(())
}

/// Helper for tests / callers assembling a memory from known maps.
pub fn definition_memory_from_parts(
    identifiers: HashMap<String, crate::exec_env::StoredIdentifierDefinition>,
    predicates: HashMap<String, crate::ast::stmt::DefPropStmt>,
    abstracts: HashMap<String, crate::ast::stmt::DefAbstractPropStmt>,
    structures: HashMap<String, crate::ast::stmt::DefStructStmt>,
    theorems: HashMap<String, crate::ast::stmt::DefThmStmt>,
    axioms: HashMap<String, crate::ast::stmt::AxiomStmt>,
) -> DefinitionMemory {
    let mut defs = DefinitionMemory::new();
    defs.identifiers = identifiers;
    defs.predicate_definitions = predicates;
    defs.abstract_predicate_definitions = abstracts;
    defs.structure_definitions = structures;
    defs.theorem_definitions = theorems;
    defs.axiom_definitions = axioms;
    defs
}
