//! One-pass resolution of executed transparent object definitions.

use crate::prelude::*;
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug)]
pub struct TransparentObjectDefinitionUse {
    pub symbol: SymbolRef,
    pub definition: TransparentObjectDefinition,
}

pub struct TransparentObjectSubstitutionPass {
    substitutions: HashMap<String, Obj>,
    definitions: Vec<TransparentObjectDefinitionUse>,
}

impl TransparentObjectSubstitutionPass {
    pub fn substitutions(&self) -> &HashMap<String, Obj> {
        &self.substitutions
    }

    pub fn definitions(&self) -> &[TransparentObjectDefinitionUse] {
        &self.definitions
    }

    pub fn changed(&self) -> bool {
        !self.definitions.is_empty()
    }
}

impl Runtime {
    fn visible_transparent_object_definitions(
        &self,
    ) -> Result<BTreeMap<SymbolId, TransparentObjectDefinitionUse>, RuntimeError> {
        let mut definitions = BTreeMap::new();
        for environment in self.iter_environments_from_top() {
            collect_transparent_object_definitions(environment, &mut definitions)?;
        }
        for module in self.module_manager.modules.values() {
            collect_transparent_object_definitions(&module.main_environment, &mut definitions)?;
            for source in &module.sources {
                let is_current_source =
                    self.current_module_id == module.id && self.current_source_id == source.id;
                if source.real_file_path().is_none() && !is_current_source {
                    continue;
                }
                collect_transparent_object_definitions(&source.environment, &mut definitions)?;
            }
        }
        Ok(definitions)
    }

    /// Select exactly the transparent symbols occurring in `objects`.
    ///
    /// Each candidate is tested against the original objects, and the final
    /// substitution map is applied only once by the caller. Consequently a
    /// definition inserted by this pass is never rescanned for another alias.
    pub fn transparent_object_substitutions_once<'a>(
        &self,
        objects: impl IntoIterator<Item = &'a Obj>,
    ) -> Result<TransparentObjectSubstitutionPass, RuntimeError> {
        let objects = objects.into_iter().collect::<Vec<_>>();
        let mut substitutions = HashMap::new();
        let mut used_definitions = Vec::new();
        for (symbol_id, definition_use) in self.visible_transparent_object_definitions()? {
            let key = symbol_id.substitution_key();
            let singleton =
                HashMap::from([(key.clone(), definition_use.definition.value().clone())]);
            let occurs = objects.iter().try_fold(false, |already_occurs, object| {
                if already_occurs {
                    return Ok(true);
                }
                let replaced = self.inst_obj(object, &singleton, SubstitutionMode::Exact)?;
                Ok::<bool, RuntimeError>(obj_equality_key(object) != obj_equality_key(&replaced))
            })?;
            if occurs {
                substitutions.insert(key, definition_use.definition.value().clone());
                used_definitions.push(definition_use);
            }
        }
        Ok(TransparentObjectSubstitutionPass {
            substitutions,
            definitions: used_definitions,
        })
    }

    pub fn resolve_transparent_obj_once(
        &self,
        object: &Obj,
    ) -> Result<(Obj, Vec<TransparentObjectDefinitionUse>), RuntimeError> {
        let pass = self.transparent_object_substitutions_once(std::iter::once(object))?;
        if !pass.changed() {
            return Ok((object.clone(), Vec::new()));
        }
        let resolved = self.inst_obj(
            object,
            pass.substitutions(),
            SubstitutionMode::TransparentDefinition,
        )?;
        Ok((resolved, pass.definitions))
    }
}

fn collect_transparent_object_definitions(
    environment: &Environment,
    definitions: &mut BTreeMap<SymbolId, TransparentObjectDefinitionUse>,
) -> Result<(), RuntimeError> {
    for (_, symbol_definition) in environment.definitions.symbols.iter() {
        let Some(transparent_definition) = symbol_definition.transparent_object_definition() else {
            continue;
        };
        let symbol_id = symbol_definition.binding().id();
        let candidate = TransparentObjectDefinitionUse {
            symbol: symbol_definition.binding().as_ref(),
            definition: transparent_definition.clone(),
        };
        if let Some(existing) = definitions.get(&symbol_id) {
            if !existing
                .definition
                .is_same_definition_as(&candidate.definition)
            {
                return Err(
                    UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                        "conflicting transparent definitions for symbol ID {}",
                        symbol_id.value()
                    )))
                    .into(),
                );
            }
            continue;
        }
        definitions.insert(symbol_id, candidate);
    }
    Ok(())
}
