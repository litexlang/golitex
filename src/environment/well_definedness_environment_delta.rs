use crate::prelude::*;
use crate::verify_rewrite::WellDefinednessId2;
use std::collections::HashMap;

/// Checked environment changes produced while preflighting well-definedness.
///
/// This is deliberately not a queryable `Environment`: callers may only add
/// another checked child environment or install the accumulated changes into
/// a real environment.  Its private fields prevent proof code from treating a
/// partial preflight artifact as the complete mathematical world.
#[derive(Clone)]
pub struct WellDefinednessEnvironmentDelta {
    definitions: DefinitionMemory,
    facts: KnownFactMemory,
    objects: ObjectPropertyMemory,
    predicate_algebraic_properties: PropAlgebraicPropertyMemory,
    inference_cache: KnownFactsCache,
    well_defined_objects: HashMap<ObjString, WellDefinednessId2>,
}

impl WellDefinednessEnvironmentDelta {
    pub fn new() -> Self {
        Self::from_environment(ExecEnv::new_empty_env())
    }

    pub fn merge_committed_environment(
        &mut self,
        checked_environment: ExecEnv,
    ) -> Result<(), RuntimeError> {
        let mut accumulated_environment = self.clone().into_environment();
        accumulated_environment.merge_committed_child(checked_environment)?;
        *self = Self::from_environment(accumulated_environment);
        Ok(())
    }

    pub fn apply_to(&self, environment: &mut ExecEnv) -> Result<(), RuntimeError> {
        environment.merge_committed_child(self.clone().into_environment())
    }

    fn from_environment(environment: ExecEnv) -> Self {
        let ExecEnv {
            definitions,
            facts,
            object_properties: objects,
            prop_algebraic_properties: predicate_algebraic_properties,
            known_facts_cache: inference_cache,
            well_defined_objects,
        } = environment;
        Self {
            definitions,
            facts,
            objects,
            predicate_algebraic_properties,
            inference_cache,
            well_defined_objects,
        }
    }

    fn into_environment(self) -> ExecEnv {
        let Self {
            definitions,
            facts,
            objects,
            predicate_algebraic_properties,
            inference_cache,
            well_defined_objects,
        } = self;
        ExecEnv {
            definitions,
            facts,
            object_properties: objects,
            prop_algebraic_properties: predicate_algebraic_properties,
            known_facts_cache: inference_cache,
            well_defined_objects,
        }
    }
}

impl Default for WellDefinednessEnvironmentDelta {
    fn default() -> Self {
        Self::new()
    }
}
