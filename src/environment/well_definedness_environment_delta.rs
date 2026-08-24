use crate::prelude::*;

/// Checked environment changes produced while preflighting well-definedness.
///
/// This is deliberately not a queryable `Environment`: callers may only add
/// another checked child environment or install the accumulated changes into
/// a real environment.  Its private fields prevent proof code from treating a
/// partial preflight artifact as the complete mathematical world.
#[derive(Clone)]
pub struct WellDefinednessEnvironmentDelta {
    declarations: EnvironmentDeclarationRegistry,
    facts: EnvironmentFactDatabase,
    objects: EnvironmentObjectKnowledgeStore,
    predicate_properties: EnvironmentPredicatePropertyStore,
    caches: EnvironmentVerificationCache,
    strategies: EnvironmentStrategyRegistry,
}

impl WellDefinednessEnvironmentDelta {
    pub fn new() -> Self {
        Self::from_environment(Environment::new_empty_env())
    }

    pub fn merge_committed_environment(
        &mut self,
        checked_environment: Environment,
    ) -> Result<(), RuntimeError> {
        let mut accumulated_environment = self.clone().into_environment();
        accumulated_environment.merge_committed_child(checked_environment)?;
        *self = Self::from_environment(accumulated_environment);
        Ok(())
    }

    pub fn apply_to(&self, environment: &mut Environment) -> Result<(), RuntimeError> {
        environment.merge_committed_child(self.clone().into_environment())
    }

    fn from_environment(environment: Environment) -> Self {
        let Environment {
            declarations,
            facts,
            objects,
            predicate_properties,
            caches,
            strategies,
        } = environment;
        Self {
            declarations,
            facts,
            objects,
            predicate_properties,
            caches,
            strategies,
        }
    }

    fn into_environment(self) -> Environment {
        let Self {
            declarations,
            facts,
            objects,
            predicate_properties,
            caches,
            strategies,
        } = self;
        Environment {
            declarations,
            facts,
            objects,
            predicate_properties,
            caches,
            strategies,
        }
    }
}

impl Default for WellDefinednessEnvironmentDelta {
    fn default() -> Self {
        Self::new()
    }
}
