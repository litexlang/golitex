use crate::prelude::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnvironmentStrategyActivationState {
    Active,
    Stopped,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnvironmentStrategySelection {
    pub strategy_name: StrategyName,
    pub activation_state: EnvironmentStrategyActivationState,
}

/// Strategy selections controlling proof search for atomic fact families.
#[derive(Clone)]
pub struct EnvironmentStrategyRegistry {
    pub strategies_by_atomic_fact_family: HashMap<(PropName, bool), EnvironmentStrategySelection>,
}

impl EnvironmentStrategyRegistry {
    pub fn new() -> Self {
        Self {
            strategies_by_atomic_fact_family: HashMap::new(),
        }
    }

    pub fn activate(&mut self, key: (PropName, bool), strategy_name: StrategyName) {
        self.strategies_by_atomic_fact_family.insert(
            key,
            EnvironmentStrategySelection {
                strategy_name,
                activation_state: EnvironmentStrategyActivationState::Active,
            },
        );
    }

    pub fn stop(&mut self, key: (PropName, bool), strategy_name: StrategyName) {
        self.strategies_by_atomic_fact_family.insert(
            key,
            EnvironmentStrategySelection {
                strategy_name,
                activation_state: EnvironmentStrategyActivationState::Stopped,
            },
        );
    }

    pub fn active_strategy(&self, key: &(PropName, bool)) -> Option<&StrategyName> {
        self.strategies_by_atomic_fact_family
            .get(key)
            .filter(|selection| {
                selection.activation_state == EnvironmentStrategyActivationState::Active
            })
            .map(|selection| &selection.strategy_name)
    }

    pub fn stopped_strategy(&self, key: &(PropName, bool)) -> Option<&StrategyName> {
        self.strategies_by_atomic_fact_family
            .get(key)
            .filter(|selection| {
                selection.activation_state == EnvironmentStrategyActivationState::Stopped
            })
            .map(|selection| &selection.strategy_name)
    }

    pub fn used_strategy_count(&self) -> usize {
        self.strategies_by_atomic_fact_family.len()
    }

    pub fn stopped_strategy_count(&self) -> usize {
        self.strategies_by_atomic_fact_family
            .values()
            .filter(|selection| {
                selection.activation_state == EnvironmentStrategyActivationState::Stopped
            })
            .count()
    }

    pub fn merge_from(&mut self, child: Self) {
        self.strategies_by_atomic_fact_family
            .extend(child.strategies_by_atomic_fact_family);
    }
}
