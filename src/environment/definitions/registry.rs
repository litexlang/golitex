//! Definitions that introduce reusable names.

use crate::prelude::*;
use std::collections::HashMap;

/// Definitions that introduce reusable names in one Environment.
#[derive(Clone)]
pub struct EnvironmentDefinitionRegistry {
    pub symbols: SymbolTable,
    pub predicate_definitions: HashMap<PropName, DefPropStmt>,
    pub abstract_predicate_definitions: HashMap<AbstractPropName, DefAbstractPropStmt>,
    pub algorithm_definitions: HashMap<AlgoName, DefAlgoStmt>,
    pub structure_definitions: HashMap<StructName, DefStructStmt>,
    pub template_definitions: HashMap<TemplateName, DefTemplateStmt>,
    pub setting_definitions: HashMap<String, DefSettingStmt>,
    pub theorem_definitions: HashMap<ThmName, DefThmStmt>,
    pub axiom_definitions: HashMap<ThmName, AxiomStmt>,
    pub strategy_definitions: HashMap<StrategyName, DefStrategyStmt>,
}

impl EnvironmentDefinitionRegistry {
    pub fn new() -> Self {
        Self {
            symbols: SymbolTable::new(),
            predicate_definitions: HashMap::new(),
            abstract_predicate_definitions: HashMap::new(),
            algorithm_definitions: HashMap::new(),
            structure_definitions: HashMap::new(),
            template_definitions: HashMap::new(),
            setting_definitions: HashMap::new(),
            theorem_definitions: HashMap::new(),
            axiom_definitions: HashMap::new(),
            strategy_definitions: HashMap::new(),
        }
    }

    pub fn object_symbol(&self, name: &str) -> Option<&SymbolDefinition> {
        self.symbols
            .get(name)
            .filter(|definition| definition.role().is_object_symbol())
    }

    pub fn object_symbols(&self) -> impl Iterator<Item = (&String, &SymbolDefinition)> {
        self.symbols
            .iter()
            .filter(|(_, definition)| definition.role().is_object_symbol())
    }

    pub fn object_symbol_count(&self) -> usize {
        self.object_symbols().count()
    }
}
