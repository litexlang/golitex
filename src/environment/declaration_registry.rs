use crate::prelude::*;
use std::collections::HashMap;

/// Declarations that introduce reusable names in one Environment.
#[derive(Clone)]
pub struct EnvironmentDeclarationRegistry {
    pub symbols: SymbolTable,
    pub defined_def_props: HashMap<PropName, DefPropStmt>,
    pub defined_abstract_props: HashMap<AbstractPropName, DefAbstractPropStmt>,
    pub defined_algorithms: HashMap<AlgoName, DefAlgoStmt>,
    pub defined_structs: HashMap<StructName, DefStructStmt>,
    pub defined_templates: HashMap<TemplateName, DefTemplateStmt>,
    pub defined_settings: HashMap<String, DefSettingStmt>,
    pub defined_thm_stmts: HashMap<ThmName, DefThmStmt>,
    pub defined_axiom_stmts: HashMap<ThmName, AxiomStmt>,
    pub defined_strategy_stmts: HashMap<StrategyName, DefStrategyStmt>,
}

impl EnvironmentDeclarationRegistry {
    pub fn new() -> Self {
        Self {
            symbols: SymbolTable::new(),
            defined_def_props: HashMap::new(),
            defined_abstract_props: HashMap::new(),
            defined_algorithms: HashMap::new(),
            defined_structs: HashMap::new(),
            defined_templates: HashMap::new(),
            defined_settings: HashMap::new(),
            defined_thm_stmts: HashMap::new(),
            defined_axiom_stmts: HashMap::new(),
            defined_strategy_stmts: HashMap::new(),
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
