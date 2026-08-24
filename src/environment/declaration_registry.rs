use crate::prelude::*;
use std::collections::HashMap;

/// Declarations that introduce reusable names in one Environment.
#[derive(Clone)]
pub struct EnvironmentDeclarationRegistry {
    pub symbols: SymbolTable,
    pub defined_identifiers: HashMap<IdentifierName, ParamObjType>,
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
            defined_identifiers: HashMap::new(),
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
}
