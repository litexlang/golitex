pub struct RuntimeContext {
    pub module_manager: ModuleManager,
    pub env_stack: Vec<Env>,
    pub objs: HashMap<String, ()>,
    pub props: HashMap<String, DefPropStmt>,
    pub algos: HashMap<String, DefAlgoStmt>,
    pub set_templates: HashMap<String, DefSetTemplateStmt>,
}