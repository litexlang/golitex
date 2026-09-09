pub type Id = u64;
pub type AtomString = String;

pub struct Runtime {
    // 用户在命令行中开启litex时输入的cli指令的那些命令的要求会保留在这里
    pub runtime_options: RuntimeOptions,

    pub next_fact_id: Id,
    pub next_well_defined_object_id: Id,
    pub next_symbol_id: Id,
    pub next_prop_algebraic_property_id: Id,

    pub current_module_id: Id,
    pub current_source_id: Id,
    pub module_manager: Box<ModuleManager>,

    pub is_current_file_trusted: bool,

    pub execution_environments_stack: Vec<Box<ExecEnv>>,

    pub parse_context: Vec<Box<ParseEnv>>,
}

pub struct ParseEnv {
    pub symbol_to_symbol_is_map: HashMap<AtomString, Id>,
    pub symbol_id_to_symbol_map: HashMap<Id, Atom>,
}

pub struct RuntimeOptions {
    /// Policy controlling whether configured dependencies must be verified.
    verify_strictness: VerifyStrictnessPolicy,

    /// Detail level used when rendering output.
    output_detail: OutputDetail,

    /// Language used for user-facing output.
    output_language: OutputLanguage,

    /// Whether to append a run summary.
    summary: SummaryOption,
}
