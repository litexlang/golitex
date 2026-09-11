use super::runtime_ids::{AtomId, Id};

pub type AtomString = String;

pub struct Runtime {
    // 用户在命令行中开启litex时输入的cli指令的那些命令的要求会保留在这里
    pub runtime_options: RuntimeOptions,

    // 在 -r 的时候会默认import来的文件都是trusted的
    pub is_current_file_trusted: bool,

    pub next_fact_id: Id,
    pub next_well_defined_object_id: Id,
    pub next_symbol_id: Id,
    pub next_prop_algebraic_property_id: Id,

    pub current_module_id: Id,
    pub current_source_id: Id,
    pub module_manager: Box<ModuleManager>,

    // 在 exec stmt 的时候所有的事情发生在这里
    // 执行 scope 的栈；只有进入真正的执行 scope 时才 push child ExecEnv。
    // child env 退出时永不 merge 回 parent，必要时由 Result 持有它。
    pub execution_environments_stack: Vec<Box<ExecEnv>>,

    // 解析 scope 的栈，与 execution_environments_stack 完全独立。
    // 解析 forall/exist 或 fn 参数可以创建 ParseScope，但不因此创建 ExecEnv。
    pub parse_scope_stack: Vec<Box<ParseScope>>,
}

pub struct ParseScope {
    pub symbol_to_atom_id: HashMap<AtomString, AtomId>,
    pub atom_id_to_atom: HashMap<AtomId, Atom>,
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
