pub struct ModuleManager {
    hierarchy: ModuleHierarchy,
    export_files_and_their_env: Vec<ExportFileAndItsExecEnv>,
    import_repos: Vec<ModuleManager>,
    import_std: Vec<ImportStdRepoAndItsExecEnv>,
}

pub enum ModuleHierarchy {
    Module,
    Submodule,
}

pub struct ExportFileAndItsExecEnv {
    name: String,
    Path: Path,
    exec_env: ExecEnv,
}

pub struct ImportStdRepoAndItsExecEnv {
    name: String,
    exec_env: ExecEnv,
}
