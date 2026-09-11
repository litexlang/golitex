use crate::new_pipeline::runtime::{PipelineError, PipelineResult, Runtime};
use crate::new_pipeline::tokenize::Tokenizer;
use std::fs;
use std::path::PathBuf;

use super::command::CliCommand;
use super::{cli_arg_e, cli_arg_f, cli_arg_r};

pub fn run_litex_code(command: CliCommand) -> PipelineResult<()> {
    match command {
        CliCommand::Eval(code) => cli_arg_e::run_cli_arg_e(code),
        CliCommand::File(path) => cli_arg_f::run_cli_arg_f(path),
        CliCommand::Repository(path) => cli_arg_r::run_cli_arg_r(path),
        CliCommand::Help | CliCommand::Version => Err(PipelineError::Invariant(
            "Help/Version are not execution commands".to_string(),
        )),
    }
}

pub struct ModuleExecutionPlan {
    pub import_std: Vec<FileSpec>,
    pub import_repos: Vec<ModuleExecutionPlan>,
    pub exports: Vec<FileSpec>,
}

pub struct FileSpec {
    pub name: String,
    pub path: PathBuf,
    pub trusted: bool,
}

impl ModuleExecutionPlan {
    pub fn single_export(path: impl AsRef<std::path::Path>) -> Self {
        let path = path.as_ref().to_path_buf();
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
            .unwrap_or_else(|| path.to_string_lossy().into_owned());
        Self {
            import_std: Vec::new(),
            import_repos: Vec::new(),
            exports: vec![FileSpec {
                name,
                path,
                trusted: false,
            }],
        }
    }
}

pub fn execute_module_plan_verified(
    runtime: &mut Runtime,
    plan: &ModuleExecutionPlan,
) -> PipelineResult<()> {
    for file in &plan.import_std {
        execute_one_file_verified(runtime, file)?;
    }
    for imported in &plan.import_repos {
        execute_module_plan_verified(runtime, imported)?;
    }
    for file in &plan.exports {
        execute_one_file_verified(runtime, file)?;
    }
    Ok(())
}

pub fn execute_one_file_verified(
    runtime: &mut Runtime,
    file: &FileSpec,
) -> PipelineResult<()> {
    let source = fs::read_to_string(&file.path).map_err(|error| PipelineError::Io {
        path: file.path.clone(),
        message: error.to_string(),
    })?;

    runtime.begin_file(file.path.clone(), file.trusted);
    if let Err(error) = runtime.run_code_verified(&source) {
        runtime.abort_file();
        return Err(error);
    }

    let (path, exec_env) = runtime.finish_file();
    runtime.publish_completed_export_file(path, exec_env);
    Ok(())
}

impl Runtime {
    pub fn run_code_verified(&mut self, code: &str) -> PipelineResult<()> {
        let source_path = self
            .current_file_path()
            .ok_or_else(|| PipelineError::Invariant("no file is active".to_string()))?
            .to_path_buf();
        let token_blocks = Tokenizer::new().tokenize(code, source_path)?;
        let stmts = self.parse(&token_blocks)?;
        for stmt in &stmts {
            self.exec_stmt(stmt)?;
        }
        Ok(())
    }
}
