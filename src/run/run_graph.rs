//! Graph output is selected outside Runtime's unchanged launch/state contract.
use crate::graph::MathGraph;
use crate::launch_command::{parse_launch_command, LaunchCommand};
use crate::runtime::{RuntimeError, RuntimeResult};

pub struct GraphCommandResult {
    pub success: bool,
    pub json: String,
}

impl GraphCommandResult {
    pub fn new(success: bool, json: String) -> Self {
        Self { success, json }
    }
}

pub fn parse_graph_command(args: &[String]) -> RuntimeResult<Option<LaunchCommand>> {
    let mut ordinary = Vec::new();
    let mut graph = false;
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        if arg == "-graph" || arg == "--graph" {
            if graph {
                return Err(RuntimeError::InvalidArguments("`-graph` may appear only once".into()));
            }
            graph = true;
            index += 1;
            continue;
        }
        ordinary.push(arg.clone());
        index += 1;
        // Operand ownership matches the existing parser. A source/path named
        // -graph is an operand, never an output request.
        let operand = matches!(arg.as_str(), "-e" | "-f" | "-r" | "-lang" | "--lang")
            || (matches!(arg.as_str(), "-extractpython" | "-extractc") && !matches!(args.get(index).map(String::as_str), Some("-f" | "-r")));
        if operand && index < args.len() {
            ordinary.push(args[index].clone());
            index += 1;
        }
    }
    if !graph { return Ok(None); }
    let command = parse_launch_command(&ordinary)?;
    match &command {
        LaunchCommand::Eval { session: false, .. }
        | LaunchCommand::File { session: false, .. }
        | LaunchCommand::Repository { session: false, .. } => Ok(Some(command)),
        _ => Err(RuntimeError::InvalidArguments("`-graph` requires -e, -f or -r and does not take -session, -latex or executable extraction".into())),
    }
}

pub fn run_graph_command(command: LaunchCommand) -> RuntimeResult<GraphCommandResult> {
    let (target, path) = match &command {
        LaunchCommand::Eval { session: false, .. } => ("eval", None),
        LaunchCommand::File { path, session: false, .. } => ("file", Some(path.display().to_string())),
        LaunchCommand::Repository { path, session: false, .. } => ("repo", Some(path.display().to_string())),
        _ => return Err(RuntimeError::InvalidArguments("graph output requires a batch mathematical run".into())),
    };
    let mut graph = MathGraph::new(command.output_language());
    let success = match command {
        command @ LaunchCommand::Eval { .. } => super::run_eval::run_eval_with_graph(command, Some(&mut graph)).map(|run| { if let Some(error) = &run.run.session_error { graph.diagnostic(error.to_string()); } run.run.success }),
        command @ LaunchCommand::File { .. } => crate::run_module::run_file_with_config_with_graph(command, Some(&mut graph)).map(|run| { if let Some(error) = &run.run.session_error { graph.diagnostic(error.to_string()); } run.run.success }),
        command @ LaunchCommand::Repository { .. } => crate::run_module::run_project_with_graph(command, Some(&mut graph)).map(|run| { if let Some(error) = &run.run.session_error { graph.diagnostic(error.to_string()); } run.run.success }),
        _ => unreachable!(),
    };
    let success = match success {
        Ok(success) => success,
        Err(error) => { graph.diagnostic(error.to_string()); false }
    };
    if !success { graph.diagnostic("The requested batch did not complete successfully.".into()); }
    Ok(GraphCommandResult::new(success, graph.json(success, target, path.as_deref())))
}
