use super::definition_graph::{
    definition_graph_file_target, definition_graph_repository_target,
    definition_graph_target_error_output, render_definition_graph_result,
};
use super::fact_graph::{fact_graph_target_error_output, render_fact_graph_from_stmt_results};
use super::result_graph_execution::{graph_target_error_output, render_graph_from_stmt_results};
use crate::prelude::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GraphKind {
    Result,
    Fact,
    Definition,
}

impl GraphKind {
    pub fn flag(self) -> &'static str {
        match self {
            Self::Result => "-graph",
            Self::Fact => "-factgraph",
            Self::Definition => "-defgraph",
        }
    }

    pub fn output_name(self) -> &'static str {
        match self {
            Self::Result => "graph",
            Self::Fact => "fact graph",
            Self::Definition => "definition graph",
        }
    }
}

pub fn render_graph(
    kind: GraphKind,
    mut outcome: RunOutcome,
    hide_file_paths: bool,
) -> (bool, String) {
    let target_kind = outcome.target.kind();
    let target_path = outcome.target.path().map(str::to_string);
    if let Some(message) = outcome.target_error {
        return match kind {
            GraphKind::Result => graph_target_error_output(
                target_kind,
                target_path.as_deref(),
                hide_file_paths,
                message,
            ),
            GraphKind::Fact => fact_graph_target_error_output(
                target_kind,
                target_path.as_deref(),
                hide_file_paths,
                message,
            ),
            GraphKind::Definition => definition_graph_target_error_output(
                target_kind,
                target_path.as_deref(),
                hide_file_paths,
                message,
            ),
        };
    }

    match kind {
        GraphKind::Result => render_graph_from_stmt_results(
            target_kind,
            target_path.as_deref(),
            hide_file_paths,
            &outcome.runtime,
            outcome.stmt_results.as_slice(),
            outcome.runtime_error.as_ref(),
        ),
        GraphKind::Fact => render_fact_graph_from_stmt_results(
            target_kind,
            target_path.as_deref(),
            hide_file_paths,
            &outcome.runtime,
            outcome.stmt_results.as_slice(),
            outcome.runtime_error.as_ref(),
        ),
        GraphKind::Definition => {
            let selected_target = match &outcome.target {
                RunTarget::Eval => None,
                RunTarget::File { path, .. } => definition_graph_file_target(
                    &outcome.runtime,
                    path,
                ),
                RunTarget::Repository { path } => {
                    definition_graph_repository_target(&outcome.runtime, path)
                }
            };
            render_definition_graph_result(
                target_kind,
                target_path.as_deref(),
                hide_file_paths,
                &mut outcome.runtime,
                outcome.stmt_results.as_slice(),
                outcome.runtime_error.as_ref(),
                selected_target,
            )
        }
    }
}
