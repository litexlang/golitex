use super::definition_graph::{
    definition_graph_file_target, definition_graph_target_error_output,
    render_definition_graph_result,
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
    let target_label = match outcome.target_kind {
        RunTargetKind::Code => format!("{} -e", kind.flag()),
        RunTargetKind::File | RunTargetKind::Repository => outcome
            .target_path
            .clone()
            .expect("file and repository outcomes must retain their target path"),
        RunTargetKind::Session => unreachable!("pipeline runs do not produce session targets"),
    };
    if let Some(message) = outcome.target_error {
        return match kind {
            GraphKind::Result => graph_target_error_output(
                outcome.target_kind,
                target_label.as_str(),
                hide_file_paths,
                message,
            ),
            GraphKind::Fact => fact_graph_target_error_output(
                outcome.target_kind,
                target_label.as_str(),
                hide_file_paths,
                message,
            ),
            GraphKind::Definition => definition_graph_target_error_output(
                outcome.target_kind,
                target_label.as_str(),
                hide_file_paths,
                message,
            ),
        };
    }

    match kind {
        GraphKind::Result => render_graph_from_stmt_results(
            outcome.target_kind,
            target_label.as_str(),
            hide_file_paths,
            &outcome.runtime,
            outcome.stmt_results.as_slice(),
            outcome.runtime_error.as_ref(),
        ),
        GraphKind::Fact => render_fact_graph_from_stmt_results(
            outcome.target_kind,
            target_label.as_str(),
            hide_file_paths,
            &outcome.runtime,
            outcome.stmt_results.as_slice(),
            outcome.runtime_error.as_ref(),
        ),
        GraphKind::Definition => {
            let selected_target = if outcome.target_kind == RunTargetKind::File {
                definition_graph_file_target(
                    &outcome.runtime,
                    outcome
                        .target_path
                        .as_deref()
                        .expect("file outcomes must retain their target path"),
                )
            } else {
                outcome.selected_repository_target
            };
            render_definition_graph_result(
                outcome.target_kind,
                target_label.as_str(),
                hide_file_paths,
                &mut outcome.runtime,
                outcome.stmt_results.as_slice(),
                outcome.runtime_error.as_ref(),
                selected_target,
            )
        }
    }
}
