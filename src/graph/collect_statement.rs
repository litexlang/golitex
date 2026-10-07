//! Collapse checked execution into mathematical nodes and dependency groups.
use super::math_graph::{GraphReference, MathGraph};
use super::walk_generated::walk_exec_stmt_result;
use crate::exec_env::ExecEnv;
use crate::execute::ExecStmtResult;
use crate::run::RunLitexCodeResult;
use crate::runtime::Runtime;

impl MathGraph {
    pub fn collect_run(&mut self, run: &RunLitexCodeResult, runtime: &Runtime, source: &str) {
        self.current_source = source.into();
        self.current_statement.clear();
        let file_scope = self.scope(runtime.top_exec_env(), false);
        self.current_owner = file_scope.clone();
        self.register_declarations(runtime.top_exec_env(), runtime, false, true);
        for (index, result) in run.statement_results.iter().enumerate() {
            self.current_statement = run.statement_texts.get(index).cloned().unwrap_or_default();
            self.collect_statement(result, runtime, &[]);
        }
        if let Some(error) = &run.session_error {
            self.diagnostic(error.to_string());
        }
        if !run.success {
            // The runner aborts this entire file. Earlier accepted statements
            // remain an inspectable attempt, but are not project publications.
            for node in &mut self.nodes {
                if node.scope == file_scope {
                    node.published = false;
                }
            }
        }
    }

    pub(super) fn collect_statement(&mut self, result: &ExecStmtResult, runtime: &Runtime, locals: &[&ExecEnv]) {
        if result.is_failed() {
            if locals.is_empty() {
                let message = match result {
                    ExecStmtResult::Fact(crate::execute::execute_fact_stmt::ExecFactStmtResult::Failed(proof)) if proof.is_wd_failed() => "Well-definedness could not be established; no fact was published.",
                    ExecStmtResult::Fact(_) => "The fact was not verified; no fact was published.",
                    _ => "Statement was not accepted; it contributes no mathematical nodes or edges.",
                };
                self.diagnostic(message.into());
            }
            return;
        }
        let saved_origin = self.current_origin.clone();
        let saved_group = self.current_group;
        self.current_group = self.next_group;
        self.next_group += 1;
        self.current_origin = if matches!(result, ExecStmtResult::Trust(_)) {
            "trusted"
        } else if locals.is_empty() {
            "verified"
        } else {
            "local"
        }.into();
        for env in locals {
            self.register_declarations(env, runtime, true, true);
        }
        let mut refs: Vec<GraphReference> = Vec::new();
        let mut outputs = Vec::new();
        walk_exec_stmt_result(result, self, runtime, locals, &mut refs, &mut outputs);
        for output in &outputs {
            for reference in &refs {
                self.edge(&reference.id, output, &reference.kind);
            }
        }
        self.current_origin = saved_origin;
        self.current_group = saved_group;
    }
}
