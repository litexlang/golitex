use super::helper::validate_namespace;
use super::source_position::{SourceOwner, SourcePosition};
use super::LeanCompileError;
use crate::prelude::*;

/// Compile one complete execution result by dispatching its original result enums.
/// Runtime supplies read-only exact citation subjects; source positions enforce
/// producer order and lexical visibility without a compiler-owned proof world.
pub struct LitexToLeanCompiler<'a> {
    pub(super) result: &'a RunLitexCodeResult,
    pub(super) runtime: &'a Runtime,
}

impl<'a> LitexToLeanCompiler<'a> {
    pub fn new(result: &'a RunLitexCodeResult, runtime: &'a Runtime) -> Self {
        Self { result, runtime }
    }

    /// Produce one complete artifact; an error returns no partial Lean output.
    pub fn compile(self, artifact_namespace: &str) -> Result<String, LeanCompileError> {
        let result = self.result;
        let position = SourcePosition {
            parent: None,
            owner: SourceOwner::Run(result),
            before: 0,
        };
        validate_namespace(artifact_namespace)?;
        if !result.success
            || result.session_error.is_some()
            || result
                .statement_results
                .iter()
                .any(ExecStmtResult::is_failed)
        {
            return Err(LeanCompileError::new(
                "source_failed",
                "Only a complete successful source run can be compiled.",
            ));
        }
        let mut declarations = Vec::new();
        for (index, result) in result.statement_results.iter().enumerate() {
            let compiled = self
                .compile_statement(
                    result,
                    &SourcePosition {
                        before: index,
                        ..position
                    },
                    index + 1,
                )
                .map_err(|mut error| {
                    error.statement_index = Some(index + 1);
                    error
                })?;
            declarations.push(compiled);
        }
        let universes = self.source_universes()?;
        Ok(format!("import Litex\n\nnamespace LitexCompiled.{artifact_namespace}\n\nuniverse {universes}\nvariable {{M : Litex.Semantics.{{u}}}}\n\n{}\nend LitexCompiled.{artifact_namespace}\n", declarations.join("\n\n")))
    }
}
