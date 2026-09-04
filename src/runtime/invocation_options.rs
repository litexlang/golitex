//! Invocation configuration shared by the CLI, pipelines, and embedding callers.

use crate::prelude::*;

/// Selects the Litex source entry point for one invocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LitexExecution {
    /// Run an interactive read-eval-print loop.
    Repl,

    /// Evaluate inline source code.
    Inline,

    /// Execute a file using configured project context when available.
    File,

    /// Execute a file without configured project context.
    IsolatedFile,

    /// Execute a repository or module target.
    Repository,

    /// Run a persistent session with configured context when available.
    Session,

    /// Run a persistent session without configured project context.
    IsolatedSession,
}

/// Controls how strictly configured dependencies are verified.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VerifyStrictnessPolicy {
    /// Execute without requiring verification of configured dependencies.
    Ordinary,

    /// Execute while requiring verification of configured dependencies.
    Strict,
}

/// Controls whether a run summary is appended to rendered output.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SummaryOption {
    /// Do not append a run summary to the output.
    None,

    /// Append a run summary to the output.
    Summarize,
}

/// Immutable configuration for one Litex invocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvocationOptions {
    /// Litex source execution entry point.
    execution: LitexExecution,

    /// Policy controlling whether configured dependencies must be verified.
    verify_strictness: VerifyStrictnessPolicy,

    /// Detail level used when rendering output.
    output_detail: OutputDetail,

    /// Language used for user-facing output.
    output_language: OutputLanguage,

    /// Whether to append a run summary.
    summary: SummaryOption,
}

impl InvocationOptions {
    /// Construct a complete invocation configuration in one immutable value.
    pub fn new(
        execution: LitexExecution,
        verify_strictness: VerifyStrictnessPolicy,
        output_detail: OutputDetail,
        output_language: OutputLanguage,
        summary: SummaryOption,
    ) -> Self {
        Self {
            execution,
            verify_strictness,
            output_detail,
            output_language,
            summary,
        }
    }

    /// Construct ordinary, non-strict options for a Litex entry point.
    pub fn execute(execution: LitexExecution) -> Self {
        Self::new(
            execution,
            VerifyStrictnessPolicy::Ordinary,
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        )
    }

    /// Construct strict invocation options for a Litex entry point.
    pub fn strict_execute(execution: LitexExecution) -> Self {
        Self::new(
            execution,
            VerifyStrictnessPolicy::Strict,
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        )
    }

    /// Return the selected Litex source execution entry point.
    pub fn execution(&self) -> LitexExecution {
        self.execution
    }

    /// Return the configured dependency-verification policy.
    pub fn verify_strictness(&self) -> VerifyStrictnessPolicy {
        self.verify_strictness
    }

    /// Return whether dependency verification is required for this invocation.
    pub fn is_strict(&self) -> bool {
        self.verify_strictness == VerifyStrictnessPolicy::Strict
    }

    /// Return whether this invocation must avoid configured project context.
    pub fn is_isolated(&self) -> bool {
        matches!(
            self.execution(),
            LitexExecution::IsolatedFile | LitexExecution::IsolatedSession
        )
    }

    /// Return whether the final output includes a run summary.
    pub fn should_summarize(&self) -> bool {
        self.summary == SummaryOption::Summarize
    }

    pub(crate) fn summary(&self) -> SummaryOption {
        self.summary
    }

    /// Return the output detail level selected for this invocation.
    pub fn output_detail(&self) -> OutputDetail {
        self.output_detail
    }

    /// Return the language selected for user-facing output.
    pub fn output_language(&self) -> OutputLanguage {
        self.output_language
    }

    #[deprecated(note = "use `output_detail`")]
    pub fn output_style(&self) -> OutputDetail {
        self.output_detail()
    }
}

impl Default for InvocationOptions {
    fn default() -> Self {
        Self::execute(LitexExecution::Inline)
    }
}
