//! Configuration used when executing Litex source.

use crate::prelude::*;

/// Selects the source entry point used by a Litex command.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LitexExecution {
    /// Run an interactive read-eval-print loop.
    Repl,

    /// Evaluate source supplied directly by the command.
    Eval,

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

/// Configuration required to execute Litex source.
///
/// The source entry point is kept by the command or pipeline entry that owns
/// it. This type contains only execution-wide verification, output, and
/// summary settings, so conversion commands do not need to carry strictness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LitexExecutionOptions {
    /// Verification mode for the current operation.
    ///
    /// This transient mode travels with the execution-wide settings so the
    /// runtime does not keep a second owner for verification state.
    pub trusted_or_require_verify: TrustedOrRequireVerify,

    /// Policy controlling whether configured dependencies must be verified.
    verify_strictness: VerifyStrictnessPolicy,

    /// Detail level used when rendering output.
    output_detail: OutputDetail,

    /// Language used for user-facing output.
    output_language: OutputLanguage,

    /// Whether to append a run summary.
    summary: SummaryOption,
}

impl LitexExecutionOptions {
    /// Construct execution settings for one Litex source operation.
    pub fn new(
        verify_strictness: VerifyStrictnessPolicy,
        output_detail: OutputDetail,
        output_language: OutputLanguage,
        summary: SummaryOption,
    ) -> Self {
        Self {
            trusted_or_require_verify: TrustedOrRequireVerify::RequireVerification,
            verify_strictness,
            output_detail,
            output_language,
            summary,
        }
    }

    /// Construct ordinary, non-strict Litex execution settings.
    pub fn ordinary(
        output_detail: OutputDetail,
        output_language: OutputLanguage,
        summary: SummaryOption,
    ) -> Self {
        Self::new(
            VerifyStrictnessPolicy::Ordinary,
            output_detail,
            output_language,
            summary,
        )
    }

    /// Construct strict Litex execution settings.
    pub fn strict(
        output_detail: OutputDetail,
        output_language: OutputLanguage,
        summary: SummaryOption,
    ) -> Self {
        Self::new(
            VerifyStrictnessPolicy::Strict,
            output_detail,
            output_language,
            summary,
        )
    }

    /// Return the configured dependency-verification policy.
    pub fn verify_strictness(&self) -> VerifyStrictnessPolicy {
        self.verify_strictness
    }

    /// Return whether dependency verification is required for this execution.
    pub fn is_strict(&self) -> bool {
        self.verify_strictness == VerifyStrictnessPolicy::Strict
    }

    /// Return whether the final execution output includes a run summary.
    pub fn should_summarize(&self) -> bool {
        self.summary == SummaryOption::Summarize
    }

    /// Return the output detail level selected for this execution.
    pub fn output_detail(&self) -> OutputDetail {
        self.output_detail
    }

    /// Return the language selected for user-facing execution output.
    pub fn output_language(&self) -> OutputLanguage {
        self.output_language
    }

    /// Replace the output detail level for an already-created execution.
    pub fn set_output_detail(&mut self, output_detail: OutputDetail) {
        self.output_detail = output_detail;
    }

    #[deprecated(note = "use `output_detail`")]
    pub fn output_style(&self) -> OutputDetail {
        self.output_detail()
    }
}

impl Default for LitexExecutionOptions {
    fn default() -> Self {
        Self::ordinary(
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        )
    }
}
