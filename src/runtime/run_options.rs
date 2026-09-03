use crate::prelude::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionOption {
    Repl,
    Eval,
    File,
    IsolatedFile,
    Repo,
    Session,
    IsolatedSession,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RunOption {
    Execute(ExecutionOption),
    StrictExecute(ExecutionOption),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SummaryOption {
    None,
    Summarize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunOptions {
    run: RunOption,
    output_detail: OutputDetail,
    output_language: OutputLanguage,
    summary: SummaryOption,
}

impl RunOptions {
    /// Construct a complete run configuration in one immutable value.
    pub fn new(
        run: RunOption,
        output_detail: OutputDetail,
        output_language: OutputLanguage,
        summary: SummaryOption,
    ) -> Self {
        Self {
            run,
            output_detail,
            output_language,
            summary,
        }
    }

    pub fn execute(execution: ExecutionOption) -> Self {
        Self::new(
            RunOption::Execute(execution),
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        )
    }

    pub fn strict_execute(execution: ExecutionOption) -> Self {
        Self::new(
            RunOption::StrictExecute(execution),
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        )
    }

    pub fn run(&self) -> RunOption {
        self.run
    }

    pub fn execution(&self) -> ExecutionOption {
        match self.run {
            RunOption::Execute(execution) | RunOption::StrictExecute(execution) => execution,
        }
    }

    pub fn is_strict(&self) -> bool {
        matches!(self.run, RunOption::StrictExecute(_))
    }

    pub fn is_isolated(&self) -> bool {
        matches!(
            self.execution(),
            ExecutionOption::IsolatedFile | ExecutionOption::IsolatedSession
        )
    }

    pub fn should_summarize(&self) -> bool {
        self.summary == SummaryOption::Summarize
    }

    pub(crate) fn summary(&self) -> SummaryOption {
        self.summary
    }

    pub fn output_detail(&self) -> OutputDetail {
        self.output_detail
    }

    pub fn output_language(&self) -> OutputLanguage {
        self.output_language
    }

    #[deprecated(note = "use `output_detail`")]
    pub fn output_style(&self) -> OutputDetail {
        self.output_detail()
    }
}

impl Default for RunOptions {
    fn default() -> Self {
        Self::execute(ExecutionOption::Eval)
    }
}
