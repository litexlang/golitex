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
    pub fn execute(execution: ExecutionOption) -> Self {
        Self::new(RunOption::Execute(execution))
    }

    pub fn strict_execute(execution: ExecutionOption) -> Self {
        Self::new(RunOption::StrictExecute(execution))
    }

    fn new(run: RunOption) -> Self {
        Self {
            run,
            output_detail: OutputDetail::Normal,
            output_language: OutputLanguage::English,
            summary: SummaryOption::None,
        }
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

    pub fn output_detail(&self) -> OutputDetail {
        self.output_detail
    }

    pub fn output_language(&self) -> OutputLanguage {
        self.output_language
    }

    pub fn with_output_detail(mut self, output_detail: OutputDetail) -> Self {
        self.output_detail = output_detail;
        self
    }

    #[deprecated(note = "use `output_detail`")]
    pub fn output_style(&self) -> OutputDetail {
        self.output_detail()
    }

    #[deprecated(note = "use `with_output_detail`")]
    pub fn with_output_style(self, output_detail: OutputDetail) -> Self {
        self.with_output_detail(output_detail)
    }

    pub fn with_output_language(mut self, output_language: OutputLanguage) -> Self {
        self.output_language = output_language;
        self
    }

    pub fn with_summary(mut self, summary: SummaryOption) -> Self {
        self.summary = summary;
        self
    }

    pub fn with_execution(mut self, execution: ExecutionOption) -> Self {
        self.run = match self.run {
            RunOption::Execute(_) => RunOption::Execute(execution),
            RunOption::StrictExecute(_) => RunOption::StrictExecute(execution),
        };
        self
    }
}

impl Default for RunOptions {
    fn default() -> Self {
        Self::execute(ExecutionOption::Eval)
    }
}
