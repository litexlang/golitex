use crate::prelude::*;
use std::cell::RefCell;

thread_local! {
    static ACTIVE_PIPELINE_STEPS: RefCell<Option<Vec<PipelineStep>>> = const { RefCell::new(None) };
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PipelineStep {
    pub stage: String,
    pub function: String,
    pub source_file: String,
}

impl PipelineStep {
    pub fn new(stage: &str, function: &str, source_file: &str) -> Self {
        Self {
            stage: stage.to_string(),
            function: function.to_string(),
            source_file: source_file.to_string(),
        }
    }

    fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            (
                "stage".to_string(),
                JsonValue::JsonString(self.stage.clone()),
            ),
            (
                "function".to_string(),
                JsonValue::JsonString(self.function.clone()),
            ),
            (
                "source_file".to_string(),
                JsonValue::JsonString(self.source_file.clone()),
            ),
        ])
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PipelineTrace {
    pub steps: Vec<PipelineStep>,
    pub lean_compiler_executed: bool,
}

impl PipelineTrace {
    pub fn new(steps: Vec<PipelineStep>, lean_compiler_executed: bool) -> Self {
        Self {
            steps,
            lean_compiler_executed,
        }
    }

    pub fn prepend_cli_entry(&mut self) {
        let mut entry = vec![
            PipelineStep::new("main", "main", "src/main.rs"),
            PipelineStep::new("cli", "cli::run_cli", "src/cli/command_dispatch.rs"),
        ];
        entry.append(&mut self.steps);
        self.steps = entry;
    }

    pub fn prepend_step(&mut self, step: PipelineStep) {
        if self
            .steps
            .iter()
            .any(|existing| existing.function == step.function)
        {
            return;
        }
        self.steps.insert(0, step);
    }

    pub fn text(&self) -> String {
        let mut output = String::from("Rust pipeline trace:\n");
        for (index, step) in self.steps.iter().enumerate() {
            output.push_str(
                format!("{}. {} — {}\n", index + 1, step.function, step.source_file).as_str(),
            );
        }
        output.push_str(if self.lean_compiler_executed {
            "Lean compiler: executed"
        } else {
            "Lean compiler: not executed"
        });
        output
    }

    pub fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            (
                "steps".to_string(),
                JsonValue::Array(self.steps.iter().map(PipelineStep::json_value).collect()),
            ),
            (
                "lean_compiler_executed".to_string(),
                JsonValue::Bool(self.lean_compiler_executed),
            ),
        ])
    }
}

pub struct PipelineTraceCapture {
    enabled: bool,
}

impl PipelineTraceCapture {
    pub fn new(enabled: bool) -> Self {
        if enabled {
            ACTIVE_PIPELINE_STEPS.with(|active| {
                *active.borrow_mut() = Some(Vec::new());
            });
        }
        Self { enabled }
    }

    pub fn finish(self, lean_compiler_executed: bool) -> PipelineTrace {
        if !self.enabled {
            return PipelineTrace::default();
        }
        let steps =
            ACTIVE_PIPELINE_STEPS.with(|active| active.borrow_mut().take().unwrap_or_default());
        PipelineTrace::new(steps, lean_compiler_executed)
    }
}

pub fn record_pipeline_step(stage: &str, function: &str, source_file: &str) {
    ACTIVE_PIPELINE_STEPS.with(|active| {
        let mut active = active.borrow_mut();
        let Some(steps) = active.as_mut() else {
            return;
        };
        if steps.iter().any(|step| step.function == function) {
            return;
        }
        steps.push(PipelineStep::new(stage, function, source_file));
    });
}
