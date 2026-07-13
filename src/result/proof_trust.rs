use crate::prelude::*;

#[derive(Clone, Debug, Default)]
pub struct ProofTrustSummary {
    pub dependencies: Vec<ProofTrustDependency>,
}

#[derive(Clone, Debug)]
pub struct ProofTrustDependency {
    pub kind: String,
    pub name: Option<String>,
    pub line_file: LineFile,
}

impl ProofTrustSummary {
    pub fn new() -> Self {
        Self {
            dependencies: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.dependencies.is_empty()
    }

    pub fn from_dependency(
        kind: impl Into<String>,
        name: Option<String>,
        line_file: LineFile,
    ) -> Self {
        let mut summary = Self::new();
        summary.add_dependency(kind, name, line_file);
        summary
    }

    pub fn from_store_reason(reason: &str, line_file: LineFile) -> Self {
        if reason == TrustStmt::store_reason() {
            return Self::from_dependency("trust", None, line_file);
        }
        if reason == TrustHaveStmt::store_reason() {
            return Self::from_dependency("trust_have", None, line_file);
        }
        if reason == DefThmStmt::axiom_store_reason() {
            return Self::from_dependency("axiom", None, line_file);
        }
        Self::new()
    }

    pub fn add_dependency(
        &mut self,
        kind: impl Into<String>,
        name: Option<String>,
        line_file: LineFile,
    ) {
        let dependency = ProofTrustDependency {
            kind: kind.into(),
            name,
            line_file,
        };
        if self
            .dependencies
            .iter()
            .any(|existing| existing.same_dependency(&dependency))
        {
            return;
        }
        self.dependencies.push(dependency);
    }

    pub fn merge(&mut self, other: &ProofTrustSummary) {
        for dependency in other.dependencies.iter() {
            self.add_dependency(
                dependency.kind.clone(),
                dependency.name.clone(),
                dependency.line_file.clone(),
            );
        }
    }

    pub fn reason_with_base(&self, base: &str) -> String {
        if self.is_empty() {
            return base.to_string();
        }
        format!(
            "{}, depends_on_unproved_assumptions: {}",
            base,
            self.dependencies_text()
        )
    }

    fn dependencies_text(&self) -> String {
        self.dependencies
            .iter()
            .map(|dependency| dependency.to_reason_text())
            .collect::<Vec<_>>()
            .join("; ")
    }
}

impl ProofTrustDependency {
    fn same_dependency(&self, other: &ProofTrustDependency) -> bool {
        self.kind == other.kind && self.name == other.name && self.line_file == other.line_file
    }

    fn to_reason_text(&self) -> String {
        let mut text = self.kind.clone();
        if let Some(name) = self.name.as_ref() {
            text.push(' ');
            text.push_str(name);
        }
        if self.line_file != default_line_file() {
            text.push_str(" at line ");
            text.push_str(&self.line_file.0.to_string());
        }
        text
    }
}
