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
    pub boundary: Option<usize>,
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

    pub fn contains_kind(&self, kind: &str) -> bool {
        self.dependencies
            .iter()
            .any(|dependency| dependency.kind == kind)
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

    pub fn cli_trusted_prefix(line_file: LineFile, boundary: usize) -> Self {
        let mut summary = Self::new();
        summary.add_dependency_with_boundary("cli_trusted_prefix", None, line_file, Some(boundary));
        summary
    }

    pub fn add_dependency(
        &mut self,
        kind: impl Into<String>,
        name: Option<String>,
        line_file: LineFile,
    ) {
        self.add_dependency_with_boundary(kind, name, line_file, None);
    }

    pub fn add_dependency_with_boundary(
        &mut self,
        kind: impl Into<String>,
        name: Option<String>,
        line_file: LineFile,
        boundary: Option<usize>,
    ) {
        let dependency = ProofTrustDependency {
            kind: kind.into(),
            name,
            line_file,
            boundary,
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
            self.add_dependency_with_boundary(
                dependency.kind.clone(),
                dependency.name.clone(),
                dependency.line_file.clone(),
                dependency.boundary,
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
        self.kind == other.kind
            && self.name == other.name
            && self.line_file == other.line_file
            && self.boundary == other.boundary
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
        if let Some(boundary) = self.boundary {
            text.push_str(" before line ");
            text.push_str(&boundary.to_string());
        }
        text
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    #[test]
    fn trust_before_line_dependency_keeps_boundary_when_merged() {
        let dependency = ProofTrustSummary::cli_trusted_prefix((17, Rc::from("chapter.lit")), 42);
        let mut summary = ProofTrustSummary::new();
        summary.merge(&dependency);
        summary.merge(&dependency);

        assert_eq!(summary.dependencies.len(), 1);
        assert_eq!(summary.dependencies[0].kind, "cli_trusted_prefix");
        assert_eq!(summary.dependencies[0].line_file.0, 17);
        assert_eq!(summary.dependencies[0].boundary, Some(42));
    }

    #[test]
    fn ordinary_trust_dependency_has_no_boundary() {
        let summary =
            ProofTrustSummary::from_dependency("trust", None, (7, Rc::from("example.lit")));

        assert_eq!(summary.dependencies.len(), 1);
        assert_eq!(summary.dependencies[0].boundary, None);
    }
}
