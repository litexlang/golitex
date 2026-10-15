use std::fmt;
use std::path::{Path, PathBuf};

/// Diagnostic context only; module execution and rollback remain unchanged.
#[derive(Clone, Debug)]
pub struct ImportFailure {
    pub path: PathBuf,
    pub cause: ImportFailureCause,
    pub import_chain: Vec<PathBuf>,
}

#[derive(Clone, Debug)]
pub enum ImportFailureCause {
    MissingDirectory,
    Cycle,
    Mount(String),
    RejectedExport { statements: Vec<String> },
}

impl ImportFailure {
    pub fn new(path: PathBuf, cause: ImportFailureCause) -> Self {
        Self {
            import_chain: vec![path.clone()],
            path,
            cause,
        }
    }

    pub fn rejected_export(file: &crate::run::run_command_outcome::RunFileResult) -> Self {
        let statements = file
            .run
            .statement_results
            .iter()
            .enumerate()
            .filter(|(_, result)| result.is_failed())
            .filter_map(|(index, _)| file.run.statement_texts.get(index).cloned())
            .collect();
        Self::new(
            file.path.clone(),
            ImportFailureCause::RejectedExport { statements },
        )
    }

    pub fn prepend(&mut self, parent: &Path) {
        self.import_chain.insert(0, parent.to_path_buf());
    }
}

impl fmt::Display for ImportFailure {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.cause {
            ImportFailureCause::MissingDirectory => write!(
                f,
                "module directory does not exist: {}",
                self.path.display()
            )?,
            ImportFailureCause::Cycle => {
                write!(f, "cyclic module import: {}", self.path.display())?
            }
            ImportFailureCause::Mount(message) => write!(
                f,
                "could not mount module {}: {message}",
                self.path.display()
            )?,
            ImportFailureCause::RejectedExport { statements } => {
                write!(f, "export rejected: {}", self.path.display())?;
                for statement in statements {
                    write!(f, "\n  rejected: {statement}")?;
                }
            }
        }
        if self.import_chain.len() > 1 {
            write!(f, "\nimport chain: ")?;
            for (index, path) in self.import_chain.iter().enumerate() {
                if index > 0 {
                    write!(f, " -> ")?;
                }
                write!(f, "{}", path.display())?;
            }
        }
        Ok(())
    }
}
