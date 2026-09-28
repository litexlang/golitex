#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RunTargetKind {
    Code,
    File,
    Repository,
    Session,
}

impl RunTargetKind {
    pub fn json_name(self) -> &'static str {
        match self {
            Self::Code => "code",
            Self::File => "file",
            Self::Repository => "repo",
            Self::Session => "session",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunTarget {
    Eval,
    File { path: String },
    IsolatedFile { path: String },
    Repository { path: String },
}

impl RunTarget {
    pub fn kind(&self) -> RunTargetKind {
        match self {
            Self::Eval => RunTargetKind::Code,
            Self::File { .. } | Self::IsolatedFile { .. } => RunTargetKind::File,
            Self::Repository { .. } => RunTargetKind::Repository,
        }
    }

    pub fn path(&self) -> Option<&str> {
        match self {
            Self::Eval => None,
            Self::File { path } | Self::IsolatedFile { path } | Self::Repository { path } => {
                Some(path)
            }
        }
    }

    /// Human-readable label for diagnostics. This is not a filesystem path.
    pub fn display_label(&self) -> &str {
        match self {
            Self::Eval => "eval",
            Self::File { path } | Self::IsolatedFile { path } | Self::Repository { path } => path,
        }
    }

    /// Compatibility name for callers that still use the old label wording.
    #[deprecated(note = "use display_label; this value is not necessarily a path")]
    pub fn source_label(&self) -> &str {
        self.display_label()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SessionTarget {
    CurrentDirectory,
    Isolated,
    File { path: String },
    IsolatedFile { path: String },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExecutionTarget {
    Run(RunTarget),
    Repl,
    Session(SessionTarget),
}

impl ExecutionTarget {
    pub fn virtual_source(&self) -> Option<VirtualSource> {
        match self {
            Self::Run(RunTarget::Eval) => Some(VirtualSource::Eval),
            Self::Run(RunTarget::File { .. })
            | Self::Run(RunTarget::IsolatedFile { .. })
            | Self::Run(RunTarget::Repository { .. }) => None,
            Self::Repl => Some(VirtualSource::Repl),
            Self::Session(_) => Some(VirtualSource::Session),
        }
    }

    /// Human-readable label for diagnostics. This is not a filesystem path.
    pub fn display_label(&self) -> &str {
        match self {
            Self::Run(target) => target.display_label(),
            Self::Repl => "repl",
            Self::Session(_) => "session",
        }
    }

    /// Compatibility name for callers that still use the old label wording.
    #[deprecated(note = "use display_label; this value is not necessarily a path")]
    pub fn source_label(&self) -> &str {
        self.display_label()
    }
}
use crate::module_system::VirtualSource;
