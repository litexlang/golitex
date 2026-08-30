#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FileRunMode {
    Project,
    Isolated,
}

impl FileRunMode {
    pub fn from_isolated(isolated: bool) -> Self {
        if isolated {
            Self::Isolated
        } else {
            Self::Project
        }
    }

    pub fn is_isolated(self) -> bool {
        self == Self::Isolated
    }
}

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
    File { path: String, mode: FileRunMode },
    Repository { path: String },
}

impl RunTarget {
    pub fn kind(&self) -> RunTargetKind {
        match self {
            Self::Eval => RunTargetKind::Code,
            Self::File { .. } => RunTargetKind::File,
            Self::Repository { .. } => RunTargetKind::Repository,
        }
    }

    pub fn path(&self) -> Option<&str> {
        match self {
            Self::Eval => None,
            Self::File { path, .. } | Self::Repository { path } => Some(path),
        }
    }

    pub fn source_label(&self) -> &str {
        match self {
            Self::Eval => "eval",
            Self::File { path, .. } | Self::Repository { path } => path,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SessionTarget {
    CurrentDirectory,
    Isolated,
    File { path: String, mode: FileRunMode },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExecutionTarget {
    Run(RunTarget),
    Repl,
    Session(SessionTarget),
}

impl ExecutionTarget {
    pub fn source_label(&self) -> &str {
        match self {
            Self::Run(target) => target.source_label(),
            Self::Repl => "repl",
            Self::Session(_) => "session",
        }
    }
}
