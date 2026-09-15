use std::fmt;
use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealOrVirtualPath {
    Real(PathBuf),
    Eval,
    Repl,
}

impl RealOrVirtualPath {
    pub fn display_path(&self) -> PathBuf {
        match self {
            RealOrVirtualPath::Real(path) => path.clone(),
            RealOrVirtualPath::Eval => PathBuf::from("<eval>"),
            RealOrVirtualPath::Repl => PathBuf::from("<repl>"),
        }
    }

    pub fn name(&self) -> String {
        match self {
            RealOrVirtualPath::Real(path) => path
                .file_name()
                .and_then(|name| name.to_str())
                .map(str::to_owned)
                .unwrap_or_else(|| path.to_string_lossy().into_owned()),
            RealOrVirtualPath::Eval => "<eval>".to_string(),
            RealOrVirtualPath::Repl => "<repl>".to_string(),
        }
    }
}

impl fmt::Display for RealOrVirtualPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RealOrVirtualPath::Real(path) => write!(f, "{}", path.display()),
            RealOrVirtualPath::Eval => write!(f, "<eval>"),
            RealOrVirtualPath::Repl => write!(f, "<repl>"),
        }
    }
}
