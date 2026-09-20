use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstError {
    CannotUseAsFnHead,
}

impl fmt::Display for InstError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InstError::CannotUseAsFnHead => {
                write!(f, "substituted object cannot be used as a function head")
            }
        }
    }
}

impl std::error::Error for InstError {}
