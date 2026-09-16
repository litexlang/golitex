use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstError {
    MissingStructCarrier,
    CannotUseAsFnHead,
}

impl fmt::Display for InstError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InstError::MissingStructCarrier => {
                write!(
                    f,
                    "ObjAsStructInstanceWithFieldAccess has no resolved_struct_carrier"
                )
            }
            InstError::CannotUseAsFnHead => {
                write!(f, "substituted object cannot be used as a function head")
            }
        }
    }
}

impl std::error::Error for InstError {}
