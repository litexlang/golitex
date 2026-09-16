use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstError {
    MissingStructCarrier,
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
        }
    }
}

impl std::error::Error for InstError {}
