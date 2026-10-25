use crate::ast::obj::FnSet;
use crate::runtime::FactId;

/// The signature already selected by a structural consumer. A literal owns its
/// body; an indexed property retains the exact source fact that supplied it.
pub enum FunctionSignatureSelection {
    AnonymousLiteral {
        signature: FnSet,
    },
    Property {
        signature: FnSet,
        fact_id: FactId,
    },
    /// The structural field resolver supplied the carrier directly, without
    /// selecting an indexed membership fact. Consumers must handle that route
    /// explicitly; this is not a fabricated property citation.
    DeclaredField {
        signature: FnSet,
    },
}

impl FunctionSignatureSelection {
    pub fn signature(&self) -> &FnSet {
        match self {
            Self::AnonymousLiteral { signature }
            | Self::Property { signature, .. }
            | Self::DeclaredField { signature } => signature,
        }
    }
}
