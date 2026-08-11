use crate::prelude::*;
use std::rc::Rc;

/// Stable only within one executed source statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WellDefinednessCertificateId(u64);

impl WellDefinednessCertificateId {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WellDefinednessRequirementRole {
    /// The verifier consumed this proof while checking an object. Whether a
    /// target term also consumes it is decided only by a typed application
    /// certificate, never by dropping this audit entry.
    SourceObjectRequirement,
}

/// One exact successful factual proof retained while an object
/// well-definedness scope is still alive.
#[derive(Clone, Debug)]
pub struct WellDefinednessFactEvidence {
    pub certificate_id: WellDefinednessCertificateId,
    pub role: WellDefinednessRequirementRole,
    pub proof: Rc<FactualStmtSuccess>,
}

#[derive(Clone, Debug, Default)]
pub struct WellDefinednessCertificate {
    pub facts: Vec<WellDefinednessFactEvidence>,
}

impl WellDefinednessCertificate {
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }
}
