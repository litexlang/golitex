use super::closed_calculation_proof::ClosedCalculationProof;
use super::AtomicFactSearchedProof;

// Direct has three successful routes and one soft miss. Known proofs retain their
// existing identity/path/citation payload; calculation never manufactures a cite.
pub enum DirectAtomicFactSearchResult {
    ByKnownFact(AtomicFactSearchedProof),
    ByClosedCalculation(ClosedCalculationProof),
    ByStructuralMembership(super::structural_membership_proof::StructuralMembershipProof),
    NotFound,
}
