pub enum VerifyAtomicFactResult {
    Equality(VerifyEqualityResult),
    NonEquationalAtomicFact(VerifyNonEquationalAtomicFactResult),
}
