use super::verify_equality::verification_and_result::VerifyEqualityResult2;
use super::verify_non_equational_atomic_fact::verification_and_result::
    VerifyNonEquationalAtomicFactResult2;

pub enum VerifyAtomicFactResult2 {
    Equality(VerifyEqualityResult2),
    NonEquationalAtomicFact(VerifyNonEquationalAtomicFactResult2),
}
