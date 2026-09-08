use crate::prelude::*;

pub struct VerifyForallFactWithIffResult {
    pub then_implies_iff: VerifyForallFactResult,
    pub iff_implies_then: VerifyForallFactResult,
}
