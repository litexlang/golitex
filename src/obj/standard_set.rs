use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum StandardSet {
    NPos,
    N,
    Q,
    Z,
    R,
    C,
    QPos,
    RPos,
    QNeg,
    ZNeg,
    RNeg,
    QNz,
    ZNz,
    RNz,
}

impl fmt::Display for StandardSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            StandardSet::NPos => write!(f, "{}", COMPACT_N_POS),
            StandardSet::N => write!(f, "{}", N),
            StandardSet::Q => write!(f, "{}", Q),
            StandardSet::Z => write!(f, "{}", Z),
            StandardSet::R => write!(f, "{}", R),
            StandardSet::C => write!(f, "{}", C),
            StandardSet::QPos => write!(f, "{}", COMPACT_Q_POS),
            StandardSet::RPos => write!(f, "{}", COMPACT_R_POS),
            StandardSet::QNeg => write!(f, "{}", COMPACT_Q_NEG),
            StandardSet::ZNeg => write!(f, "{}", COMPACT_Z_NEG),
            StandardSet::RNeg => write!(f, "{}", COMPACT_R_NEG),
            StandardSet::QNz => write!(f, "{}", COMPACT_Q_NZ),
            StandardSet::ZNz => write!(f, "{}", COMPACT_Z_NZ),
            StandardSet::RNz => write!(f, "{}", COMPACT_R_NZ),
        }
    }
}
