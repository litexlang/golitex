use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum StandardSet {
    NPos,
    N,
    Q,
    Z,
    R,
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StandardSet::NPos => write!(f, "{}", N_POS),
            StandardSet::N => write!(f, "{}", N),
            StandardSet::Q => write!(f, "{}", Q),
            StandardSet::Z => write!(f, "{}", Z),
            StandardSet::R => write!(f, "{}", R),
            StandardSet::QPos => write!(f, "{}", Q_POS),
            StandardSet::RPos => write!(f, "{}", R_POS),
            StandardSet::QNeg => write!(f, "{}", Q_NEG),
            StandardSet::ZNeg => write!(f, "{}", Z_NEG),
            StandardSet::RNeg => write!(f, "{}", R_NEG),
            StandardSet::QNz => write!(f, "{}", Q_NZ),
            StandardSet::ZNz => write!(f, "{}", Z_NZ),
            StandardSet::RNz => write!(f, "{}", R_NZ),
        }
    }
}
