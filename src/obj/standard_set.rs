use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
    QStar,
    ZStar,
    RStar,
    CStar,
}

impl StandardSet {
    /// Whether membership in `self` may be projected to membership in
    /// `superset` through Litex's standard numeric-set hierarchy.
    ///
    /// This is deliberately about membership projection, not about lowering a
    /// heterogeneous set proposition such as `N $subset Z` to Lean.
    pub(crate) fn is_subset_eq(&self, superset: &Self) -> bool {
        matches!(
            (self, superset),
            (_, StandardSet::C)
                | (StandardSet::NPos, StandardSet::NPos)
                | (StandardSet::NPos, StandardSet::N)
                | (StandardSet::NPos, StandardSet::Z)
                | (StandardSet::NPos, StandardSet::Q)
                | (StandardSet::NPos, StandardSet::R)
                | (StandardSet::NPos, StandardSet::QPos)
                | (StandardSet::NPos, StandardSet::RPos)
                | (StandardSet::NPos, StandardSet::ZStar)
                | (StandardSet::NPos, StandardSet::QStar)
                | (StandardSet::NPos, StandardSet::RStar)
                | (StandardSet::N, StandardSet::N)
                | (StandardSet::N, StandardSet::Z)
                | (StandardSet::N, StandardSet::Q)
                | (StandardSet::N, StandardSet::R)
                | (StandardSet::ZNeg, StandardSet::ZNeg)
                | (StandardSet::ZNeg, StandardSet::Z)
                | (StandardSet::ZNeg, StandardSet::Q)
                | (StandardSet::ZNeg, StandardSet::R)
                | (StandardSet::ZNeg, StandardSet::QNeg)
                | (StandardSet::ZNeg, StandardSet::RNeg)
                | (StandardSet::ZNeg, StandardSet::ZStar)
                | (StandardSet::ZNeg, StandardSet::QStar)
                | (StandardSet::ZNeg, StandardSet::RStar)
                | (StandardSet::ZStar, StandardSet::ZStar)
                | (StandardSet::ZStar, StandardSet::Z)
                | (StandardSet::ZStar, StandardSet::Q)
                | (StandardSet::ZStar, StandardSet::R)
                | (StandardSet::ZStar, StandardSet::QStar)
                | (StandardSet::ZStar, StandardSet::RStar)
                | (StandardSet::Z, StandardSet::Z)
                | (StandardSet::Z, StandardSet::Q)
                | (StandardSet::Z, StandardSet::R)
                | (StandardSet::QPos, StandardSet::QPos)
                | (StandardSet::QPos, StandardSet::Q)
                | (StandardSet::QPos, StandardSet::R)
                | (StandardSet::QPos, StandardSet::RPos)
                | (StandardSet::QPos, StandardSet::QStar)
                | (StandardSet::QPos, StandardSet::RStar)
                | (StandardSet::QNeg, StandardSet::QNeg)
                | (StandardSet::QNeg, StandardSet::Q)
                | (StandardSet::QNeg, StandardSet::R)
                | (StandardSet::QNeg, StandardSet::RNeg)
                | (StandardSet::QNeg, StandardSet::QStar)
                | (StandardSet::QNeg, StandardSet::RStar)
                | (StandardSet::QStar, StandardSet::QStar)
                | (StandardSet::QStar, StandardSet::Q)
                | (StandardSet::QStar, StandardSet::R)
                | (StandardSet::QStar, StandardSet::RStar)
                | (StandardSet::Q, StandardSet::Q)
                | (StandardSet::Q, StandardSet::R)
                | (StandardSet::RPos, StandardSet::RPos)
                | (StandardSet::RPos, StandardSet::R)
                | (StandardSet::RPos, StandardSet::RStar)
                | (StandardSet::RNeg, StandardSet::RNeg)
                | (StandardSet::RNeg, StandardSet::R)
                | (StandardSet::RNeg, StandardSet::RStar)
                | (StandardSet::RStar, StandardSet::RStar)
                | (StandardSet::RStar, StandardSet::R)
                | (StandardSet::NPos, StandardSet::CStar)
                | (StandardSet::ZNeg, StandardSet::CStar)
                | (StandardSet::ZStar, StandardSet::CStar)
                | (StandardSet::QPos, StandardSet::CStar)
                | (StandardSet::QNeg, StandardSet::CStar)
                | (StandardSet::QStar, StandardSet::CStar)
                | (StandardSet::RPos, StandardSet::CStar)
                | (StandardSet::RNeg, StandardSet::CStar)
                | (StandardSet::RStar, StandardSet::CStar)
                | (StandardSet::CStar, StandardSet::CStar)
                | (StandardSet::R, StandardSet::R)
        )
    }

    /// Proper standard subcarriers to try when proving membership in `self`.
    ///
    /// The candidates come from the target carrier, never from sets previously
    /// stored for the element. Example: proving `x $in C` may ask for
    /// `x $in N`, `x $in Z`, `x $in Q`, or `x $in R` even on a cold query.
    pub(crate) fn proper_subsets_in_membership_proof_order(&self) -> Vec<Self> {
        [
            Self::N,
            Self::Z,
            Self::Q,
            Self::R,
            Self::NPos,
            Self::ZNeg,
            Self::ZStar,
            Self::QPos,
            Self::QNeg,
            Self::QStar,
            Self::RPos,
            Self::RNeg,
            Self::RStar,
            Self::CStar,
        ]
        .into_iter()
        .filter(|source| source != self && source.is_subset_eq(self))
        .collect()
    }
}

impl fmt::Display for StandardSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            StandardSet::NPos => write!(f, "{}", N_POSITIVE),
            StandardSet::N => write!(f, "{}", N),
            StandardSet::Q => write!(f, "{}", Q),
            StandardSet::Z => write!(f, "{}", Z),
            StandardSet::R => write!(f, "{}", R),
            StandardSet::C => write!(f, "{}", C),
            StandardSet::QPos => write!(f, "{}", Q_POSITIVE),
            StandardSet::RPos => write!(f, "{}", R_POSITIVE),
            StandardSet::QNeg => write!(f, "{}", Q_NEGATIVE),
            StandardSet::ZNeg => write!(f, "{}", Z_NEGATIVE),
            StandardSet::RNeg => write!(f, "{}", R_NEGATIVE),
            StandardSet::QStar => write!(f, "{}", Q_NOT_ZERO),
            StandardSet::ZStar => write!(f, "{}", Z_NOT_ZERO),
            StandardSet::RStar => write!(f, "{}", R_NOT_ZERO),
            StandardSet::CStar => write!(f, "{}", C_NOT_ZERO),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn membership_projection_candidates_are_proper_and_target_driven() {
        let complex_sources = StandardSet::C.proper_subsets_in_membership_proof_order();
        assert!(complex_sources.contains(&StandardSet::N));
        assert!(complex_sources.contains(&StandardSet::Z));
        assert!(complex_sources.contains(&StandardSet::Q));
        assert!(complex_sources.contains(&StandardSet::R));
        assert!(complex_sources.contains(&StandardSet::CStar));
        assert!(!complex_sources.contains(&StandardSet::C));
        assert_eq!(
            &complex_sources[..4],
            &[
                StandardSet::N,
                StandardSet::Z,
                StandardSet::Q,
                StandardSet::R,
            ]
        );

        let real_sources = StandardSet::R.proper_subsets_in_membership_proof_order();
        assert!(!real_sources.contains(&StandardSet::C));
        assert!(!real_sources.contains(&StandardSet::CStar));

        for target in [
            StandardSet::NPos,
            StandardSet::N,
            StandardSet::ZNeg,
            StandardSet::ZStar,
            StandardSet::Z,
            StandardSet::QPos,
            StandardSet::QNeg,
            StandardSet::QStar,
            StandardSet::Q,
            StandardSet::RPos,
            StandardSet::RNeg,
            StandardSet::RStar,
            StandardSet::R,
            StandardSet::CStar,
            StandardSet::C,
        ] {
            for source in target.proper_subsets_in_membership_proof_order() {
                assert_ne!(source, target);
                assert!(source.is_subset_eq(&target));
            }
        }
    }
}
