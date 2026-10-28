//! Evidence retained by execution result producers.
//!
//! This policy belongs to execution, not JSON projection. It never changes
//! which mathematical checks run. A parent checks the mode of each child;
//! checking a mode does not convert or reconstruct evidence.

use crate::runtime::{RuntimeError, RuntimeResult};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum OutputDetail {
    Compact,
    #[default]
    Normal,
    Detailed,
}

impl OutputDetail {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Compact => "compact",
            Self::Normal => "normal",
            Self::Detailed => "detailed",
        }
    }

    /// Check a pipeline boundary without reducing one mode to another.
    pub fn require(self, actual: Self, stage: &str) -> RuntimeResult<()> {
        if self == actual {
            Ok(())
        } else {
            Err(RuntimeError::InternalBug(format!(
                "{stage}: expected {} result, received {} result",
                self.as_str(),
                actual.as_str(),
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_cross_mode_boundary_is_an_internal_bug() {
        let modes = [
            OutputDetail::Compact,
            OutputDetail::Normal,
            OutputDetail::Detailed,
        ];
        for expected in modes {
            for actual in modes {
                let result = expected.require(actual, "verify child");
                if expected == actual {
                    assert!(result.is_ok());
                } else {
                    let Err(RuntimeError::InternalBug(message)) = result else {
                        panic!("mode mismatch must be an internal bug");
                    };
                    assert!(message.contains(expected.as_str()));
                    assert!(message.contains(actual.as_str()));
                    assert!(message.contains("verify child"));
                }
            }
        }
    }
}
