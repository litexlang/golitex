//! Parameter sets and standard-set representations.

use super::super::*;

pub(in super::super) fn parameter_set(param_type: &ParamType) -> Result<&Obj, String> {
    match param_type {
        ParamType::Obj(set) => Ok(set),
        _ => Err(format!(
            "unsupported compiler parameter type `{param_type}`"
        )),
    }
}

pub(in super::super) fn render_lean_source_for_standard_set_representation(
    set: LeanTargetStandardSet,
) -> Result<String, String> {
    let name = match set {
        LeanTargetStandardSet::PositiveNatural => "Litex.NPos",
        LeanTargetStandardSet::Natural => "Litex.N",
        LeanTargetStandardSet::Integer => "Litex.Z",
        LeanTargetStandardSet::Rational => "Litex.Q",
        LeanTargetStandardSet::Real => "Litex.R",
        LeanTargetStandardSet::Complex => "Litex.C",
        LeanTargetStandardSet::PositiveRational => "Litex.QPos",
        LeanTargetStandardSet::PositiveReal => "Litex.RPos",
        LeanTargetStandardSet::NegativeInteger => "Litex.ZNeg",
        LeanTargetStandardSet::NegativeRational => "Litex.QNeg",
        LeanTargetStandardSet::NegativeReal => "Litex.RNeg",
        LeanTargetStandardSet::NonzeroInteger => "Litex.ZStar",
        LeanTargetStandardSet::NonzeroRational => "Litex.QStar",
        LeanTargetStandardSet::NonzeroReal => "Litex.RStar",
        LeanTargetStandardSet::NonzeroComplex => "Litex.CStar",
    };
    Ok(name.into())
}

pub(in super::super) fn render_standard_set(set: StandardSet) -> Result<&'static str, String> {
    match set {
        StandardSet::N => Ok("Litex.N"),
        StandardSet::NPos => Ok("Litex.NPos"),
        StandardSet::Z => Ok("Litex.Z"),
        StandardSet::ZStar => Ok("Litex.ZStar"),
        StandardSet::Q => Ok("Litex.Q"),
        StandardSet::QPos => Ok("Litex.QPos"),
        StandardSet::QNeg => Ok("Litex.QNeg"),
        StandardSet::QStar => Ok("Litex.QStar"),
        StandardSet::R => Ok("Litex.R"),
        StandardSet::RPos => Ok("Litex.RPos"),
        StandardSet::RNeg => Ok("Litex.RNeg"),
        StandardSet::RStar => Ok("Litex.RStar"),
        StandardSet::C => Ok("Litex.C"),
        StandardSet::CStar => Ok("Litex.CStar"),
        StandardSet::ZNeg => Ok("Litex.ZNeg"),
    }
}
