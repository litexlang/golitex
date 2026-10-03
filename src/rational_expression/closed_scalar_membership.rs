//! Exact standard-set classification shared by Direct and builtin leaves.
use super::exact_rational::EvalRational;
use crate::ast::obj::StandardSet;

pub(crate) fn normalized_decimal_inhabits_standard_set(v: &str, set: &StandardSet) -> bool {
    let v = v.trim();
    let is_integer = !v.contains('.');
    let is_negative = v.starts_with('-');
    let is_zero = v == "0";
    let is_positive = !is_negative && !is_zero;
    let is_nonzero = !is_zero;
    match set {
        StandardSet::N => is_integer && !is_negative,
        StandardSet::NPos => is_integer && is_positive,
        StandardSet::Z => is_integer,
        StandardSet::ZStar => is_integer && is_nonzero,
        StandardSet::ZNeg => is_integer && is_negative,
        StandardSet::Q | StandardSet::R | StandardSet::C => true,
        StandardSet::QPos | StandardSet::RPos => is_positive,
        StandardSet::QNeg | StandardSet::RNeg => is_negative,
        StandardSet::QStar | StandardSet::RStar | StandardSet::CStar => is_nonzero,
    }
}

pub(crate) fn exact_complex_inhabits_standard_set(
    real: &EvalRational,
    imaginary: &EvalRational,
    set: &StandardSet,
) -> bool {
    let real_only = imaginary.is_zero();
    let nonzero = !real.is_zero();
    let positive = nonzero && !real.is_negative();
    let integer = real.to_i128_if_integer().is_some();
    match set {
        StandardSet::C => true,
        StandardSet::CStar => nonzero || !imaginary.is_zero(),
        StandardSet::R | StandardSet::Q => real_only,
        StandardSet::RStar | StandardSet::QStar => real_only && nonzero,
        StandardSet::RPos | StandardSet::QPos => real_only && positive,
        StandardSet::RNeg | StandardSet::QNeg => real_only && real.is_negative(),
        StandardSet::Z => real_only && integer,
        StandardSet::ZStar => real_only && integer && nonzero,
        StandardSet::ZNeg => real_only && integer && real.is_negative(),
        StandardSet::N => real_only && integer && !real.is_negative(),
        StandardSet::NPos => real_only && integer && positive,
    }
}
