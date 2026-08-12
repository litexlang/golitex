use crate::prelude::*;

use super::helper::{
    lean_generic_object_binder, TO_LEAN_DEFAULT_UNIVERSE, TO_LEAN_GENERIC_CARRIER_PREFIX,
    TO_LEAN_IS_FINITE_SET, TO_LEAN_IS_NONEMPTY_SET, TO_LEAN_IS_SET, TO_LEAN_OBJECT_CLASS,
};

/// Lean declarations shared by every generated source.
///
/// Litex keeps one source object sort, while Lean uses native Mathlib carriers.
/// This prelude marks the supported target carriers as Litex objects and keeps
/// `$is_set`, nonemptiness, and finiteness as ordinary propositions. It does
/// not define a universal value wrapper or private arithmetic/equality laws.
pub(super) fn lean_object_prelude() -> String {
    let carrier = TO_LEAN_GENERIC_CARRIER_PREFIX;
    let generic_type_binder = format!("{{{} : Type {}}}", carrier, TO_LEAN_DEFAULT_UNIVERSE);
    let generic_object_binder = lean_generic_object_binder(carrier);

    format!(
        r#"universe {universe}

class {object_class} ({carrier} : Type {universe}) : Prop where
  valid : True

instance : {object_class} ℕ := ⟨True.intro⟩
instance : {object_class} ℤ := ⟨True.intro⟩
instance : {object_class} ℚ := ⟨True.intro⟩
instance : {object_class} ℝ := ⟨True.intro⟩
instance : {object_class} ℂ := ⟨True.intro⟩
instance {generic_object_binder} : {object_class} (Set {carrier}) := ⟨True.intro⟩

def {is_set} {generic_object_binder} (_ : {carrier}) : Prop := True
def {is_nonempty_set} {generic_type_binder} (set : Set {carrier}) : Prop := set.Nonempty
def {is_finite_set} {generic_type_binder} (set : Set {carrier}) : Prop := set.Finite

namespace Litex.StandardSets

abbrev N : Set ℕ := Set.univ
abbrev NPos : Set ℕ := Set.Ioi 0

abbrev Z : Set ℤ := Set.univ
abbrev ZNeg : Set ℤ := Set.Iio 0
abbrev ZStar : Set ℤ := {{z | z ≠ 0}}

abbrev Q : Set ℚ := Set.univ
abbrev QPos : Set ℚ := Set.Ioi 0
abbrev QNeg : Set ℚ := Set.Iio 0
abbrev QStar : Set ℚ := {{q | q ≠ 0}}

abbrev R : Set ℝ := Set.univ
abbrev RPos : Set ℝ := Set.Ioi 0
abbrev RNeg : Set ℝ := Set.Iio 0
abbrev RStar : Set ℝ := {{r | r ≠ 0}}

abbrev C : Set ℂ := Set.univ
abbrev CStar : Set ℂ := {{c | c ≠ 0}}

end Litex.StandardSets"#,
        universe = TO_LEAN_DEFAULT_UNIVERSE,
        object_class = TO_LEAN_OBJECT_CLASS,
        is_set = TO_LEAN_IS_SET,
        is_nonempty_set = TO_LEAN_IS_NONEMPTY_SET,
        is_finite_set = TO_LEAN_IS_FINITE_SET,
    )
}

pub(super) fn lean_standard_set_name(set: LitexToLeanStandardSetIr) -> &'static str {
    match set {
        LitexToLeanStandardSetIr::PositiveNatural => "Litex.StandardSets.NPos",
        LitexToLeanStandardSetIr::Natural => "Litex.StandardSets.N",
        LitexToLeanStandardSetIr::Rational => "Litex.StandardSets.Q",
        LitexToLeanStandardSetIr::Integer => "Litex.StandardSets.Z",
        LitexToLeanStandardSetIr::Real => "Litex.StandardSets.R",
        LitexToLeanStandardSetIr::Complex => "Litex.StandardSets.C",
        LitexToLeanStandardSetIr::PositiveRational => "Litex.StandardSets.QPos",
        LitexToLeanStandardSetIr::PositiveReal => "Litex.StandardSets.RPos",
        LitexToLeanStandardSetIr::NegativeRational => "Litex.StandardSets.QNeg",
        LitexToLeanStandardSetIr::NegativeInteger => "Litex.StandardSets.ZNeg",
        LitexToLeanStandardSetIr::NegativeReal => "Litex.StandardSets.RNeg",
        LitexToLeanStandardSetIr::NonzeroRational => "Litex.StandardSets.QStar",
        LitexToLeanStandardSetIr::NonzeroInteger => "Litex.StandardSets.ZStar",
        LitexToLeanStandardSetIr::NonzeroReal => "Litex.StandardSets.RStar",
        LitexToLeanStandardSetIr::NonzeroComplex => "Litex.StandardSets.CStar",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn object_prelude_uses_the_shared_universe_and_binder() {
        let prelude = lean_object_prelude();

        assert!(prelude.lines().any(|line| line == "universe u"));
        assert!(prelude.contains("class LitexObject (α : Type u) : Prop where"));
        assert!(prelude.contains(
            "instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩"
        ));
        assert!(
            prelude.contains("def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True")
        );
        for declaration in [
            "abbrev N : Set ℕ := Set.univ",
            "abbrev NPos : Set ℕ := Set.Ioi 0",
            "abbrev Z : Set ℤ := Set.univ",
            "abbrev ZNeg : Set ℤ := Set.Iio 0",
            "abbrev ZStar : Set ℤ := {z | z ≠ 0}",
            "abbrev Q : Set ℚ := Set.univ",
            "abbrev QPos : Set ℚ := Set.Ioi 0",
            "abbrev QNeg : Set ℚ := Set.Iio 0",
            "abbrev QStar : Set ℚ := {q | q ≠ 0}",
            "abbrev R : Set ℝ := Set.univ",
            "abbrev RPos : Set ℝ := Set.Ioi 0",
            "abbrev RNeg : Set ℝ := Set.Iio 0",
            "abbrev RStar : Set ℝ := {r | r ≠ 0}",
            "abbrev C : Set ℂ := Set.univ",
            "abbrev CStar : Set ℂ := {c | c ≠ 0}",
        ] {
            assert!(prelude.contains(declaration), "missing `{declaration}`");
        }
        assert!(!prelude.contains("LitexUniverse"));
        assert!(!prelude.contains("LitexFact"));
    }

    #[test]
    fn every_standard_set_ir_uses_its_prelude_name() {
        for (set, expected) in [
            (
                LitexToLeanStandardSetIr::PositiveNatural,
                "Litex.StandardSets.NPos",
            ),
            (LitexToLeanStandardSetIr::Natural, "Litex.StandardSets.N"),
            (LitexToLeanStandardSetIr::Rational, "Litex.StandardSets.Q"),
            (LitexToLeanStandardSetIr::Integer, "Litex.StandardSets.Z"),
            (LitexToLeanStandardSetIr::Real, "Litex.StandardSets.R"),
            (LitexToLeanStandardSetIr::Complex, "Litex.StandardSets.C"),
            (
                LitexToLeanStandardSetIr::PositiveRational,
                "Litex.StandardSets.QPos",
            ),
            (
                LitexToLeanStandardSetIr::PositiveReal,
                "Litex.StandardSets.RPos",
            ),
            (
                LitexToLeanStandardSetIr::NegativeRational,
                "Litex.StandardSets.QNeg",
            ),
            (
                LitexToLeanStandardSetIr::NegativeInteger,
                "Litex.StandardSets.ZNeg",
            ),
            (
                LitexToLeanStandardSetIr::NegativeReal,
                "Litex.StandardSets.RNeg",
            ),
            (
                LitexToLeanStandardSetIr::NonzeroRational,
                "Litex.StandardSets.QStar",
            ),
            (
                LitexToLeanStandardSetIr::NonzeroInteger,
                "Litex.StandardSets.ZStar",
            ),
            (
                LitexToLeanStandardSetIr::NonzeroReal,
                "Litex.StandardSets.RStar",
            ),
            (
                LitexToLeanStandardSetIr::NonzeroComplex,
                "Litex.StandardSets.CStar",
            ),
        ] {
            assert_eq!(lean_standard_set_name(set), expected);
        }
    }
}
