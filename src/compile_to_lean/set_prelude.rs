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
def {is_finite_set} {generic_type_binder} (set : Set {carrier}) : Prop := set.Finite"#,
        universe = TO_LEAN_DEFAULT_UNIVERSE,
        object_class = TO_LEAN_OBJECT_CLASS,
        is_set = TO_LEAN_IS_SET,
        is_nonempty_set = TO_LEAN_IS_NONEMPTY_SET,
        is_finite_set = TO_LEAN_IS_FINITE_SET,
    )
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
        assert!(!prelude.contains("LitexUniverse"));
        assert!(!prelude.contains("LitexFact"));
    }
}
