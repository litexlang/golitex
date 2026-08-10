/// Lean declarations shared by every generated source.
///
/// Litex keeps one source object sort, while Lean uses native Mathlib carriers.
/// This prelude marks the supported target carriers as Litex objects and keeps
/// `$is_set`, nonemptiness, and finiteness as ordinary propositions. It does
/// not define a universal value wrapper or private arithmetic/equality laws.
pub(super) const LITEX_OBJECT_PRELUDE: &str = r#"universe u

abbrev LitexFact := Prop

class LitexObject (α : Type u) : Prop where
  valid : True

instance : LitexObject ℕ := ⟨True.intro⟩
instance : LitexObject ℤ := ⟨True.intro⟩
instance : LitexObject ℚ := ⟨True.intro⟩
instance : LitexObject ℝ := ⟨True.intro⟩
instance : LitexObject ℂ := ⟨True.intro⟩
instance {α : Type u} [LitexObject α] : LitexObject (Set α) := ⟨True.intro⟩

def litexIsSet {α : Type u} [LitexObject α] (_ : α) : Prop := True
def litexIsNonemptySet {α : Type u} (set : Set α) : Prop := set.Nonempty
def litexIsFiniteSet {α : Type u} (set : Set α) : Prop := set.Finite"#;
