/// The logical bridge shared by universal-object generated Lean sources.
///
/// `LitexObject` is intentionally one target type. Standard-set membership is
/// represented by `Litex.In`; it never retypes an object. Concrete builtin
/// rules are theorems below this semantic boundary rather than new axioms.
pub(super) fn universal_object_prelude() -> &'static str {
    r#"axiom LitexObject : Type

namespace Litex

noncomputable section

axiom In : LitexObject → LitexObject → Prop
axiom IsSet : LitexObject → Prop

def IsNonemptySet (s : LitexObject) : Prop :=
  IsSet s ∧ ∃ x : LitexObject, In x s

def IsFiniteSet (s : LitexObject) : Prop :=
  IsSet s ∧ Set.Finite {x : LitexObject | In x s}

axiom embedComplex : ℂ → LitexObject
axiom embedComplex_injective : Function.Injective embedComplex

axiom N : LitexObject
axiom Z : LitexObject
axiom Q : LitexObject
axiom R : LitexObject
axiom C : LitexObject
axiom NPos : LitexObject
axiom ZNeg : LitexObject
axiom ZStar : LitexObject
axiom QPos : LitexObject
axiom QNeg : LitexObject
axiom QStar : LitexObject
axiom RPos : LitexObject
axiom RNeg : LitexObject
axiom RStar : LitexObject
axiom CStar : LitexObject

axiom inN_iff {x : LitexObject} :
  In x N ↔ ∃ n : ℕ, embedComplex (n : ℂ) = x
axiom inZ_iff {x : LitexObject} :
  In x Z ↔ ∃ z : ℤ, embedComplex (z : ℂ) = x
axiom inQ_iff {x : LitexObject} :
  In x Q ↔ ∃ q : ℚ, embedComplex (q : ℂ) = x
axiom inR_iff {x : LitexObject} :
  In x R ↔ ∃ r : ℝ, embedComplex (r : ℂ) = x
axiom inC_iff {x : LitexObject} :
  In x C ↔ ∃ z : ℂ, embedComplex z = x

axiom add : LitexObject → LitexObject → LitexObject
axiom sub : LitexObject → LitexObject → LitexObject
axiom mul : LitexObject → LitexObject → LitexObject
axiom div : LitexObject → LitexObject → LitexObject

@[simp] axiom add_embedComplex (a b : ℂ) :
  add (embedComplex a) (embedComplex b) = embedComplex (a + b)
@[simp] axiom sub_embedComplex (a b : ℂ) :
  sub (embedComplex a) (embedComplex b) = embedComplex (a - b)
@[simp] axiom mul_embedComplex (a b : ℂ) :
  mul (embedComplex a) (embedComplex b) = embedComplex (a * b)
@[simp] axiom div_embedComplex (a b : ℂ) :
  div (embedComplex a) (embedComplex b) = embedComplex (a / b)

instance (n : Nat) : OfNat LitexObject n where
  ofNat := embedComplex (n : ℂ)

def arg (args : List LitexObject) (index : Nat) : LitexObject :=
  args.getD index 0

structure FnSpec where
  arity : Nat
  requirements : List LitexObject → Prop
  range : List LitexObject → LitexObject

axiom FnSet : FnSpec → LitexObject
axiom Applicable : LitexObject → List LitexObject → Prop
axiom apply :
  (f : LitexObject) →
  (args : List LitexObject) →
  Applicable f args →
  LitexObject

instance : CoeFun LitexObject fun f =>
    (args : List LitexObject) → Applicable f args → LitexObject where
  coe := apply

axiom fnSetApplicable
    {f : LitexObject}
    {spec : FnSpec}
    {args : List LitexObject} :
    In f (FnSet spec) →
    args.length = spec.arity →
    spec.requirements args →
    Applicable f args

axiom fnSetResult
    {f : LitexObject}
    {spec : FnSpec}
    {args : List LitexObject}
    (hf : In f (FnSet spec))
    (hLength : args.length = spec.arity)
    (hRequirements : spec.requirements args) :
    In (f args (fnSetApplicable hf hLength hRequirements)) (spec.range args)

namespace BuiltinRules

theorem notEqualSymmetry {a b : LitexObject} (h : a ≠ b) : b ≠ a := by
  exact Ne.symm h

theorem numeralInN (n : Nat) : In (OfNat.ofNat n : LitexObject) N := by
  apply inN_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInZ (n : Nat) : In (OfNat.ofNat n : LitexObject) Z := by
  apply inZ_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInQ (n : Nat) : In (OfNat.ofNat n : LitexObject) Q := by
  apply inQ_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInR (n : Nat) : In (OfNat.ofNat n : LitexObject) R := by
  apply inR_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInC (n : Nat) : In (OfNat.ofNat n : LitexObject) C := by
  apply inC_iff.mpr
  exact ⟨n, rfl⟩

theorem realAddClosure {a b : LitexObject} (ha : In a R) (hb : In b R) :
    In (add a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a + b, ?_⟩
  simpa using (add_embedComplex (a : ℂ) (b : ℂ)).symm

theorem realSubClosure {a b : LitexObject} (ha : In a R) (hb : In b R) :
    In (sub a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a - b, ?_⟩
  simpa using (sub_embedComplex (a : ℂ) (b : ℂ)).symm

theorem realMulClosure {a b : LitexObject} (ha : In a R) (hb : In b R) :
    In (mul a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a * b, ?_⟩
  simpa using (mul_embedComplex (a : ℂ) (b : ℂ)).symm

theorem realDivClosure {a b : LitexObject} (ha : In a R) (hb : In b R) :
    In (div a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a / b, ?_⟩
  simpa using (div_embedComplex (a : ℂ) (b : ℂ)).symm

end BuiltinRules
end
end Litex"#
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn universal_prelude_has_one_object_type_and_membership_relation() {
        let prelude = universal_object_prelude();
        assert!(prelude.contains("axiom LitexObject : Type"));
        assert!(prelude.contains("axiom In : LitexObject → LitexObject → Prop"));
        assert!(prelude.contains("axiom IsSet : LitexObject → Prop"));
        assert!(!prelude.contains("def IsSet"));
        assert!(prelude.contains("def IsNonemptySet (s : LitexObject) : Prop :="));
        assert!(prelude.contains("IsSet s ∧ ∃ x : LitexObject, In x s"));
        assert!(prelude.contains("def IsFiniteSet (s : LitexObject) : Prop :="));
        assert!(prelude.contains("IsSet s ∧ Set.Finite {x : LitexObject | In x s}"));
        assert!(!prelude.contains("axiom IsNonemptySet"));
        assert!(!prelude.contains("axiom IsFiniteSet"));
        assert!(prelude.contains("axiom Applicable : LitexObject → List LitexObject → Prop"));
        assert!(prelude.contains("axiom add : LitexObject → LitexObject → LitexObject"));
        assert!(prelude.contains("theorem realSubClosure"));
        assert!(!prelude.contains("class LitexObject"));
        assert!(!prelude.contains("Set ℝ"));
        assert!(!prelude.contains("Set ℂ"));
    }
}
