import Litex.Core

/-!
# Checked Litex builtin rules

This module proves concrete verifier rules from the shared `Litex.Core`
interpretation and Mathlib. Its declarations are ordinary Lean theorems, not
additional semantic axioms. See `lean/SEMANTIC_REFERENCE.md` for their
source-concept correspondence and exact trust boundary.
-/

namespace Litex.BuiltinRules

theorem notEqualSymmetry {a b : Object} (h : a ≠ b) : b ≠ a := by
  exact Ne.symm h

theorem numeralInN (n : Nat) : In (OfNat.ofNat n : Object) N := by
  apply inN_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInNPos (n : Nat) (positive : 0 < n) :
    In (OfNat.ofNat n : Object) NPos := by
  apply inNPos_iff.mpr
  exact ⟨n, positive, rfl⟩

theorem numeralInZ (n : Nat) : In (OfNat.ofNat n : Object) Z := by
  apply inZ_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInQ (n : Nat) : In (OfNat.ofNat n : Object) Q := by
  apply inQ_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInR (n : Nat) : In (OfNat.ofNat n : Object) R := by
  apply inR_iff.mpr
  exact ⟨n, rfl⟩

theorem numeralInC (n : Nat) : In (OfNat.ofNat n : Object) C := by
  apply inC_iff.mpr
  exact ⟨n, rfl⟩

theorem realSetNonempty : IsNonemptySet R := by
  exact ⟨0, numeralInR 0⟩

theorem objectIsSet (x : Object) : IsSet x := by
  exact everyObjectIsSet x

theorem numeralLt (m n : Nat) :
    Litex.Lt (OfNat.ofNat m : Object) (OfNat.ofNat n : Object) ↔ m < n := by
  rw [show (OfNat.ofNat m : Object) = embedComplex ((m : ℝ) : ℂ) by
    simp [OfNat.ofNat]]
  rw [show (OfNat.ofNat n : Object) = embedComplex ((n : ℝ) : ℂ) by
    simp [OfNat.ofNat]]
  rw [lt_embedReal]
  norm_num

theorem numeralLe (m n : Nat) :
    Litex.Le (OfNat.ofNat m : Object) (OfNat.ofNat n : Object) ↔ m ≤ n := by
  rw [show (OfNat.ofNat m : Object) = embedComplex ((m : ℝ) : ℂ) by
    simp [OfNat.ofNat]]
  rw [show (OfNat.ofNat n : Object) = embedComplex ((n : ℝ) : ℂ) by
    simp [OfNat.ofNat]]
  rw [le_embedReal]
  norm_num

theorem positiveRealMembership {x : Object} (h : In x RPos) : Lt 0 x := by
  rcases inRPos_iff.mp h with ⟨r, hr, rfl⟩
  rw [show (0 : Object) = embedComplex ((0 : ℝ) : ℂ) by
    simp only [OfNat.ofNat]
    congr 1
    norm_num]
  exact (lt_embedReal 0 r).mpr hr

theorem naturalInInteger {x : Object} (h : In x N) : In x Z := by
  rcases inN_iff.mp h with ⟨n, rfl⟩
  apply inZ_iff.mpr
  refine ⟨(n : ℤ), ?_⟩
  simp

theorem integerInRational {x : Object} (h : In x Z) : In x Q := by
  rcases inZ_iff.mp h with ⟨z, rfl⟩
  apply inQ_iff.mpr
  refine ⟨(z : ℚ), ?_⟩
  simp

theorem rationalInReal {x : Object} (h : In x Q) : In x R := by
  rcases inQ_iff.mp h with ⟨q, rfl⟩
  apply inR_iff.mpr
  refine ⟨(q : ℝ), ?_⟩
  simp

theorem realInComplex {x : Object} (h : In x R) : In x C := by
  rcases inR_iff.mp h with ⟨r, rfl⟩
  apply inC_iff.mpr
  exact ⟨r, rfl⟩

theorem complexAddClosure {a b : Object} (ha : In a C) (hb : In b C) :
    In (Litex.add a b ha hb) C := by
  rcases inC_iff.mp ha with ⟨a, rfl⟩
  rcases inC_iff.mp hb with ⟨b, rfl⟩
  apply inC_iff.mpr
  refine ⟨a + b, ?_⟩
  simp

theorem complexSubClosure {a b : Object} (ha : In a C) (hb : In b C) :
    In (Litex.sub a b ha hb) C := by
  rcases inC_iff.mp ha with ⟨a, rfl⟩
  rcases inC_iff.mp hb with ⟨b, rfl⟩
  apply inC_iff.mpr
  refine ⟨a - b, ?_⟩
  simp

theorem complexMulClosure {a b : Object} (ha : In a C) (hb : In b C) :
    In (Litex.mul a b ha hb) C := by
  rcases inC_iff.mp ha with ⟨a, rfl⟩
  rcases inC_iff.mp hb with ⟨b, rfl⟩
  apply inC_iff.mpr
  refine ⟨a * b, ?_⟩
  simp

theorem complexDivClosure {a b : Object}
    (ha : In a C) (hb : In b C) (hb0 : b ≠ 0) :
    In (Litex.div a b ha hb hb0) C := by
  rcases inC_iff.mp ha with ⟨a, rfl⟩
  rcases inC_iff.mp hb with ⟨b, rfl⟩
  apply inC_iff.mpr
  refine ⟨a / b, ?_⟩
  simp

theorem realAddClosure {a b : Object}
    (haC : In a C) (hbC : In b C) (ha : In a R) (hb : In b R) :
    In (Litex.add a b haC hbC) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a + b, ?_⟩
  simp

theorem realSubClosure {a b : Object}
    (haC : In a C) (hbC : In b C) (ha : In a R) (hb : In b R) :
    In (Litex.sub a b haC hbC) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a - b, ?_⟩
  simp

theorem realMulClosure {a b : Object}
    (haC : In a C) (hbC : In b C) (ha : In a R) (hb : In b R) :
    In (Litex.mul a b haC hbC) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a * b, ?_⟩
  simp

theorem realDivClosure {a b : Object}
    (haC : In a C) (hbC : In b C) (hb0 : b ≠ 0)
    (ha : In a R) (hb : In b R) :
    In (div a b haC hbC hb0) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a / b, ?_⟩
  simp

end Litex.BuiltinRules
