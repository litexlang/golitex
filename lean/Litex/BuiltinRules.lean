import Litex.Core

namespace Litex.BuiltinRules

theorem notEqualSymmetry {a b : Object} (h : a ≠ b) : b ≠ a := by
  exact Ne.symm h

theorem numeralInN (n : Nat) : In (OfNat.ofNat n : Object) N := by
  apply inN_iff.mpr
  exact ⟨n, rfl⟩

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

theorem realAddClosure {a b : Object} (ha : In a R) (hb : In b R) :
    In (add a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a + b, ?_⟩
  simp

theorem realSubClosure {a b : Object} (ha : In a R) (hb : In b R) :
    In (sub a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a - b, ?_⟩
  simp

theorem realMulClosure {a b : Object} (ha : In a R) (hb : In b R) :
    In (mul a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a * b, ?_⟩
  simp

theorem realDivClosure {a b : Object} (ha : In a R) (hb : In b R) :
    In (div a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a / b, ?_⟩
  simp

end Litex.BuiltinRules
