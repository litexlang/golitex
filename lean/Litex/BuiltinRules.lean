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

theorem realDivClosure {a b : Object} (ha : In a R) (hb : In b R) :
    In (div a b) R := by
  rcases inR_iff.mp ha with ⟨a, rfl⟩
  rcases inR_iff.mp hb with ⟨b, rfl⟩
  apply inR_iff.mpr
  refine ⟨a / b, ?_⟩
  simp

end Litex.BuiltinRules
