import Litex.NumericRules

namespace Litex.NativeBridge

universe u v w

variable {M : Semantics.{u}}

def numberInR (r : ℝ) : In (number (M := M) (r : ℂ)) R :=
  (M.real_members (M.number (r : ℂ))).mpr ⟨r, rfl⟩

theorem complexEq {z w : ℂ}
    (h : Same (number (M := M) z) (number w)) : z = w :=
  M.number_injective h

def numberNonzero (z : ℂ) (hz : z ≠ 0) :
    ¬ Same (number (M := M) z) (number 0) :=
  fun h => hz (complexEq h)

theorem addSame_iff (x y z : ℂ) :
    Same (add (number (M := M) x) (number y) (numberInC x) (numberInC y))
      (number z) ↔ x + y = z := by
  change M.addValue (M.number x) (M.number y) = M.number z ↔ x + y = z
  rw [M.add_numbers]
  exact M.number_injective.eq_iff

theorem divSame_iff (x y z : ℂ) (hy : y ≠ 0) :
    Same (div (number (M := M) x) (number y)
      (numberInC x) (numberInC y) (numberNonzero y hy))
      (number z) ↔ x / y = z := by
  change M.divValue (M.number x) (M.number y) = M.number z ↔ x / y = z
  rw [M.div_numbers x y hy]
  exact M.number_injective.eq_iff

noncomputable def asComplex {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) : ℂ :=
  Classical.choose ((M.complex_members (denote a)).mp haC)

theorem asComplex_spec {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) :
    denote a = M.number (asComplex a haC) :=
  Classical.choose_spec ((M.complex_members (denote a)).mp haC)

theorem asComplex_proofIndependent {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (h₁ h₂ : In a C) :
    asComplex a h₁ = asComplex a h₂ :=
  M.number_injective ((asComplex_spec a h₁).symm.trans (asComplex_spec a h₂))

theorem same_iff_asComplex {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) (hbC : In b C) :
    Same a b ↔ asComplex a haC = asComplex b hbC := by
  change denote a = denote b ↔ _
  rw [asComplex_spec a haC, asComplex_spec b hbC]
  exact M.number_injective.eq_iff

end Litex.NativeBridge
