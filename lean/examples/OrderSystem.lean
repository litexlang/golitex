import Litex.Rules

set_option linter.style.nameCheck false

namespace __OrderSystem01

/-!
Tracer source:

  forall a R, b R:
      a < b
      =>:
          a <= b

Compiler2 keeps the default numeric carrier `ℂ`.  Membership, strict order,
and non-strict order are separate Litex propositions over those same values.
-/

theorem __fact0 :
    ∀ (a : ℂ) (__h0_1 : Litex.In a Litex.R)
      (b : ℂ) (__h0_2 : Litex.In b Litex.R)
      (__h0_3 : Litex.Lt a b),
      Litex.Le a b := by
  intro a __h0_1 b __h0_2 __h0_3
  exact Litex.Lt.toLe __h0_3

/-- A Mathlib real comparison introduces the corresponding Litex comparison. -/
theorem __fact1 : Litex.Lt (2 : ℂ) (3 : ℂ) := by
  exact Litex.OrderBridge.ltOfComplexReals (by norm_num)

/-- Eliminating back to native Mathlib order is the point where uniqueness of
real representatives is required explicitly. -/
theorem __fact2 [Litex.RealCoherence] (r s : ℝ) :
    Litex.Lt r s ↔ r < s :=
  Litex.OrderBridge.real_lt_iff

#print axioms __fact0
#print axioms __fact1
#print axioms __fact2

end __OrderSystem01
