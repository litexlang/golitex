import rational_inverse_maps.Final

namespace CompilerDocClient

/-- The native Equiv supplies the round-trip law directly. -/
theorem inverseRoundTrip (x : {q : ℚ // q ≠ 1}) :
    RationalMaps.equivalence.symm (RationalMaps.equivalence x) = x := by
  exact RationalMaps.equivalence.symm_apply_apply x

/-- The native Equiv is injective; no rational normalization is needed here. -/
theorem differentInputsStayDifferent (x y : {q : ℚ // q ≠ 1}) (h : x ≠ y) :
    RationalMaps.equivalence x ≠ RationalMaps.equivalence y := by
  intro equal
  exact h (RationalMaps.equivalence.injective equal)

/-- Evaluate the computable forward map at one legal input. -/
theorem forwardAtZero :
    (RationalMaps.equivalence ⟨0, by norm_num⟩).val = (-1 : ℚ) := by
  change RationalMaps.forward 0 = -1
  norm_num [RationalMaps.forward]

end CompilerDocClient
