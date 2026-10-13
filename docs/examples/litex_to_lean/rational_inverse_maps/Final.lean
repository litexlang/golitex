import rational_inverse_maps.Adapter

namespace RationalMaps

theorem forwardPreservesDomain (x : ℚ) (hx : x ≠ 1) : forward x ≠ 2 := by
  exact Adapter.forwardPreservesDomain x hx

theorem backwardPreservesDomain (y : ℚ) (hy : y ≠ 2) : backward y ≠ 1 := by
  exact Adapter.backwardPreservesDomain y hy

theorem leftInverse (x : ℚ) (hx : x ≠ 1) : backward (forward x) = x := by
  exact Adapter.leftInverse x hx

theorem rightInverse (y : ℚ) (hy : y ≠ 2) : forward (backward y) = y := by
  exact Adapter.rightInverse y hy

theorem forwardInjective (a b : ℚ) (ha : a ≠ 1) (hb : b ≠ 1)
    (equal : forward a = forward b) : a = b := by
  exact Adapter.forwardInjective a b ha hb equal

def equivalence : {x : ℚ // x ≠ 1} ≃ {y : ℚ // y ≠ 2} where
  toFun x := ⟨forward x, forwardPreservesDomain x x.property⟩
  invFun y := ⟨backward y, backwardPreservesDomain y y.property⟩
  left_inv x := Subtype.ext (leftInverse x x.property)
  right_inv y := Subtype.ext (rightInverse y y.property)

end RationalMaps
