import Final

namespace UserTheorems

/-- Use the exported theorem as an ordinary lemma in a larger Lean proof. -/
theorem threeTerms (x y t z : ℝ) (hz : z ≠ 0) :
    (x + y + t) / z = x / z + y / z + t / z := by
  calc
    (x + y + t) / z = (x + y) / z + t / z :=
      LitexLeanExample.quotientDistributes (x + y) t z hz
    _ = x / z + y / z + t / z := by
      rw [LitexLeanExample.quotientDistributes x y z hz]

/-- Consume the compiler-backed involution as an ordinary native lemma. -/
theorem applyMobiusTwice (x : ℝ) (hx : x ≠ 1) :
    LitexLeanExample.mobius (LitexLeanExample.mobius x) = x := by
  exact (LitexLeanExample.mobiusInvolution x hx).2

end UserTheorems
