import Mathlib

/- The same analytic-plane construction as `main.lit`.
Points have real coordinates, the equilateral vertex is explicitly constructed
with `Real.sqrt 3`, and both distance identities are proved. -/

namespace EuclideanGeometrySameMathInLean

abbrev Point := ℝ × ℝ

def vec (A B : Point) : Point := (B.1 - A.1, B.2 - A.2)
def dot (u v : Point) : ℝ := u.1 * v.1 + u.2 * v.2
def distanceSq (A B : Point) : ℝ := dot (vec A B) (vec A B)

theorem distanceSqCoordinateFormula (A B : Point) :
    distanceSq A B = (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 := by
  simp [distanceSq, dot, vec, pow_two]

def SegmentsCongruent (a b c d : Point) : Prop :=
  distanceSq a b = distanceSq c d

def IsEquilateralTriangle (a b c : Point) : Prop :=
  a ≠ b ∧ SegmentsCongruent a b a c ∧ SegmentsCongruent a b b c

noncomputable def equilateralVertex (a b : Point) : Point :=
  ((a.1 + b.1) / 2 - Real.sqrt 3 * (b.2 - a.2) / 2,
   (a.2 + b.2) / 2 + Real.sqrt 3 * (b.1 - a.1) / 2)

theorem equilateralRotationNorm (x y : ℝ) :
    (x / 2 - Real.sqrt 3 * y / 2) ^ 2 +
        (y / 2 + Real.sqrt 3 * x / 2) ^ 2 =
      x ^ 2 + y ^ 2 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  calc
    (x / 2 - Real.sqrt 3 * y / 2) ^ 2 +
        (y / 2 + Real.sqrt 3 * x / 2) ^ 2 =
      ((1 + (Real.sqrt 3) ^ 2) / 4) * (x ^ 2 + y ^ 2) := by ring
    _ = x ^ 2 + y ^ 2 := by rw [hsqrt]; ring

theorem equilateralVertexDistanceLemma (a b : Point) :
    distanceSq a (equilateralVertex a b) = distanceSq a b ∧
      distanceSq b (equilateralVertex a b) = distanceSq a b := by
  constructor
  · rw [distanceSqCoordinateFormula, distanceSqCoordinateFormula]
    unfold equilateralVertex
    simp only [Prod.fst, Prod.snd]
    convert equilateralRotationNorm (b.1 - a.1) (b.2 - a.2) using 1 <;> ring
  · rw [distanceSqCoordinateFormula, distanceSqCoordinateFormula]
    unfold equilateralVertex
    simp only [Prod.fst, Prod.snd]
    convert equilateralRotationNorm (a.1 - b.1) (b.2 - a.2) using 1 <;> ring

theorem euclidBook1Proposition1 {a b : Point} (hne : a ≠ b) :
    ∃ c, IsEquilateralTriangle a b c := by
  refine ⟨equilateralVertex a b, hne, ?_, ?_⟩
  · exact (equilateralVertexDistanceLemma a b).1.symm
  · exact (equilateralVertexDistanceLemma a b).2.symm

example : equilateralVertex (0, 0) (2, 0) = (1, Real.sqrt 3) := by
  simp [equilateralVertex]

end EuclideanGeometrySameMathInLean
