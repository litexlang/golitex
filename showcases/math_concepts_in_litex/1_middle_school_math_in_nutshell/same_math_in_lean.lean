import Mathlib

/- The same real-number mathematics as `main.lit`.
The linear equation and AM-GM theorem are proved over `ℝ`; square root,
finite-cardinality probability, and division keep their ordinary meanings. -/

namespace MiddleSchoolMathInNutshell

example : Nat.gcd 84 30 = 6 := by decide

theorem solveLinearEquation {a b c x : ℝ}
    (ha : a ≠ 0) (h : a * x + b = c) :
    x = (c - b) / a := by
  apply (eq_div_iff ha).2
  linarith

theorem factoredQuadraticRoots {r s x : ℝ}
    (h : (x - r) * (x - s) = 0) : x = r ∨ x = s := by
  rcases mul_eq_zero.mp h with hxr | hxs
  · exact Or.inl (sub_eq_zero.mp hxr)
  · exact Or.inr (sub_eq_zero.mp hxs)

noncomputable def arithmeticMean (x y : ℝ) : ℝ := (x + y) / 2
noncomputable def geometricMean (x y : ℝ) : ℝ := Real.sqrt (x * y)

theorem twoVariableAmGm {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    geometricMean x y ≤ arithmeticMean x y := by
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hsqrt : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (x * y)) ^ 2 = x * y :=
    Real.sq_sqrt hxy
  have hsum : 0 ≤ x + y := add_nonneg hx hy
  have hsquare : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  unfold geometricMean arithmeticMean
  nlinarith

def linearFunction (x : ℝ) : ℝ := 3 * x + 2

example : linearFunction 4 = 14 := by norm_num [linearFunction]
example : linearFunction (-1) = -1 := by norm_num [linearFunction]

def arithmeticTerm (first difference : ℝ) (n : ℕ) : ℝ :=
  first + ((n : ℝ) - 1) * difference

example : arithmeticTerm 2 3 1 = 2 := by norm_num [arithmeticTerm]
example : arithmeticTerm 2 3 4 = 11 := by norm_num [arithmeticTerm]

abbrev Point := ℝ × ℝ

def distanceSq (p q : Point) : ℝ :=
  (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2

example : distanceSq (0, 0) (3, 4) = 25 := by norm_num [distanceSq]
example : (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 := by norm_num

noncomputable def uniformProbability (S A : Finset ℕ) : ℝ :=
  (A.card : ℝ) / S.card

example :
    uniformProbability {1, 2, 3, 4, 5, 6} {2, 4, 6} = 1 / 2 := by
  norm_num [uniformProbability]

noncomputable def mean3 (a b c : ℝ) : ℝ := (a + b + c) / 3
def range3 (minimum maximum : ℝ) : ℝ := maximum - minimum

example : mean3 2 4 6 = 4 := by norm_num [mean3]
example : range3 2 6 = 4 := by norm_num [range3]

end MiddleSchoolMathInNutshell
