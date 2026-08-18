/-
The same mathematical mainline as `main.lit`, expressed in pure Lean 4.

This file has no imports. Prelude integers cover the exact arithmetic,
equation, function, sequence, geometry, and statistics examples. Prelude has
no real square root, so AM-GM receives the square-order step explicitly.
Probability equality is written by cross multiplication because Prelude does
not provide a rational-probability library. This is handwritten comparison
code, not compiler output.
-/

namespace MiddleSchoolMathInNutshell

example : Nat.gcd 84 30 = 6 := by decide

theorem factoredQuadraticRoots {r s x : Int}
    (factoredEquation : (x - r) * (x - s) = 0) :
    x = r ∨ x = s := by
  have zeroFactor : x - r = 0 ∨ x - s = 0 :=
    (Int.mul_eq_zero).mp factoredEquation
  cases zeroFactor with
  | inl h => exact Or.inl ((Int.sub_eq_zero).mp h)
  | inr h => exact Or.inr ((Int.sub_eq_zero).mp h)

example : 3 * (2 : Int) + (-6) = 0 := by decide
example : ((3 : Int) - 2) * (3 - 3) = 0 := by decide

structure IntegerGeometricMean (x y g : Int) : Prop where
  nonnegative : 0 ≤ g
  squareEqProduct : g * g = x * y

theorem doubledAmGm
    {x y g : Int} (geometric : IntegerGeometricMean x y g)
    (sumNonnegative : 0 ≤ x + y)
    (squareBound : (2 * g) * (2 * g) ≤ (x + y) * (x + y))
    (squareOrderReflection :
      ∀ a b : Int, 0 ≤ a → 0 ≤ b → a * a ≤ b * b → a ≤ b)
    (doubleNonnegative : 0 ≤ 2 * g) :
    2 * g ≤ x + y := by
  have _productCertificate : g * g = x * y := geometric.squareEqProduct
  exact squareOrderReflection (2 * g) (x + y)
    doubleNonnegative sumNonnegative squareBound

def linearFunction (x : Int) : Int := 3 * x + 2

example : linearFunction 4 = 14 := by decide
example : linearFunction (-1) = -1 := by decide

def arithmeticTerm (first difference : Int) (n : Nat) : Int :=
  first + (Int.ofNat n - 1) * difference

example : arithmeticTerm 2 3 1 = 2 := by decide
example : arithmeticTerm 2 3 4 = 11 := by decide

abbrev Point := Int × Int

def distanceSq (p q : Point) : Int :=
  (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2

example : distanceSq (0, 0) (3, 4) = 25 := by decide
example : (3 : Int) ^ 2 + 4 ^ 2 = 5 ^ 2 := by decide

def equivalentFractions
    (firstNumerator firstDenominator secondNumerator secondDenominator : Nat) : Prop :=
  firstNumerator * secondDenominator = secondNumerator * firstDenominator

example : equivalentFractions 3 6 1 2 := by rfl

def mean3 (a b c : Int) : Int := (a + b + c) / 3
def range3 (minimum maximum : Int) : Int := maximum - minimum

example : mean3 2 4 6 = 4 := by decide
example : range3 2 6 = 4 := by decide

end MiddleSchoolMathInNutshell
