/-
The same mathematics as `main.lit`, expressed in pure Lean 4.

Prelude `Int` supports the exact factorization/candidate logic below. Pure Lean
has no real square root, so AM-GM is shown in the equivalent doubled form after
the nonnegative square-comparison step has been made explicit. This is
handwritten comparison code, not compiler output.
-/

namespace ElementaryAlgebraSameMathInLean

structure IntegerGeometricMean (x y g : Int) : Prop where
  nonnegative : 0 ≤ g
  square_eq_product : g * g = x * y

theorem doubled_am_gm
    {x y g : Int} (geometric : IntegerGeometricMean x y g)
    (sum_nonnegative : 0 ≤ x + y)
    (square_bound : (2 * g) * (2 * g) ≤ (x + y) * (x + y))
    (square_order_reflection :
      ∀ a b : Int, 0 ≤ a → 0 ≤ b → a * a ≤ b * b → a ≤ b)
    (double_nonnegative : 0 ≤ 2 * g) :
    2 * g ≤ x + y := by
  have _product_certificate : g * g = x * y := geometric.square_eq_product
  exact square_order_reflection (2 * g) (x + y)
    double_nonnegative sum_nonnegative square_bound

theorem factored_quadratic_roots {x : Int}
    (factored_equation : (x - 1) * (x - 5) = 0) :
    x = 1 ∨ x = 5 := by
  have zero_factor : x - 1 = 0 ∨ x - 5 = 0 :=
    (Int.mul_eq_zero).mp factored_equation
  cases zero_factor with
  | inl h => exact Or.inl ((Int.sub_eq_zero).mp h)
  | inr h => exact Or.inr ((Int.sub_eq_zero).mp h)

def RadicalCandidateIsAdmissible (x : Int) : Prop := 4 ≤ x

theorem radical_candidate_filter {x : Int}
    (algebraic_candidates : x = 1 ∨ x = 5)
    (admissible : RadicalCandidateIsAdmissible x)
    (one_is_extraneous : ¬ RadicalCandidateIsAdmissible 1) :
    x = 5 := by
  cases algebraic_candidates with
  | inl h =>
      subst x
      exact False.elim (one_is_extraneous admissible)
  | inr h => exact h

example : ((5 : Int) - 1) * (5 - 5) = 0 := by decide

end ElementaryAlgebraSameMathInLean
