/-
Pure Lean 4 analogy for `main.lit`.

Lean's Prelude has no real numbers, absolute value, division, or ordered-field
library. Those operations and the two algebraic identities used by the proof
are therefore explicit setting fields. The epsilon-delta witness construction
itself is checked by Lean core. This is handwritten comparison code, not
compiler output.
-/

universe u

namespace CalculusCoreAnalogy

structure RealCalculusSetting (R : Type u) where
  sub : R → R → R
  div : R → R → R
  abs : R → R
  lt : R → R → Prop
  positive : R → Prop
  square : R → R
  add : R → R → R
  double : R → R
  square_difference_quotient : ∀ x x0, x ≠ x0 →
    div (sub (square x) (square x0)) (sub x x0) = add x x0
  square_error : ∀ x x0, sub (add x x0) (double x0) = sub x x0

def DerivativeDeltaControlled (S : RealCalculusSetting R)
    (f : R → R) (x0 L epsilon delta : R) : Prop :=
  ∀ x, x ≠ x0 → S.lt (S.abs (S.sub x x0)) delta →
    S.lt
      (S.abs
        (S.sub
          (S.div (S.sub (f x) (f x0)) (S.sub x x0))
          L))
      epsilon

def HasDerivativeAt (S : RealCalculusSetting R)
    (f : R → R) (x0 L : R) : Prop :=
  ∀ epsilon, S.positive epsilon →
    ∃ delta, S.positive delta ∧
      DerivativeDeltaControlled S f x0 L epsilon delta

def IsDifferentiableAt (S : RealCalculusSetting R)
    (f : R → R) (x0 : R) : Prop :=
  ∃ L, HasDerivativeAt S f x0 L

theorem square_function_has_derivative_at (S : RealCalculusSetting R)
    (x0 : R) : HasDerivativeAt S S.square x0 (S.double x0) := by
  intro epsilon epsilon_positive
  refine ⟨epsilon, epsilon_positive, ?_⟩
  intro x hne hclose
  change S.lt
    (S.abs
      (S.sub
        (S.div (S.sub (S.square x) (S.square x0)) (S.sub x x0))
        (S.double x0)))
    epsilon
  rw [S.square_difference_quotient x x0 hne, S.square_error x x0]
  exact hclose

theorem derivative_candidate_implies_differentiable
    (S : RealCalculusSetting R) {f : R → R} {x0 L : R}
    (candidate : HasDerivativeAt S f x0 L) :
    IsDifferentiableAt S f x0 :=
  ⟨L, candidate⟩

theorem square_function_is_differentiable_at
    (S : RealCalculusSetting R) (x0 : R) :
    IsDifferentiableAt S S.square x0 :=
  derivative_candidate_implies_differentiable S
    (square_function_has_derivative_at S x0)

structure AffineCalculusSetting (R : Type u) extends RealCalculusSetting R where
  zero : R
  one : R
  one_positive : positive one
  affine : R → R → R → R
  affine_difference_quotient : ∀ slope intercept x x0, x ≠ x0 →
    div (sub (affine slope intercept x) (affine slope intercept x0))
      (sub x x0) = slope
  affine_error : ∀ slope, sub slope slope = zero
  abs_zero_lt_positive : ∀ epsilon, positive epsilon → lt (abs zero) epsilon

theorem affine_function_has_derivative_at
    (S : AffineCalculusSetting R) (slope intercept x0 : R) :
    HasDerivativeAt S.toRealCalculusSetting (S.affine slope intercept) x0 slope := by
  intro epsilon epsilon_positive
  refine ⟨S.one, S.one_positive, ?_⟩
  intro x hne _hclose
  change S.lt
    (S.abs
      (S.sub
        (S.div
          (S.sub (S.affine slope intercept x) (S.affine slope intercept x0))
          (S.sub x x0))
        slope))
    epsilon
  rw [S.affine_difference_quotient slope intercept x x0 hne,
    S.affine_error slope]
  exact S.abs_zero_lt_positive epsilon epsilon_positive

structure SquareTangentAtThreeSetting
    (S : RealCalculusSetting R) where
  three : R
  tangent : R → R
  exact_remainder : ∀ x,
    S.sub (S.square x) (tangent x) = S.square (S.sub x three)

theorem square_tangent_error_at_three
    (S : RealCalculusSetting R) (T : SquareTangentAtThreeSetting S) (x : R) :
    S.sub (S.square x) (T.tangent x) = S.square (S.sub x T.three) :=
  T.exact_remainder x

end CalculusCoreAnalogy
