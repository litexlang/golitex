import Mathlib

/-!
The same real-variable mathematics as `main.lit`, written directly in Lean.

The first derivative predicate is the punctured epsilon-delta definition used
by the Litex source. The proof of the quadratic derivative expands and cancels
the difference quotient; it is not supplied as an assumption. A second theorem
records the same derivative with Mathlib's standard `HasDerivAt` interface.
-/

namespace OrdinaryDifferentialEquationsSameMathInLean

def quadraticSolution (c x : ℝ) : ℝ := x ^ 2 + c
def odeSolution (x : ℝ) : ℝ := quadraticSolution 1 x
def odeRhs (x _y : ℝ) : ℝ := 2 * x

def DerivativeDeltaControlled (f : ℝ → ℝ)
    (x₀ slope ε δ : ℝ) : Prop :=
  ∀ x : ℝ, x ≠ x₀ → |x - x₀| < δ →
    |(f x - f x₀) / (x - x₀) - slope| < ε

def HasDerivativeAt (f : ℝ → ℝ) (x₀ slope : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ DerivativeDeltaControlled f x₀ slope ε δ

def IsDifferentiableAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ slope, HasDerivativeAt f x₀ slope

def SolvesAt (f : ℝ → ℝ) (rhs : ℝ → ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ slope : ℝ, HasDerivativeAt f x slope ∧ slope = rhs x (f x)

theorem quadraticInitialValueSelectsParameter (c y₀ : ℝ)
    (initialValue : quadraticSolution c 0 = y₀) : c = y₀ := by
  simpa [quadraticSolution] using initialValue

theorem odeSolutionHasDerivative (x₀ : ℝ) :
    HasDerivativeAt odeSolution x₀ (2 * x₀) := by
  intro ε εPositive
  refine ⟨ε, εPositive, ?_⟩
  intro x xNe hClose
  have differenceNe : x - x₀ ≠ 0 := sub_ne_zero.mpr xNe
  have quotientError :
      (odeSolution x - odeSolution x₀) / (x - x₀) - 2 * x₀ = x - x₀ := by
    simp only [odeSolution, quadraticSolution]
    field_simp [differenceNe]
    ring
  rw [quotientError]
  exact hClose

theorem derivativeValueUnique {f : ℝ → ℝ} {x₀ slope₁ slope₂ : ℝ}
    (h₁ : HasDerivativeAt f x₀ slope₁)
    (h₂ : HasDerivativeAt f x₀ slope₂) : slope₁ = slope₂ := by
  by_contra hne
  have hdistance : 0 < |slope₁ - slope₂| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  let ε := |slope₁ - slope₂| / 3
  have hε : 0 < ε := div_pos hdistance (by norm_num)
  obtain ⟨δ₁, hδ₁, controlled₁⟩ := h₁ ε hε
  obtain ⟨δ₂, hδ₂, controlled₂⟩ := h₂ ε hε
  let δ := min δ₁ δ₂ / 2
  have hδ : 0 < δ := div_pos (lt_min hδ₁ hδ₂) (by norm_num)
  let sample := x₀ + δ
  have sampleNe : sample ≠ x₀ := by
    dsimp [sample]
    linarith
  have sampleDistance : |sample - x₀| = δ := by
    rw [abs_of_pos]
    · dsimp [sample]
      ring
    · dsimp [sample]
      linarith
  have close₁ : |sample - x₀| < δ₁ := by
    rw [sampleDistance]
    dsimp [δ]
    have := min_le_left δ₁ δ₂
    linarith
  have close₂ : |sample - x₀| < δ₂ := by
    rw [sampleDistance]
    dsimp [δ]
    have := min_le_right δ₁ δ₂
    linarith
  let quotient := (f sample - f x₀) / (sample - x₀)
  have approximation₁ : |quotient - slope₁| < ε :=
    controlled₁ sample sampleNe close₁
  have approximation₂ : |quotient - slope₂| < ε :=
    controlled₂ sample sampleNe close₂
  have triangle :
      |slope₁ - slope₂| ≤
        |quotient - slope₁| + |quotient - slope₂| := by
    calc
      |slope₁ - slope₂| =
          |(slope₁ - quotient) + (quotient - slope₂)| := by ring_nf
      _ ≤ |slope₁ - quotient| + |quotient - slope₂| := abs_add_le _ _
      _ = |quotient - slope₁| + |quotient - slope₂| := by
        rw [abs_sub_comm slope₁]
  dsimp [ε] at approximation₁ approximation₂
  linarith

noncomputable def derivativeAt (f : ℝ → ℝ) (x₀ : ℝ)
    (h : IsDifferentiableAt f x₀) : ℝ :=
  Classical.choose h

theorem derivativeAtHasDerivative (f : ℝ → ℝ) (x₀ : ℝ)
    (h : IsDifferentiableAt f x₀) :
    HasDerivativeAt f x₀ (derivativeAt f x₀ h) :=
  Classical.choose_spec h

theorem hasDerivativeAtToDerivativeValue {f : ℝ → ℝ} {x₀ slope : ℝ}
    (h : HasDerivativeAt f x₀ slope) :
    let differentiable : IsDifferentiableAt f x₀ := ⟨slope, h⟩
    derivativeAt f x₀ differentiable = slope := by
  dsimp
  exact derivativeValueUnique (derivativeAtHasDerivative f x₀ ⟨slope, h⟩) h

def SolvesAtByDerivative (f : ℝ → ℝ) (rhs : ℝ → ℝ → ℝ)
    (x : ℝ) : Prop :=
  ∃ h : IsDifferentiableAt f x, derivativeAt f x h = rhs x (f x)

theorem odeSolutionHasMathlibDerivative (x : ℝ) :
    HasDerivAt odeSolution (2 * x) x := by
  change HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x
  simpa only [id_eq, Nat.reduceSub, pow_one, mul_one] using
    ((hasDerivAt_id x).pow 2).add_const (1 : ℝ)

theorem odeSolutionSolvesEquation (x : ℝ) :
    SolvesAt odeSolution odeRhs x := by
  refine ⟨2 * x, odeSolutionHasDerivative x, ?_⟩
  rfl

theorem odeSolutionDerivativeValue (x : ℝ) :
    let differentiable : IsDifferentiableAt odeSolution x :=
      ⟨2 * x, odeSolutionHasDerivative x⟩
    derivativeAt odeSolution x differentiable = 2 * x :=
  hasDerivativeAtToDerivativeValue (odeSolutionHasDerivative x)

theorem odeSolutionSolvesEquationByDerivative (x : ℝ) :
    SolvesAtByDerivative odeSolution odeRhs x := by
  let differentiable : IsDifferentiableAt odeSolution x :=
    ⟨2 * x, odeSolutionHasDerivative x⟩
  refine ⟨differentiable, ?_⟩
  calc
    derivativeAt odeSolution x differentiable = 2 * x :=
      hasDerivativeAtToDerivativeValue (odeSolutionHasDerivative x)
    _ = odeRhs x (odeSolution x) := rfl

example : odeSolution 0 = 1 := by
  norm_num [odeSolution, quadraticSolution]

example : quadraticSolution 1 0 = 1 := by
  norm_num [quadraticSolution]

end OrdinaryDifferentialEquationsSameMathInLean
