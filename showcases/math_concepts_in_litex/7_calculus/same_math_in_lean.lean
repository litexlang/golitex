import Mathlib

/- The same real epsilon-delta calculus as `main.lit`.
No derivative law is assumed: the difference quotients and bounds are proved
from the definitions over `ℝ`. -/

namespace CalculusSameMathInLean

def DerivativeDeltaControlled (f : ℝ → ℝ)
    (x₀ L ε δ : ℝ) : Prop :=
  ∀ x, x ≠ x₀ → |x - x₀| < δ →
    |(f x - f x₀) / (x - x₀) - L| < ε

def HasDerivativeAt (f : ℝ → ℝ) (x₀ L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, DerivativeDeltaControlled f x₀ L ε δ

def IsDifferentiableAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ L, HasDerivativeAt f x₀ L

def squareFunction (x : ℝ) : ℝ := x ^ 2

theorem squareDifferenceQuotient (x₀ x : ℝ) (hne : x ≠ x₀) :
    (squareFunction x - squareFunction x₀) / (x - x₀) = x + x₀ := by
  have hsub : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
  unfold squareFunction
  field_simp [hsub]
  ring

theorem squareFunctionHasDerivativeAt (x₀ : ℝ) :
    HasDerivativeAt squareFunction x₀ (2 * x₀) := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hne hclose
  rw [squareDifferenceQuotient x₀ x hne]
  convert hclose using 1 <;> ring

theorem squareFunctionHasMathlibDerivative (x₀ : ℝ) :
    HasDerivAt squareFunction (2 * x₀) x₀ := by
  simpa [squareFunction, two_mul] using
    (hasDerivAt_pow 2 x₀)

theorem derivativeCandidateImpliesDifferentiable
    {f : ℝ → ℝ} {x₀ L : ℝ} (h : HasDerivativeAt f x₀ L) :
    IsDifferentiableAt f x₀ :=
  ⟨L, h⟩

def affineFunction (a b x : ℝ) : ℝ := a * x + b

theorem affineDifferenceQuotient (a b x₀ x : ℝ) (hne : x ≠ x₀) :
    (affineFunction a b x - affineFunction a b x₀) / (x - x₀) = a := by
  have hsub : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
  unfold affineFunction
  field_simp [hsub]
  ring

theorem affineFunctionHasDerivativeAt (a b x₀ : ℝ) :
    HasDerivativeAt (affineFunction a b) x₀ a := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro x hne _
  rw [affineDifferenceQuotient a b x₀ x hne]
  simpa using hε

def squareTangentAtThree (x : ℝ) : ℝ := 9 + 6 * (x - 3)

theorem squareTangentErrorAtThree (x : ℝ) :
    squareFunction x - squareTangentAtThree x = (x - 3) ^ 2 := by
  simp [squareFunction, squareTangentAtThree]
  ring

end CalculusSameMathInLean
