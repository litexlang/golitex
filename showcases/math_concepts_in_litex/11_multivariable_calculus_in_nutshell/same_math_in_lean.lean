import Mathlib

/- The same real coordinate-partial-derivative development as `main.lit`.
The surface lives on `ℝ × ℝ`; both partial derivatives are proved directly
from their epsilon-delta definitions. -/

namespace MultivariableCalculusSameMathInLean

abbrev Point := ℝ × ℝ

def quadraticSurface (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
def quadraticGradient (p : Point) : Point := (2 * p.1, 2 * p.2)

theorem xDifferenceQuotient (p : Point) (x : ℝ) (hne : x ≠ p.1) :
    (quadraticSurface (x, p.2) - quadraticSurface p) / (x - p.1) =
      x + p.1 := by
  have hsub : x - p.1 ≠ 0 := sub_ne_zero.mpr hne
  unfold quadraticSurface
  field_simp [hsub]
  ring

theorem yDifferenceQuotient (p : Point) (y : ℝ) (hne : y ≠ p.2) :
    (quadraticSurface (p.1, y) - quadraticSurface p) / (y - p.2) =
      y + p.2 := by
  have hsub : y - p.2 ≠ 0 := sub_ne_zero.mpr hne
  unfold quadraticSurface
  field_simp [hsub]
  ring

def XPartialDeltaControlled (f : Point → ℝ) (p : Point)
    (slope ε δ : ℝ) : Prop :=
  ∀ x, x ≠ p.1 → |x - p.1| < δ →
    |(f (x, p.2) - f p) / (x - p.1) - slope| < ε

def HasXPartialDerivativeAt (f : Point → ℝ) (p : Point)
    (slope : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, XPartialDeltaControlled f p slope ε δ

def YPartialDeltaControlled (f : Point → ℝ) (p : Point)
    (slope ε δ : ℝ) : Prop :=
  ∀ y, y ≠ p.2 → |y - p.2| < δ →
    |(f (p.1, y) - f p) / (y - p.2) - slope| < ε

def HasYPartialDerivativeAt (f : Point → ℝ) (p : Point)
    (slope : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, YPartialDeltaControlled f p slope ε δ

theorem quadraticSurfaceHasXPartialDerivative (p : Point) :
    HasXPartialDerivativeAt quadraticSurface p (2 * p.1) := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x hne hclose
  rw [xDifferenceQuotient p x hne]
  convert hclose using 1 <;> ring

theorem quadraticSurfaceHasYPartialDerivative (p : Point) :
    HasYPartialDerivativeAt quadraticSurface p (2 * p.2) := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hne hclose
  rw [yDifferenceQuotient p y hne]
  convert hclose using 1 <;> ring

def IsCoordinateGradientAt (f : Point → ℝ) (p gradient : Point) : Prop :=
  HasXPartialDerivativeAt f p gradient.1 ∧
    HasYPartialDerivativeAt f p gradient.2

theorem quadraticGradientIsCoordinateGradient (p : Point) :
    IsCoordinateGradientAt quadraticSurface p (quadraticGradient p) := by
  exact ⟨quadraticSurfaceHasXPartialDerivative p,
    quadraticSurfaceHasYPartialDerivative p⟩

theorem quadraticSurfaceHasMathlibCoordinateDerivatives (p : Point) :
    HasDerivAt (fun x => quadraticSurface (x, p.2)) (2 * p.1) p.1 ∧
      HasDerivAt (fun y => quadraticSurface (p.1, y)) (2 * p.2) p.2 := by
  constructor
  · simpa [quadraticSurface, two_mul] using
      (hasDerivAt_pow 2 p.1).add_const (p.2 ^ 2)
  · simpa [quadraticSurface, two_mul, add_comm] using
      (hasDerivAt_pow 2 p.2).const_add (p.1 ^ 2)

example : quadraticGradient (3, 4) = (6, 8) := by norm_num [quadraticGradient]

end MultivariableCalculusSameMathInLean
