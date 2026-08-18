import Mathlib

/- The same real epsilon-tail definitions as `main.lit`.
Closeness is `|a n - L| < ε`; limit uniqueness is proved from the triangle
inequality instead of being supplied as a setting axiom. -/

namespace RealAnalysisSameMathInLean

def IsTailCloseTo (a : ℕ → ℝ) (L ε : ℝ) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → |a n - L| < ε

def HasEventualClosenessTo (a : ℕ → ℝ) (L ε : ℝ) : Prop :=
  ∃ N, IsTailCloseTo a L ε N

def HasLimit (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, HasEventualClosenessTo a L ε

def Convergent (a : ℕ → ℝ) : Prop := ∃ L, HasLimit a L

theorem constantSequenceHasLimit (c : ℝ) :
    HasLimit (fun _ => c) c := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro n _
  simpa using hε

theorem sequenceLimitUnique {a : ℕ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : HasLimit a L₁) (h₂ : HasLimit a L₂) : L₁ = L₂ := by
  by_contra hne
  have hdist : 0 < |L₁ - L₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
  let ε : ℝ := |L₁ - L₂| / 3
  have hε : 0 < ε := div_pos hdist (by norm_num)
  obtain ⟨N₁, hN₁⟩ := h₁ ε hε
  obtain ⟨N₂, hN₂⟩ := h₂ ε hε
  let N := max N₁ N₂
  have hclose₁ := hN₁ N (Nat.le_max_left _ _)
  have hclose₂ := hN₂ N (Nat.le_max_right _ _)
  have htriangle :
      |L₁ - L₂| ≤ |a N - L₁| + |a N - L₂| := by
    calc
      |L₁ - L₂| = |(L₁ - a N) + (a N - L₂)| := by ring_nf
      _ ≤ |L₁ - a N| + |a N - L₂| := abs_add_le _ _
      _ = |a N - L₁| + |a N - L₂| := by rw [abs_sub_comm L₁]
  dsimp [ε] at hclose₁ hclose₂
  linarith

noncomputable def lim (a : ℕ → ℝ) (h : Convergent a) : ℝ :=
  Classical.choose h

theorem selectedLimitHasLimit (a : ℕ → ℝ) (h : Convergent a) :
    HasLimit a (lim a h) :=
  Classical.choose_spec h

end RealAnalysisSameMathInLean
