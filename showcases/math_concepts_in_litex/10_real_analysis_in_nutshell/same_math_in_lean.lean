/- Prelude has no real numbers, absolute value, or epsilon-limit library.
The setting therefore supplies only an abstract closeness relation and its
separation law.  Tail limits, uniqueness, and limit selection are then built
from that lower-level interface rather than assumed as fields. -/

structure SequenceLimitSetting where
  Point : Type
  Precision : Type
  Close : Point → Point → Precision → Prop
  reflexiveClose : ∀ x ε, Close x x ε
  jointlyCloseForcesEq :
    ∀ L₁ L₂, (∀ ε, ∃ x, Close x L₁ ε ∧ Close x L₂ ε) → L₁ = L₂

def HasLimit (S : SequenceLimitSetting) (a : Nat → S.Point)
    (L : S.Point) : Prop :=
  ∀ ε, ∃ N, ∀ n, N ≤ n → S.Close (a n) L ε

def Convergent (S : SequenceLimitSetting) (a : Nat → S.Point) : Prop :=
  ∃ L, HasLimit S a L

theorem sequenceLimitUnique (S : SequenceLimitSetting)
    (a : Nat → S.Point) (L₁ L₂ : S.Point)
    (h₁ : HasLimit S a L₁) (h₂ : HasLimit S a L₂) : L₁ = L₂ := by
  apply S.jointlyCloseForcesEq L₁ L₂
  intro ε
  obtain ⟨N₁, hN₁⟩ := h₁ ε
  obtain ⟨N₂, hN₂⟩ := h₂ ε
  let N := Nat.max N₁ N₂
  exact ⟨a N, hN₁ N (Nat.le_max_left _ _),
    hN₂ N (Nat.le_max_right _ _)⟩

theorem constantSequenceHasLimit (S : SequenceLimitSetting) (c : S.Point) :
    HasLimit S (fun _ => c) c := by
  intro ε
  exact ⟨0, fun _ _ => S.reflexiveClose c ε⟩

/- This is the Prelude-only analogue of Litex's `have fn lim by exist!`.
Lean's built-in classical choice selects the witness; uniqueness above proves
that any two witnesses denote the same mathematical limit. -/

noncomputable def lim (S : SequenceLimitSetting) (a : Nat → S.Point)
    (h : Convergent S a) : S.Point :=
  Classical.choose h

theorem selectedLimitHasLimit (S : SequenceLimitSetting)
    (a : Nat → S.Point) (h : Convergent S a) :
    HasLimit S a (lim S a h) :=
  Classical.choose_spec h
