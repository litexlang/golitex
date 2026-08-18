/- Prelude has no real numbers, absolute value, or epsilon-limit library.
This structure is the explicit boundary corresponding to the Litex
has_limit relation and its proved uniqueness theorem. -/

structure SequenceLimitSetting where
  Real : Type
  Sequence : Type
  HasLimit : Sequence → Real → Prop
  constant : Real → Sequence
  constantHasLimit : ∀ c, HasLimit (constant c) c
  limitUnique : ∀ a L₁ L₂, HasLimit a L₁ → HasLimit a L₂ → L₁ = L₂

theorem sequenceLimitUnique (S : SequenceLimitSetting)
    (a : S.Sequence) (L₁ L₂ : S.Real)
    (h₁ : S.HasLimit a L₁) (h₂ : S.HasLimit a L₂) : L₁ = L₂ :=
  S.limitUnique a L₁ L₂ h₁ h₂

theorem constantSequenceHasLimit (S : SequenceLimitSetting) (c : S.Real) :
    S.HasLimit (S.constant c) c :=
  S.constantHasLimit c
