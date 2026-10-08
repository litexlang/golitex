import Mathlib.Data.Complex.Basic

namespace Litex

universe u

inductive StandardSetValue where
  | natural
  | integer
  | rational
  | real
  | complex
  deriving DecidableEq, Repr

/-- An explicit contract for a future mathematical model, not an instantiated
model or a collection of global axioms. The object API is conditional on it. -/
structure Semantics where
  Value : Type u
  mem : Value → Value → Prop
  isSet : Value → Prop
  number : ℂ → Value
  standard : StandardSetValue → Value
  addValue : Value → Value → Value
  divValue : Value → Value → Value
  number_injective : Function.Injective number
  complex_members : ∀ x, mem x (standard .complex) ↔ ∃ z, x = number z
  real_members : ∀ x, mem x (standard .real) ↔ ∃ r : ℝ, x = number (r : ℂ)
  real_subset_complex : ∀ x, mem x (standard .real) → mem x (standard .complex)
  member_isSet : ∀ {x A}, mem x A → isSet x
  standard_isSet : ∀ A, isSet (standard A)
  add_numbers : ∀ a b, addValue (number a) (number b) = number (a + b)
  div_numbers : ∀ a b, b ≠ 0 → divValue (number a) (number b) = number (a / b)
  add_closed : ∀ {a b},
    mem a (standard .complex) → mem b (standard .complex) →
    mem (addValue a b) (standard .complex)
  div_closed : ∀ {a b},
    mem a (standard .complex) → mem b (standard .complex) →
    b ≠ number 0 → mem (divValue a b) (standard .complex)

end Litex
