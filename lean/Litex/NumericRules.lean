import Litex.Arithmetic

namespace Litex

universe u v

/-- A Core arithmetic law; this is not yet a replay of a Rust verifier result. -/
theorem addZero {M : Semantics.{u}} {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) :
    Same (add a (number 0) haC (numberInC 0)) a := by
  obtain ⟨z, hz⟩ := (M.complex_members (denote a)).mp haC
  change M.addValue (denote a) (M.number 0) = denote a
  rw [hz, M.add_numbers, add_zero]

end Litex
