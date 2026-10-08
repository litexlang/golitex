import Litex

open Litex

-- Intentionally rejected: arbitrary α has no automatic Representation instance.
def missingRepresentation {M : Semantics} {α : Type} (a : α) :
    Obj (M := M) α :=
  ⟨a, True.intro⟩
