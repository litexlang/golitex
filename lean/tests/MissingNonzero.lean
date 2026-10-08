import Litex

open Litex

-- Intentionally rejected: hb0 is absent, so div is still a function.
def missingNonzero {M : Semantics} {α β : Type}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : Obj (M := M) (DivObj (M := M) α β) :=
  div a b haC hbC
