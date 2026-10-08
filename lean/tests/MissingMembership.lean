import Litex

open Litex

-- Intentionally rejected: hbC is absent, so add is still a function.
def missingMembership {M : Semantics} {α β : Type}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (haC : In a C) :
    Obj (M := M) (AddObj (M := M) α β) :=
  add a b haC
