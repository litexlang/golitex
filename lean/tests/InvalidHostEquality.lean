import Litex.NativeBridge

open Litex

-- Intentionally rejected: semantic equality does not imply equality of raw payloads.
def invalidHostEquality {M : Semantics} {α : Type} [Representation M α]
    (a b : Obj (M := M) α) (h : Same a b) : a.val = b.val :=
  h
