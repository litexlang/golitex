import Litex

-- Handwritten expected compiler output. No automatic emitter exists yet.
namespace InteropExamples.ExpectedTarget

open Litex

universe u v w

variable {M : Semantics.{u}}

theorem oneSelf : Same (number (M := M) 1) (number 1) :=
  sameRefl (number 1)

theorem oneIsSet : IsSet (number (M := M) 1) :=
  isSet (number 1)

theorem oneInR : In (number (M := M) 1) R :=
  (M.real_members (M.number 1)).mpr ⟨1, rfl⟩

theorem complexSelf {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (_haC : In a C) : Same a a :=
  sameRefl a

theorem realInComplex {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haR : In a R) : In a C :=
  realToComplex a haR

theorem addZero {α : Type v} [Representation M α]
    (a : Obj (M := M) α) (haC : In a C) :
    Same (add a (number 0) haC (numberInC 0)) a :=
  Litex.addZero a haC

theorem quotientSelf {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (hb0 : ¬ Same b (number 0)) :
    Same (div a b haC hbC hb0) (div a b haC hbC hb0) :=
  sameRefl (div a b haC hbC hb0)

end InteropExamples.ExpectedTarget
