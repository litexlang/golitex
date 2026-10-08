import Litex

namespace Litex.ObjectMvp

universe u v w x

variable {M : Semantics.{u}}

def one : Obj (M := M) ℂ := number 1
def realSet : Obj (M := M) StandardSetValue := R
def complexSet : Obj (M := M) StandardSetValue := C

def oneSethood : IsSet (one (M := M)) := isSet one
def oneSelf : Same (one (M := M)) one := sameRefl one

section Generic

variable {α : Type v} {β : Type w} {γ : Type x}
variable [Representation M α] [Representation M β] [Representation M γ]

def fromRaw (a : α) (wa : WD (M := M) a) : Obj (M := M) α := ⟨a, wa⟩

def genericSelf (a : Obj (M := M) α) : Same a a := sameRefl a

def genericRealToComplex (a : Obj (M := M) α) (haR : In a R) : In a C :=
  realToComplex a haR

def sum (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) : Obj (M := M) (AddObj (M := M) α β) :=
  add a b haC hbC

def quotient (a : Obj (M := M) α) (b : Obj (M := M) β)
    (haC : In a C) (hbC : In b C) (hb0 : ¬ Same b (number 0)) :
    Obj (M := M) (DivObj (M := M) α β) :=
  div a b haC hbC hb0

def nested (a : Obj (M := M) α) (b : Obj (M := M) β) (c : Obj (M := M) γ)
    (haC : In a C) (hbC : In b C)
    (hsC : In (add a b haC hbC) C) (hcC : In c C) (hc0 : ¬ Same c (number 0)) :
    Obj (M := M) (DivObj (M := M) (AddObj (M := M) α β) γ) :=
  div (add a b haC hbC) c hsC hcC hc0

end Generic

end Litex.ObjectMvp
