import Litex

namespace Litex.InterfaceChecks

universe u v

variable {M : Semantics.{u}} {α : Type v} [Representation M α]

example : (number (M := M) 1).val = (1 : ℂ) := rfl

example (a : α) (wa₁ wa₂ : WD (M := M) a) :
    (⟨a, wa₁⟩ : Obj (M := M) α) = ⟨a, wa₂⟩ := rfl

example (a : Obj (M := M) α) : Same a a := sameRefl a
example (a : Obj (M := M) α) : IsSet a := isSet a

example (a : Obj (M := M) α) (haR : In a R) : In a C := realToComplex a haR

#print axioms Litex.isSet
#print axioms Litex.sameRefl
#print axioms Litex.numberInC
#print axioms Litex.realToComplex
#print axioms Litex.add
#print axioms Litex.div
#print axioms Litex.addInC
#print axioms Litex.divInC

end Litex.InterfaceChecks
