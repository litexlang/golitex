import Litex.Derivative

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

-- Formation is checked separately against the two original complete domains.
-- The mathematical relation is exactly the source's pointwise definition.
def IsAntiderivativeOnValue (M : Semantics.{u}) [FunctionSemantics M]
    (primitive function region : M.Value) : Prop :=
  ∀ point, M.mem point region →
    HasDerivativeAtValue M primitive point
      (FunctionSemantics.callValue function point)

theorem antiderivativeFromDefiningClause (primitive function region : M.Value)
    (h : ∀ point, M.mem point region →
      HasDerivativeAtValue M primitive point (F.callValue function point)) :
    IsAntiderivativeOnValue M primitive function region := h

theorem antiderivativeDefiningClause (primitive function region : M.Value)
    (h : IsAntiderivativeOnValue M primitive function region) :
    ∀ point, M.mem point region →
      HasDerivativeAtValue M primitive point (F.callValue function point) := h

theorem antiderivativeRestrict (primitive function source target : M.Value)
    (subset : ∀ point, M.mem point target → M.mem point source)
    (h : IsAntiderivativeOnValue M primitive function source) :
    IsAntiderivativeOnValue M primitive function target :=
  fun point member => h point (subset point member)

end Litex
