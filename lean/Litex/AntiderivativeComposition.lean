import Litex.AntiderivativeAlgebra

universe u
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M]

theorem antiderivativeComposeFunctions
    (primitive function inner innerValue result resultValue region target : M.Value)
    (realPrimitive : RealFunctionValue M primitive) (realInner : RealFunctionValue M inner)
    (interior : RealRegionInteriorValue M region)
    (cover : ∀ x, M.mem x region → M.mem x (F.domainValue result))
    (source : IsAntiderivativeOnValue M primitive function target)
    (image : ∀ x, M.mem x region → M.mem (F.callValue inner x) target)
    (innerDerivative : ∀ x, M.mem x region →
      HasDerivativeAtValue M inner x (F.callValue innerValue x))
    (equal : ∀ x, M.mem x region →
      F.callValue result x=F.callValue primitive (F.callValue inner x) ∧
      F.callValue resultValue x=M.mulValue (F.callValue function (F.callValue inner x)) (F.callValue innerValue x)) :
    IsAntiderivativeOnValue M result resultValue region := by
  intro point member
  obtain ⟨p,hp,radius,hradius,hnear⟩ := interior point member
  have composed := semanticDerivativeComposeCandidates inner primitive point
    (F.callValue innerValue point) (F.callValue function (F.callValue inner point)) p hp
    realInner realPrimitive (innerDerivative point member) (source _ (image point member))
  rw [(equal point member).2]
  exact derivativeInRegionOfSemanticFormula result point _ region p radius _ hp hradius
    hnear cover (fun x hx => (equal _ hx).1) composed
end Litex
