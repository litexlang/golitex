import Litex.FiniteSets

universe u
namespace Litex

/-- Range interpretation respects the original function denotation equality. -/
theorem functionRangeValueCongr {M : Semantics.{u}} [FunctionSemantics M]
    {f g : M.Value} (h : f = g) :
    FunctionSemantics.rangeValue f = FunctionSemantics.rangeValue g :=
  congrArg (FunctionSemantics.rangeValue (M := M)) h

/-- A point target retains its equality predicate. -/
theorem pointPreimageValueCongr {M : Semantics.{u}} [FunctionSemantics M]
    {f g a b : M.Value} (hf : f = g) (ht : a = b) :
    FunctionSemantics.preimageValue f (fun y => y = a) =
      FunctionSemantics.preimageValue g (fun y => y = b) :=
  congrArg₂ (FunctionSemantics.preimageValue (M := M)) hf
    (funext fun y => congrArg (fun value => y = value) ht)

/-- A set target retains its membership predicate. -/
theorem setPreimageValueCongr {M : Semantics.{u}} [FunctionSemantics M]
    {f g a b : M.Value} (hf : f = g) (ht : a = b) :
    FunctionSemantics.preimageValue f (fun y => M.mem y a) =
      FunctionSemantics.preimageValue g (fun y => M.mem y b) :=
  congrArg₂ (FunctionSemantics.preimageValue (M := M)) hf
    (funext fun y => congrArg (fun value => M.mem y value) ht)

/-- Composition interpretation keeps the original outer-then-inner order. -/
theorem compositionValueCongr {M : Semantics.{u}} [FunctionSemantics M]
    {f g a b : M.Value} (hf : f = g) (hg : a = b) :
    FunctionSemantics.compositionValue f a = FunctionSemantics.compositionValue g b :=
  congrArg₂ (FunctionSemantics.compositionValue (M := M)) hf hg

end Litex
