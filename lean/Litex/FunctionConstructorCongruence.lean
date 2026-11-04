import Litex.FiniteSets

universe u
namespace Litex

/-- A function graph depends only on body values inside its declared domain.
The original return certificate also certifies the pointwise equal body. -/
theorem functionGraphValueCongr {M : Semantics.{u}} [F : FunctionSemantics M]
    (D B : M.Value) (f g : M.Value → M.Value)
    (hf : ∀ x, M.mem x D → M.mem (f x) B)
    (h : ∀ x, M.mem x D → f x = g x) :
    F.graphValue D B f = F.graphValue D B g := by
  apply F.graph_ext D B _ _ (FunctionSemantics.graph_isFunction D B f hf)
    (FunctionSemantics.graph_isFunction D B g (fun x hx => (h x hx) ▸ hf x hx))
  intro x y
  rw [FunctionSemantics.pair_mem_graph, FunctionSemantics.pair_mem_graph]
  constructor
  · rintro ⟨hx, hy, he⟩
    exact ⟨hx, hy, he.trans (h x hx)⟩
  · rintro ⟨hx, hy, he⟩
    exact ⟨hx, hy, he.trans (h x hx).symm⟩

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
