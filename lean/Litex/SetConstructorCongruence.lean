import Litex.FiniteSets
import Litex.Folds

universe u v w x y

namespace Litex

theorem unionSameOfArgs {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (s : Obj (M := M) (UnionObj (M := M) α β))
    (t : Obj (M := M) (UnionObj (M := M) γ δ))
    (hl : Same s.val.left t.val.left) (hr : Same s.val.right t.val.right) : Same s t :=
  congrArg₂ S.unionValue hl hr

theorem intersectSameOfArgs {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (s : Obj (M := M) (IntersectObj (M := M) α β))
    (t : Obj (M := M) (IntersectObj (M := M) γ δ))
    (hl : Same s.val.left t.val.left) (hr : Same s.val.right t.val.right) : Same s t :=
  congrArg₂ (fun a b => S.sepValue a (fun z => M.mem z b)) hl hr

theorem setMinusSameOfArgs {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (s : Obj (M := M) (SetMinusObj (M := M) α β))
    (t : Obj (M := M) (SetMinusObj (M := M) γ δ))
    (hl : Same s.val.left t.val.left) (hr : Same s.val.right t.val.right) : Same s t :=
  congrArg₂ (fun a b => S.sepValue a (fun z => ¬ M.mem z b)) hl hr

theorem powerSetSameOfBound {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (PowerSetObj (M := M) α))
    (t : Obj (M := M) (PowerSetObj (M := M) β))
    (h : Same s.val.bound t.val.bound) : Same s t :=
  congrArg S.powerValue h

theorem familyUnionSameOfFamily {M : Semantics.{u}} [I : IndexedUnionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (s : Obj (M := M) (FamilyUnionObj (M := M) α))
    (t : Obj (M := M) (FamilyUnionObj (M := M) β))
    (h : Same s.val.family t.val.family) : Same s t :=
  congrArg (fun A => I.indexedUnionValue A id) h

theorem symmetricDifferenceSameOfArgs {M : Semantics.{u}} [S : SetSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (s : Obj (M := M) (SymmetricDifferenceObj (M := M) α β))
    (t : Obj (M := M) (SymmetricDifferenceObj (M := M) γ δ))
    (hl : Same s.val.left t.val.left) (hr : Same s.val.right t.val.right) : Same s t :=
  congrArg₂ (symmetricDifferenceValue (M := M)) hl hr

end Litex
