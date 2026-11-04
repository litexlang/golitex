import Litex.Analysis
universe u v w x y
namespace Litex

theorem sequenceExtremumBound {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (upper : Bool) (a : Obj (M := M) α) (value : Obj (M := M) β)
    (epsilon : Obj (M := M) γ)
    (h : HasSequenceExtremum upper a value) (he : In epsilon RPos) :
    ∃ cutoff : Obj (M := M) M.Value, ∃ _ : In cutoff NPos,
      SequenceExtremumBoundValue M upper (denote a) (denote value) (denote epsilon) (denote cutoff) :=
  h.1 (denote epsilon) he

theorem sequenceExtremumHit {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (upper : Bool) (a : Obj (M := M) α) (value : Obj (M := M) β)
    (epsilon : Obj (M := M) γ) (cutoff : Obj (M := M) δ)
    (h : HasSequenceExtremum upper a value) (he : In epsilon RPos) (hc : In cutoff NPos) :
    SequenceExtremumHitValue M upper (denote a) (denote value) (denote epsilon) (denote cutoff) :=
  h.2 (denote epsilon) he (denote cutoff) hc

end Litex
