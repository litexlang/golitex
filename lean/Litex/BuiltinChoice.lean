import Litex.Folds
universe u v w x
namespace Litex
variable {M : Semantics.{u}} [F : FunctionSemantics M] [IU : IndexedUnionSemantics M]
variable {α : Type v} {β : Type w} {γ : Type x}
variable [Representation M α] [Representation M β] [Representation M γ]

theorem indexCartNonemptyPointwise (p : Obj (M := M) (IndexCartObj M α β γ))
    (h : ∀ i, M.mem i (denote p.val.index) →
      ∃ y, M.mem y (F.callValue (denote p.val.family) i)) : IsNonempty p := by
  classical
  let select := fun i : M.Value =>
    if hi : ∃ y, M.mem y (F.callValue (denote p.val.family) i) then Classical.choose hi else F.emptyValue
  have selected : ∀ i, M.mem i (denote p.val.index) →
      M.mem (select i) (F.callValue (denote p.val.family) i) := by
    intro i hi
    have hy := h i hi
    dsimp only [select]
    rw [dif_pos hy]
    exact Classical.choose_spec hy
  let D := F.sepValue (denote p.val.index) (fun _ => True)
  let E := IU.indexedUnionValue (denote p.val.familySet) id
  have returned : ∀ i, M.mem i D → M.mem (select i) E := by
    intro i hi
    have hiI := ((F.sep_members _ _ _).mp hi).1
    have hg : M.mem (F.callValue (denote p.val.family) i) (denote p.val.familySet) :=
      FunctionSemantics.call_mem _ _ _ _ p.wd.2.2.2 hi
    exact (IU.indexedUnion_members _ _ _).mpr ⟨_,hg,selected i hiI⟩
  let value := F.graphValue D E select
  have hvalue := FunctionSemantics.graph_inFnSet D E select returned
  refine ⟨value, (F.sep_members _ _ _).mpr ⟨hvalue, ?_⟩⟩
  intro i hi
  have hiD : M.mem i D := (F.sep_members _ _ _).mpr ⟨hi,True.intro⟩
  change M.mem (F.callValue value i) (F.callValue (denote p.val.family) i)
  rw [FunctionSemantics.call_graphValue D E select returned i hiD]
  exact selected i hi

theorem indexCartNonemptyFamily (p : Obj (M := M) (IndexCartObj M α β γ))
    (h : ∀ A, M.mem A (denote p.val.familySet) → ∃ y, M.mem y A) : IsNonempty p := by
  apply indexCartNonemptyPointwise p
  intro i hi
  have hiD : M.mem i (indexFamilySignature p.val.index p.val.familySet).domain :=
    (F.sep_members _ _ _).mpr ⟨hi,True.intro⟩
  exact h _ (FunctionSemantics.call_mem _ _ _ _ p.wd.2.2.2 hiD)
end Litex
