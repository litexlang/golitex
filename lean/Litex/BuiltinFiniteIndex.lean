import Litex.FiniteSets
universe u v w x y z
namespace Litex

theorem finiteSetBijectiveIndexValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} [Representation M α] (A : Obj (M := M) α) (hA : IsFiniteSet A) :
    ∃ f : Obj (M := M) M.Value,
      M.mem (denote f) (F.fnSetValue (FiniteFunction.indexSet (finiteCard (denote A))) (denote A)) ∧
      bijectiveValue (FiniteFunction.indexSet (finiteCard (denote A))) (denote A) (denote f) := by
  classical
  letI : Fintype (memberSet (denote A)) := hA.fintype
  have hc : Fintype.card (memberSet (denote A)) = finiteCard (denote A) :=
    Set.fintypeCard_eq_ncard _
  let e : Fin (finiteCard (denote A)) ≃ memberSet (denote A) :=
    (finCongr hc.symm).trans (Fintype.equivFin _).symm
  let a : Fin (finiteCard (denote A)) → M.Value := fun i => (e i).val
  have hset : FiniteFunction.finiteSetValue (List.ofFn a) = denote A := by
    apply F.ext _ _ (FiniteFunction.finiteSet_isSet _ (by
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact M.member_isSet (e i).property)) (isSet A)
    intro y
    rw [FiniteFunction.finiteSet_members]
    constructor
    · intro hy
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
      exact (e i).property
    · intro hy
      obtain ⟨i,hi⟩ := e.surjective ⟨y,hy⟩
      exact List.mem_ofFn.mpr ⟨i,congrArg Subtype.val hi⟩
  let f : Obj (M := M) M.Value := semanticObject (FiniteFunction.tupleValue a)
    (FiniteFunction.tuple_isSet a)
  have hf : M.mem (denote f)
      (F.fnSetValue (FiniteFunction.indexSet (finiteCard (denote A))) (denote A)) := by
    change M.mem (FiniteFunction.tupleValue a) (F.fnSetValue (FiniteFunction.indexSet (finiteCard (denote A))) (denote A))
    have htuple := (F.fnSet_members _ _ _).mpr (FiniteFunction.tuple_isFunction a)
    simpa only [hset] using htuple
  refine ⟨f,hf,?_,?_⟩
  · intro x hx y hy hxy
    obtain ⟨i,rfl⟩ := (FiniteFunction.indexSet_members x).mp hx
    obtain ⟨j,rfl⟩ := (FiniteFunction.indexSet_members y).mp hy
    change F.callValue (FiniteFunction.tupleValue a) _ = F.callValue (FiniteFunction.tupleValue a) _ at hxy
    rw [FiniteFunction.call_tuple,FiniteFunction.call_tuple] at hxy
    exact congrArg FiniteFunction.index (e.injective (Subtype.ext hxy))
  · intro y hy
    obtain ⟨i,hi⟩ := e.surjective ⟨y,hy⟩
    refine ⟨FiniteFunction.index i,FiniteFunction.index_mem i,?_⟩
    change y = F.callValue (FiniteFunction.tupleValue a) (FiniteFunction.index i)
    rw [FiniteFunction.call_tuple]
    exact (congrArg Subtype.val hi).symm


theorem finiteSetBijectiveIndexWitness {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y} {ε : Type z}
    [Representation M α] [Representation M β] [Representation M γ]
    [Representation M δ] [Representation M ε]
    (A : Obj (M := M) α) (hA : IsFiniteSet A)
    (s : Obj (M := M) (FiniteSeqSetObj (M := M) β γ))
    (r : Obj (M := M) (ClosedRangeObj (M := M) δ ε))
    (hcarrier : Same s.val.carrier A)
    (hn : denote s.val.length = M.number (finiteCard (denote A) : ℂ))
    (hstart : denote r.val.start = M.number 1)
    (hfinish : denote r.val.finish = M.number (finiteCard (denote A) : ℂ)) :
    ∃ f : Obj (M := M) M.Value, In f s ∧ bijectiveValue (denote r) (denote A) (denote f) := by
  have hrange : denote r = FiniteFunction.indexSet (finiteCard (denote A)) := by
    change F.sepValue (M.standard .integer) (ClosedRangeObj.condition r.val) = _
    unfold ClosedRangeObj.condition
    rw [hstart,hfinish]
    exact closedRange_indexSet (finiteCard (denote A))
      (NativeBridge.numberInZOfEq 1 1 (by norm_num))
      (naturalToInteger _ (NativeBridge.numberInN _))
  obtain ⟨f,hf,hbij⟩ := finiteSetBijectiveIndexValue A hA
  refine ⟨f,?_,?_⟩
  · change M.mem (denote f) (denote s)
    rw [denoteFiniteSeq s (finiteCard (denote A)) hn,hcarrier]
    exact hf
  · rw [hrange]
    exact hbij

end Litex
