import Litex.GlobalContinuity

universe u v w x
namespace Litex

noncomputable def uniformNearPairsValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (domain delta : M.Value) : M.Value :=
  F.sepValue (FiniteFunction.cartValue ![domain, domain]) (fun pair =>
    ∃ _ : M.mem pair (FiniteFunction.cartValue ![domain, domain]),
      RealLtValue M (absValue (M.subValue (F.callValue pair (M.number 1))
        (F.callValue pair (M.number 2)))) delta)

noncomputable def uniformImagePairsValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (f domain epsilon : M.Value) : M.Value :=
  F.sepValue (FiniteFunction.cartValue ![domain, domain]) (fun pair =>
    ∃ _ : M.mem pair (FiniteFunction.cartValue ![domain, domain]),
      RealLtValue M (absValue (M.subValue (F.callValue f (F.callValue pair (M.number 1)))
        (F.callValue f (F.callValue pair (M.number 2))))) epsilon)

def FunctionUniformControlValue (M : Semantics.{u}) [FunctionSemantics M]
    (f domain epsilon delta : M.Value) : Prop :=
  ∀ pair, M.mem pair (uniformNearPairsValue domain delta) →
    M.mem pair (uniformImagePairsValue f domain epsilon)

def FunctionUniformEpsilonClauseValue (M : Semantics.{u}) [FunctionSemantics M]
    (f domain epsilon : M.Value) : Prop :=
  ∃ delta : Obj (M := M) M.Value, ∃ _ : In delta RPos,
    FunctionUniformControlValue M f domain epsilon (denote delta)

def FunctionUniformContinuousValue (M : Semantics.{u}) [F : FunctionSemantics M]
    (f : M.Value) : Prop :=
  ∀ epsilon, M.mem epsilon (denote (RPos (M := M))) →
    FunctionUniformEpsilonClauseValue M f (F.domainValue f) epsilon

def FunctionUniformContinuous {M : Semantics.{u}} [FunctionSemantics M]
    {α : Type v} [Representation M α] (f : Obj (M := M) α) : Prop :=
  FunctionUniformContinuousValue M (denote f)

theorem functionUniformOfForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (domain : Obj (M := M) β)
    (hd : denote domain = F.domainValue (denote f))
    (h : ∀ {γ : Type x} [Representation M γ], (epsilon : Obj (M := M) γ) →
      In epsilon RPos → FunctionUniformEpsilonClauseValue M
        (denote f) (denote domain) (denote epsilon)) : FunctionUniformContinuous f := by
  have hraw := forallMembersOfRepresentations RPos h
  intro epsilon hepsilon
  exact hd ▸ hraw epsilon hepsilon

theorem functionUniformForall {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (domain : Obj (M := M) β)
    (hd : denote domain = F.domainValue (denote f)) (h : FunctionUniformContinuous f) :
    ∀ {γ : Type x} [Representation M γ], (epsilon : Obj (M := M) γ) →
      In epsilon RPos → FunctionUniformEpsilonClauseValue M
        (denote f) (denote domain) (denote epsilon) := by
  intro _ _ epsilon hepsilon
  exact hd.symm ▸ h (denote epsilon) hepsilon

theorem functionUniformControl {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (f : Obj (M := M) α) (epsilon : Obj (M := M) β) (he : In epsilon RPos)
    (h : FunctionUniformContinuous f) :
    FunctionUniformEpsilonClauseValue M (denote f) (F.domainValue (denote f))
      (denote epsilon) := h (denote epsilon) he

theorem functionUniformImpliesContinuous {M : Semantics.{u}} [F : FunctionSemantics M]
    (f : M.Value) (hf : RealFunctionValue M f)
    (h : FunctionUniformContinuousValue M f) : FunctionContinuousValue M f := by
  intro point hp epsilon he
  obtain ⟨delta, hd, control⟩ := h epsilon he
  refine ⟨delta, hd, ?_⟩
  intro input hn
  obtain ⟨hx, _, near⟩ := (F.sep_members _ _ _).mp hn
  change RealLtValue M (absValue (M.subValue input point)) (denote delta) at near
  let pair := FiniteFunction.tupleValue ![input, point]
  have hpair : M.mem pair (FiniteFunction.cartValue ![F.domainValue f, F.domainValue f]) := by
    apply FiniteFunction.tuple_inCart
    intro i
    fin_cases i
    · exact hx
    · exact hp
  have first : F.callValue pair (M.number 1) = input := by
    simpa [pair, FiniteFunction.index] using (FiniteFunction.call_tuple (M := M) ![input, point] (0 : Fin 2))
  have second : F.callValue pair (M.number 2) = point := by
    simpa [pair, FiniteFunction.index] using (FiniteFunction.call_tuple (M := M) ![input, point] (1 : Fin 2))
  have hin : M.mem pair (uniformNearPairsValue (F.domainValue f) (denote delta)) := by
    apply (F.sep_members _ _ _).mpr
    refine ⟨hpair, hpair, ?_⟩
    change RealLtValue M (absValue (M.subValue (F.callValue pair (M.number 1))
      (F.callValue pair (M.number 2)))) (denote delta)
    rw [first, second]
    exact near
  obtain ⟨_, _, close⟩ := (F.sep_members _ _ _).mp (control pair hin)
  change RealLtValue M (absValue (M.subValue (F.callValue f (F.callValue pair (M.number 1)))
    (F.callValue f (F.callValue pair (M.number 2))))) epsilon at close
  rw [first, second] at close
  obtain ⟨signature, hfn, _, outputReal⟩ := hf
  have hdomain := F.domainValue_eq signature.domain_isSet hfn
  have hxSig := hdomain ▸ hx
  have hy := outputReal _ (F.call_mem _ _ _ _ hfn hxSig)
  apply (F.preimage_mem_iff _ signature.domain_isSet hfn).mpr
  refine ⟨hxSig, ?_⟩
  apply (F.sep_members _ _ _).mpr
  exact ⟨hy, hy, close⟩

end Litex
