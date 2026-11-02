import Litex.ElementaryFunctions
universe u v w x
namespace Litex

theorem finiteAggregatePointwiseValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (product : Bool) (A B f g : M.Value) (hfinite : (memberSet A).Finite)
    (hsets : A = B)
    (hpoint : ∀ x, M.mem x A → F.callValue f x = F.callValue g x) :
    finiteAggregateValue product A (fun x => NativeBridge.complexValue (F.callValue f x)) =
      finiteAggregateValue product B (fun x => NativeBridge.complexValue (F.callValue g x)) := by
  subst B
  unfold finiteAggregateValue
  simp only [dif_pos hfinite]
  cases product
  · simp only [Bool.false_eq_true,if_false]
    apply Finset.sum_congr rfl
    intro x hx
    exact congrArg NativeBridge.complexValue (hpoint x (hfinite.mem_toFinset.mp hx))
  · simp only [if_true]
    apply Finset.prod_congr rfl
    intro x hx
    exact congrArg NativeBridge.complexValue (hpoint x (hfinite.mem_toFinset.mp hx))
private theorem finiteSumRealDenotation {M : Semantics.{u}} (A : M.Value)
    (value : M.Value → ℂ) (hfinite : (memberSet A).Finite)
    (hreal : ∀ x, M.mem x A → value x = ((value x).re : ℂ)) :
    finiteAggregateValue false A value =
      ((∑ x ∈ hfinite.toFinset, (value x).re : ℝ) : ℂ) := by
  unfold finiteAggregateValue
  rw [dif_pos hfinite]
  simp only [Bool.false_eq_true,if_false]
  push_cast
  exact Finset.sum_congr rfl (fun x hx => hreal x (hfinite.mem_toFinset.mp hx))

theorem finiteSumPointwiseLeValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (A B f g : M.Value) (hfinite : (memberSet A).Finite) (hsets : A = B)
    (hpoint : ∀ x, M.mem x A → realBound true (F.callValue f x) (F.callValue g x)) :
    realBound true
      (M.number (finiteAggregateValue false A (fun x => NativeBridge.complexValue (F.callValue f x))))
      (M.number (finiteAggregateValue false B (fun x => NativeBridge.complexValue (F.callValue g x)))) := by
  subst B
  let vf := fun x => NativeBridge.complexValue (F.callValue f x)
  let vg := fun x => NativeBridge.complexValue (F.callValue g x)
  have hf : ∀ x, M.mem x A → vf x = ((vf x).re : ℂ) := by
    intro x hx
    obtain ⟨r,s,hr,hs,_⟩ := hpoint x hx
    dsimp [vf]
    rw [hr,NativeBridge.complexValue_number]
    rfl
  have hg : ∀ x, M.mem x A → vg x = ((vg x).re : ℂ) := by
    intro x hx
    obtain ⟨r,s,hr,hs,_⟩ := hpoint x hx
    dsimp [vg]
    rw [hs,NativeBridge.complexValue_number]
    rfl
  have hle : (∑ x ∈ hfinite.toFinset, (vf x).re) ≤
      ∑ x ∈ hfinite.toFinset, (vg x).re := by
    apply Finset.sum_le_sum
    intro x hx
    obtain ⟨r,s,hr,hs,hrs⟩ := hpoint x (hfinite.mem_toFinset.mp hx)
    dsimp [vf,vg]
    rw [hr,hs,NativeBridge.complexValue_number,NativeBridge.complexValue_number]
    exact hrs
  exact ⟨_,_,congrArg M.number (finiteSumRealDenotation A vf hfinite hf),
    congrArg M.number (finiteSumRealDenotation A vg hfinite hg),hle⟩

theorem finiteSummandLeSumValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (A f t : M.Value) (hfinite : (memberSet A).Finite) (hmember : M.mem t A)
    (hnonnegative : ∀ x, M.mem x A → realBound true (M.number 0) (F.callValue f x)) :
    realBound true (F.callValue f t)
      (M.number (finiteAggregateValue false A (fun x => NativeBridge.complexValue (F.callValue f x)))) := by
  let v := fun x => NativeBridge.complexValue (F.callValue f x)
  have hvalue : ∀ x, M.mem x A → F.callValue f x = M.number ((v x).re : ℂ) := by
    intro x hx
    obtain ⟨r,s,hr,hs,_⟩ := hnonnegative x hx
    dsimp [v]
    rw [hs,NativeBridge.complexValue_number]
    rfl
  have hreal : ∀ x, M.mem x A → v x = ((v x).re : ℂ) := by
    intro x hx
    obtain ⟨r,s,hr,hs,_⟩ := hnonnegative x hx
    dsimp [v]
    rw [hs,NativeBridge.complexValue_number]
    rfl
  have hnonneg : ∀ x ∈ hfinite.toFinset, 0 ≤ (v x).re := by
    intro x hx
    obtain ⟨r,s,hr,hs,hrs⟩ := hnonnegative x (hfinite.mem_toFinset.mp hx)
    have hr0 : r = 0 := Complex.ofReal_injective (by
      simpa only [Complex.ofReal_zero] using (M.number_injective hr).symm)
    subst r
    dsimp [v]
    rw [hs,NativeBridge.complexValue_number]
    exact hrs
  have hle : (v t).re ≤ ∑ x ∈ hfinite.toFinset, (v x).re :=
    Finset.single_le_sum hnonneg (hfinite.mem_toFinset.mpr hmember)
  exact ⟨_,_,hvalue t hmember,
    congrArg M.number (finiteSumRealDenotation A v hfinite hreal),hle⟩


theorem integerRangeBoundsValue {M : Semantics.{u}} (a b : M.Value)
    (ha : M.mem a (M.standard .integer)) (hb : M.mem b (M.standard .integer))
    (k : ℤ) (hlo : NativeBridge.integerValue a ≤ k) (hhi : k ≤ NativeBridge.integerValue b) :
    realBound true a (M.number (k : ℂ)) ∧ realBound true (M.number (k : ℂ)) b := by
  constructor
  · refine ⟨(NativeBridge.integerValue a : ℝ), (k : ℝ), ?_, ?_, ?_⟩
    · simpa only [Complex.ofReal_intCast] using NativeBridge.integerValue_spec a ha
    · simp only [Complex.ofReal_intCast]
    · exact_mod_cast hlo
  · refine ⟨(k : ℝ), (NativeBridge.integerValue b : ℝ), ?_, ?_, ?_⟩
    · simp only [Complex.ofReal_intCast]
    · simpa only [Complex.ofReal_intCast] using NativeBridge.integerValue_spec b hb
    · exact_mod_cast hhi

theorem rangeSumPointwiseLeValue {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b c d f g : M.Value) (ha : a=c) (hb : b=d)
    (hpoint : ∀ k : ℤ, NativeBridge.integerValue a ≤ k → k ≤ NativeBridge.integerValue b →
      realBound true (F.callValue f (M.number (k : ℂ))) (F.callValue g (M.number (k : ℂ)))) :
    realBound true
      (M.number (nativeRangeAggregate false (NativeBridge.integerValue a) (NativeBridge.integerValue b)
        (fun k => NativeBridge.complexValue (F.callValue f (M.number (k : ℂ))))))
      (M.number (nativeRangeAggregate false (NativeBridge.integerValue c) (NativeBridge.integerValue d)
        (fun k => NativeBridge.complexValue (F.callValue g (M.number (k : ℂ)))))) := by
  subst c
  subst d
  let vf := fun k : ℤ => NativeBridge.complexValue (F.callValue f (M.number (k : ℂ)))
  let vg := fun k : ℤ => NativeBridge.complexValue (F.callValue g (M.number (k : ℂ)))
  let s := Finset.Icc (NativeBridge.integerValue a) (NativeBridge.integerValue b)
  have hf : ∀ k ∈ s, vf k = ((vf k).re : ℂ) := by
    intro k hk
    obtain ⟨r,t,hr,ht,_⟩ := hpoint k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    dsimp [vf]
    rw [hr,NativeBridge.complexValue_number]
    rfl
  have hg : ∀ k ∈ s, vg k = ((vg k).re : ℂ) := by
    intro k hk
    obtain ⟨r,t,hr,ht,_⟩ := hpoint k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    dsimp [vg]
    rw [ht,NativeBridge.complexValue_number]
    rfl
  have hle : (∑ k ∈ s, (vf k).re) ≤ ∑ k ∈ s, (vg k).re := by
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨r,t,hr,ht,hrt⟩ := hpoint k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    dsimp [vf,vg]
    rw [hr,ht,NativeBridge.complexValue_number,NativeBridge.complexValue_number]
    exact hrt
  have hcast (v : ℤ → ℂ) (hv : ∀ k ∈ s, v k = ((v k).re : ℂ)) :
      (∑ k ∈ s, v k) = ((∑ k ∈ s, (v k).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl hv
  exact ⟨_,_,congrArg M.number (hcast vf hf),congrArg M.number (hcast vg hg),hle⟩


theorem rangeSumEnumerationValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (b : Obj (M := M) β) (ha : In a Z) (hb : In b Z)
    (A f e : M.Value) (hfinite : (memberSet A).Finite)
    (hmaps : ∀ k : ℤ, NativeBridge.integerValue (denote a) ≤ k →
      k ≤ NativeBridge.integerValue (denote b) → M.mem (F.callValue e (M.number (k : ℂ))) A)
    (hbij : bijectiveValue (denote (closedRange a b ha hb)) A e) :
    nativeRangeAggregate false (NativeBridge.integerValue (denote a))
      (NativeBridge.integerValue (denote b))
      (fun k => NativeBridge.complexValue (F.callValue f (F.callValue e (M.number (k : ℂ))))) =
    finiteAggregateValue false A (fun x => NativeBridge.complexValue (F.callValue f x)) := by
  classical
  have hdom (k : ℤ) (hk : k ∈ Finset.Icc (NativeBridge.integerValue (denote a))
      (NativeBridge.integerValue (denote b))) :
      M.mem (M.number (k : ℂ)) (denote (closedRange a b ha hb)) :=
    inClosedRangeOfDenote a b (number (k : ℂ)) ha hb
      (NativeBridge.integerValue (denote a)) (NativeBridge.integerValue (denote b)) k
      (NativeBridge.integerValue_spec _ ha) (NativeBridge.integerValue_spec _ hb) rfl
      (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  unfold nativeRangeAggregate finiteAggregateValue
  simp only [Bool.false_eq_true, if_false, dif_pos hfinite]
  apply Finset.sum_bij (fun (k : ℤ) _ => F.callValue e (M.number (k : ℂ)))
  · intro k hk
    exact hfinite.mem_toFinset.mpr (hmaps k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  · intro k hk l hl heq
    have hn := M.number_injective (hbij.1 _ (hdom k hk) _ (hdom l hl) heq)
    exact_mod_cast hn
  · intro y hy
    obtain ⟨x,hx,heq⟩ := hbij.2 y (hfinite.mem_toFinset.mp hy)
    obtain ⟨lower,upper,k,hl,hu,hxk,hlo,hhi⟩ :=
      (inClosedRange_iff a b (semanticObject x (M.member_isSet hx)) ha hb).mp hx
    have hlower : lower = NativeBridge.integerValue (denote a) := by
      have h := M.number_injective (hl.symm.trans (NativeBridge.integerValue_spec _ ha))
      exact_mod_cast h
    have hupper : upper = NativeBridge.integerValue (denote b) := by
      have h := M.number_injective (hu.symm.trans (NativeBridge.integerValue_spec _ hb))
      exact_mod_cast h
    refine ⟨k,Finset.mem_Icc.mpr ⟨hlower ▸ hlo,hupper ▸ hhi⟩,?_⟩
    exact (congrArg (F.callValue e) hxk).symm.trans heq.symm
  · intro k hk
    rfl

theorem rangeSumNamedEnumerationValue {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x}
    [Representation M α] [Representation M β] [Representation M γ]
    (p : Obj (M := M) (RangeAggregateObj (M := M) false α β γ))
    (g : Obj (M := M) (FormulaFn M)) (A f e : M.Value)
    (hfinite : (memberSet A).Finite)
    (heq : denote p.val.function = denote g)
    (hbody : ∀ x, g.val.bodyValue x = F.callValue f (F.callValue e x))
    (hdom : p.val.signature.domain = g.val.signature.domain)
    (hmaps : ∀ x, M.mem x (denote (closedRange p.val.first p.val.last p.wd.1 p.wd.2.1)) →
      M.mem (F.callValue e x) A)
    (hbij : bijectiveValue (denote (closedRange p.val.first p.val.last p.wd.1 p.wd.2.1)) A e) :
    denote p = M.number (finiteAggregateValue false A
      (fun x => NativeBridge.complexValue (F.callValue f x))) := by
  have hpoint (k : ℤ) (hlo : NativeBridge.integerValue (denote p.val.first) ≤ k)
      (hhi : k ≤ NativeBridge.integerValue (denote p.val.last)) :
      F.callValue (denote p.val.function) (M.number (k : ℂ)) =
        F.callValue f (F.callValue e (M.number (k : ℂ))) := by
    rw [heq]
    exact (FunctionSemantics.call_graphValue _ _ _ g.wd _
      (hdom ▸ p.wd.2.2.2.2.2 k hlo hhi)).trans (hbody _)
  change M.number (nativeRangeAggregate false _ _ _) = _
  apply congrArg M.number
  calc
    _ = nativeRangeAggregate false _ _
        (fun k => NativeBridge.complexValue (F.callValue f (F.callValue e (M.number (k : ℂ))))) := by
      unfold nativeRangeAggregate
      simp only [Bool.false_eq_true, if_false]
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg NativeBridge.complexValue (hpoint k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
    _ = _ := rangeSumEnumerationValue p.val.first p.val.last p.wd.1 p.wd.2.1 A f e hfinite
      (fun k hlo hhi => hmaps _ (inClosedRangeOfDenote _ _ (number (k : ℂ)) _ _
        _ _ k (NativeBridge.integerValue_spec _ p.wd.1) (NativeBridge.integerValue_spec _ p.wd.2.1)
        rfl hlo hhi)) hbij
end Litex
