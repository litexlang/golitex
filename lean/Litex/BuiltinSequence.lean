import Litex.Analysis
universe u v w x r
open Filter
open scoped Topology
namespace Litex

theorem FunctionSignature.withGuard_true_domain {M : Semantics.{u}} [F : FunctionSemantics M]
    (D B : M.Value) (hD : M.isSet D) (hB : M.isSet B) :
    (FunctionSignature.withGuard D B hD hB (fun _ => True)).domain = D := by
  apply F.ext _ _ (F.sep_isSet D _ hD) hD
  intro x
  exact (F.sep_members D (fun _ => True) x).trans ⟨And.left,fun h => ⟨h,True.intro⟩⟩


theorem sequenceLimitConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β)
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In value R)
    (h : ∀ n, M.mem n (denote (NPos (M := M))) → F.callValue (denote a) n=denote value) :
    HasSequenceLimit a value := by
  obtain ⟨r,hr⟩ := (M.real_members _).mp hv
  change HasSequenceLimitValue M (denote a) (denote value)
  rw [hr]
  apply (sequenceLimit_iff_tendsto (denote a) r hf).mpr
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn
  unfold observeRealSequence
  have hcall : F.callValue (denote a) (M.number (n : ℂ)) = denote value :=
    h _ (numberInNPosOfEq (n : ℂ) n rfl hnpos)
  rw [hcall,hr,observeRealValue_number]


theorem sequenceLimitMap {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} [Representation M α] [Representation M β]
    (a : Obj (M := M) α) (value : Obj (M := M) β) (g : Obj (M := M) (FormulaFn M))
    (hf : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : In value R) (hlimit : HasSequenceLimit a value)
    (operation : M.Value → M.Value) (native : ℝ → ℝ) (hc : Continuous native)
    (hoperation : ∀ r : ℝ, operation (M.number (r : ℂ)) = M.number (native r : ℂ))
    (hD : g.val.signature.domain = denote (NPos (M := M)))
    (hR : g.val.signature.output = denote (R (M := M)))
    (hbody : g.val.bodyValue = fun k => operation (F.callValue (denote a) k)) :
    HasSequenceLimitValue M (denote g) (operation (denote value)) := by
  have hg : M.mem (denote g) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) := by
    have h := formulaFnInFnSet g
    change M.mem (denote g) (F.fnSetValue g.val.signature.domain g.val.signature.output) at h
    rwa [hD,hR] at h
  obtain ⟨r,hr⟩ := (M.real_members _).mp hv
  change HasSequenceLimitValue M (denote a) (denote value) at hlimit
  have hin := (sequenceLimit_iff_tendsto (denote a) r hf).mp (hr ▸ hlimit)
  rw [hr,hoperation]
  apply (sequenceLimit_iff_tendsto (denote g) (native r) hg).mpr
  have hout : Tendsto (fun n => native (observeRealSequence (denote a) n)) atTop (𝓝 (native r)) :=
    hc.continuousAt.tendsto.comp hin
  apply hout.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hd : M.mem (M.number (n : ℂ)) g.val.signature.domain :=
    hD.symm ▸ numberInNPosOfEq (n : ℂ) n rfl hnpos
  have hcall : F.callValue (denote g) (M.number (n : ℂ)) = g.val.bodyValue (M.number (n : ℂ)) :=
    F.call_graphValue _ _ _ g.wd _ hd
  unfold observeRealSequence
  rw [hcall,hbody]
  dsimp only
  rw [observeRealSequence_spec (denote a) n hnpos hf,hoperation]
  simp only [observeRealValue_number]


theorem sequenceLimitMapTwo {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (left : Obj (M := M) γ) (right : Obj (M := M) δ) (g : Obj (M := M) (FormulaFn M))
    (ha : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem (denote b) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : In left R) (hr : In right R) (hla : HasSequenceLimit a left) (hlb : HasSequenceLimit b right)
    (operation : M.Value → M.Value → M.Value) (native : ℝ × ℝ → ℝ)
    (hc : ContinuousAt native (observeRealValue (denote left),observeRealValue (denote right)))
    (hoperation : ∀ r s : ℝ, operation (M.number (r : ℂ)) (M.number (s : ℂ)) = M.number (native (r,s) : ℂ))
    (hD : g.val.signature.domain = denote (NPos (M := M)))
    (hR : g.val.signature.output = denote (R (M := M)))
    (hbody : g.val.bodyValue = fun k => operation (F.callValue (denote a) k) (F.callValue (denote b) k)) :
    HasSequenceLimitValue M (denote g) (operation (denote left) (denote right)) := by
  have hg : M.mem (denote g) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) := by
    have h := formulaFnInFnSet g
    change M.mem (denote g) (F.fnSetValue g.val.signature.domain g.val.signature.output) at h
    rwa [hD,hR] at h
  obtain ⟨l,hleft⟩ := (M.real_members _).mp hl
  obtain ⟨r,hright⟩ := (M.real_members _).mp hr
  change HasSequenceLimitValue M (denote a) (denote left) at hla
  change HasSequenceLimitValue M (denote b) (denote right) at hlb
  have hia := (sequenceLimit_iff_tendsto (denote a) l ha).mp (hleft ▸ hla)
  have hib := (sequenceLimit_iff_tendsto (denote b) r hb).mp (hright ▸ hlb)
  rw [hleft,hright,hoperation]
  apply (sequenceLimit_iff_tendsto (denote g) (native (l,r)) hg).mpr
  rw [hleft,hright,observeRealValue_number,observeRealValue_number] at hc
  have hout : Tendsto (fun n => native (observeRealSequence (denote a) n,observeRealSequence (denote b) n)) atTop (𝓝 (native (l,r))) :=
    hc.tendsto.comp (hia.prodMk_nhds hib)
  apply hout.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hd : M.mem (M.number (n : ℂ)) g.val.signature.domain :=
    hD.symm ▸ numberInNPosOfEq (n : ℂ) n rfl hnpos
  have hcall : F.callValue (denote g) (M.number (n : ℂ)) = g.val.bodyValue (M.number (n : ℂ)) :=
    F.call_graphValue _ _ _ g.wd _ hd
  unfold observeRealSequence
  rw [hcall,hbody]
  dsimp only
  rw [observeRealSequence_spec (denote a) n hnpos ha,observeRealSequence_spec (denote b) n hnpos hb,hoperation]
  simp only [observeRealValue_number]


theorem sequenceLimitDivide {M : Semantics.{u}} [F : FunctionSemantics M]
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type r}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (a : Obj (M := M) α) (b : Obj (M := M) β)
    (left : Obj (M := M) γ) (right : Obj (M := M) δ) (g : Obj (M := M) (FormulaFn M))
    (ha : M.mem (denote a) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem (denote b) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : In left R) (hr : In right R) (hla : HasSequenceLimit a left) (hlb : HasSequenceLimit b right)
    (hne : denote right ≠ M.number 0)
    (hbn : ∀ k, M.mem k (denote (NPos (M := M))) → F.callValue (denote b) k ≠ M.number 0)
    (hD : g.val.signature.domain = denote (NPos (M := M)))
    (hR : g.val.signature.output = denote (R (M := M)))
    (hbody : g.val.bodyValue = fun k => M.divValue (F.callValue (denote a) k) (F.callValue (denote b) k)) :
    HasSequenceLimitValue M (denote g) (M.divValue (denote left) (denote right)) := by
  have hg : M.mem (denote g) (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))) := by
    have h := formulaFnInFnSet g
    change M.mem (denote g) (F.fnSetValue g.val.signature.domain g.val.signature.output) at h
    rwa [hD,hR] at h
  obtain ⟨l,hleft⟩ := (M.real_members _).mp hl
  obtain ⟨r,hright⟩ := (M.real_members _).mp hr
  have hrne : r ≠ 0 := by
    intro hz
    apply hne
    rw [hright,hz,Complex.ofReal_zero]
  change HasSequenceLimitValue M (denote a) (denote left) at hla
  change HasSequenceLimitValue M (denote b) (denote right) at hlb
  have hia := (sequenceLimit_iff_tendsto (denote a) l ha).mp (hleft ▸ hla)
  have hib := (sequenceLimit_iff_tendsto (denote b) r hb).mp (hright ▸ hlb)
  rw [hleft,hright,M.div_numbers _ _ (Complex.ofReal_ne_zero.mpr hrne),←Complex.ofReal_div]
  apply (sequenceLimit_iff_tendsto (denote g) (l/r) hg).mpr
  have hc : ContinuousAt (fun p : ℝ × ℝ => p.1/p.2) (l,r) :=
    continuous_fst.continuousAt.div continuous_snd.continuousAt hrne
  have hout : Tendsto (fun n => observeRealSequence (denote a) n / observeRealSequence (denote b) n) atTop (𝓝 (l/r)) :=
    hc.tendsto.comp (hia.prodMk_nhds hib)
  apply hout.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hd : M.mem (M.number (n : ℂ)) g.val.signature.domain :=
    hD.symm ▸ numberInNPosOfEq (n : ℂ) n rfl hnpos
  have hcall : F.callValue (denote g) (M.number (n : ℂ)) = g.val.bodyValue (M.number (n : ℂ)) :=
    F.call_graphValue _ _ _ g.wd _ hd
  have hbcall := observeRealSequence_spec (denote b) n hnpos hb
  have hbne : (observeRealSequence (denote b) n : ℂ) ≠ 0 := by
    intro hz
    apply hbn (M.number (n : ℂ)) (numberInNPosOfEq (n : ℂ) n rfl hnpos)
    rw [hbcall,hz]
  unfold observeRealSequence
  rw [hcall,hbody]
  dsimp only
  rw [observeRealSequence_spec (denote a) n hnpos ha,observeRealSequence_spec (denote b) n hnpos hb,
    M.div_numbers _ _ hbne]
  simp only [←Complex.ofReal_div,observeRealValue_number]
end Litex
