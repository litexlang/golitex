import examples.sequence_limit_unique.statement
open Filter
open scoped Topology
namespace Adapter
private noncomputable abbrev model := Litex.NumericModel.model
private noncomputable def decodeNat (x : model.Value) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, x = model.number (n : ℂ) then Classical.choose h else 0
private theorem decodeNat_number (n : ℕ) : decodeNat (model.number (n : ℂ)) = n := by
  classical
  have h : ∃ k : ℕ, model.number (n : ℂ) = model.number (k : ℂ) := ⟨n,rfl⟩
  have hk : Classical.choose h = n := (Nat.cast_injective (model.number_injective (Classical.choose_spec h))).symm
  unfold decodeNat
  rw [dif_pos h, hk]
private noncomputable def seqBody (f : ℕ → ℝ) (x : model.Value) : model.Value :=
  model.number ((f (decodeNat x) : ℝ) : ℂ)
private noncomputable def sequence (f : ℕ → ℝ) : Litex.Obj (M := model) (Litex.FormulaFn model) :=
  Litex.formulaFnOn (Litex.seqSignature (Litex.R (M := model))) (seqBody f) (by
    intro x hx
    exact (model.real_members _).mpr ⟨f (decodeNat x), rfl⟩)
private theorem sequence_mem (f : ℕ → ℝ) : Litex.In (sequence f) (Litex.seqSet (Litex.R (M := model)) (Litex.isSet (Litex.R (M := model)))) := by
  exact Litex.formulaFnInFnSet (sequence f)
private theorem sequence_call (f : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    Litex.FunctionSemantics.callValue (Litex.denote (sequence f)) (model.number (n : ℂ)) = model.number ((f n : ℝ) : ℂ) := by
  have hnmem := Litex.numberInNPosOfEq (M := model) (n : ℂ) n rfl hn
  have hd : model.mem (model.number (n : ℂ)) (sequence f).val.signature.domain := by
    change model.mem (model.number (n : ℂ)) ((Litex.seqSignature (Litex.R (M := model))).domain)
    exact (Litex.FunctionSignature.withGuard_domain _ _ _ _ _ _).mpr ⟨hnmem, True.intro⟩
  have h := Litex.FunctionSemantics.call_graphValue (sequence f).val.signature.domain (sequence f).val.signature.target (sequence f).val.bodyValue (sequence f).wd (model.number (n : ℂ)) hd
  change Litex.FunctionSemantics.callValue (Litex.denote (sequence f)) (model.number (n : ℂ)) = seqBody f (model.number (n : ℂ)) at h
  simpa only [seqBody, decodeNat_number] using h

private theorem nativeLimit_to_Litex (f : ℕ → ℝ) (L : ℝ)
    (h : Tendsto f atTop (𝓝 L)) :
    Litex.HasSequenceLimit (sequence f) (Litex.number (M := model) (L : ℂ)) := by
  intro epsilon hepsilon
  let epsilonObj : Litex.Obj (M := model) model.Value := Litex.semanticObject epsilon (model.member_isSet hepsilon)
  have heR : Litex.In epsilonObj Litex.R := Litex.inRPos_real epsilonObj hepsilon
  let delta := Litex.NativeBridge.asReal epsilonObj heR
  have hevalue : epsilon = model.number (delta : ℂ) := Litex.NativeBridge.asReal_spec epsilonObj heR
  have hdelta : 0 < delta := (Litex.NativeBridge.lt_iff_ofDenoteReal (Litex.number (M := model) 0) epsilonObj 0 delta rfl hevalue).mp (Litex.inRPos_positive epsilonObj hepsilon)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) delta hdelta
  let cutoff := N+1
  have hcut : 0 < cutoff := by dsimp [cutoff]; omega
  have hcutmem : model.mem (model.number (cutoff : ℂ)) (Litex.denote (Litex.NPos (M := model))) := Litex.numberInNPosOfEq (cutoff : ℂ) cutoff rfl hcut
  let c : Litex.Obj (M := model) model.Value := Litex.semanticObject (model.number (cutoff : ℂ)) (model.member_isSet hcutmem)
  refine ⟨c, hcutmem, ?_⟩
  intro index htail
  obtain ⟨hindex, _, r, s, hr, hs, hrs⟩ := (Litex.SetSemantics.sep_members _ _ _).mp htail
  have hnat : model.mem index (model.standard .natural) := ((Litex.SetSemantics.sep_members _ _ _).mp hindex).1
  obtain ⟨n, hn⟩ := (model.natural_members index).mp hnat
  change model.number (cutoff : ℂ) = model.number (r : ℂ) at hr
  have hrcut : (cutoff : ℝ) = r := Complex.ofReal_injective (model.number_injective (by simpa only [Complex.ofReal_natCast] using hr))
  have hsindex : (n : ℝ) = s := Complex.ofReal_injective (model.number_injective (by simpa only [Complex.ofReal_natCast] using hn.symm.trans hs))
  have hcutn : cutoff ≤ n := by exact_mod_cast (hrcut ▸ hsindex ▸ hrs)
  have hnpos : 0 < n := by omega
  have hNn : N ≤ n := by dsimp [cutoff] at hcutn; omega
  have hdist : |f n - L| < delta := by simpa only [Real.dist_eq] using hN n hNn
  have hindexGuard : model.mem index (Litex.seqSignature (Litex.R (M := model))).domain :=
    (Litex.FunctionSignature.withGuard_domain _ _ _ _ _ _).mpr ⟨hindex,True.intro⟩
  have hfn : model.mem (Litex.denote (sequence f)) (Litex.FunctionSemantics.fnSetValue (Litex.seqSignature (Litex.R (M := model))).domain (Litex.denote (Litex.R (M := model)))) := Litex.formulaFnInFnSet (sequence f)
  apply (Litex.FunctionSemantics.preimage_mem_iff (fun y => model.mem y (Litex.sequenceEpsilonBallValue (model.number (L : ℂ)) epsilon)) (Litex.seqSignature (Litex.R (M := model))).domain_isSet hfn).mpr
  refine ⟨hindexGuard, ?_⟩
  rw [hn, sequence_call f n hnpos]
  apply (Litex.SetSemantics.sep_members _ _ _).mpr
  have hreal : model.mem (model.number ((f n : ℝ) : ℂ)) (Litex.denote (Litex.R (M := model))) := (model.real_members _).mpr ⟨f n,rfl⟩
  refine ⟨hreal,hreal,|f n-L|,delta,?_,hevalue,hdist⟩
  rw [model.sub_numbers, ← Complex.ofReal_sub, Litex.absValue_number]


-- The proof uses the compiler-generated Litex theorem; the statement is native.
theorem sequenceLimitsUnique (f : ℕ → ℝ) (L K : ℝ)
    (hL : Tendsto f atTop (𝓝 L)) (hK : Tendsto f atTop (𝓝 K)) : L = K := by
  have generated := LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_limit_x5f_unique_x2f_statement_x2e_lit.h_4
    (M := model) (sequence f) (sequence_mem f)
    (Litex.number (M := model) (L : ℂ)) (Litex.NativeBridge.numberInROfEq (L : ℂ) L rfl)
    (Litex.number (M := model) (K : ℂ)) (Litex.NativeBridge.numberInROfEq (K : ℂ) K rfl)
    (nativeLimit_to_Litex f L hL) (nativeLimit_to_Litex f K hK)
  exact Complex.ofReal_injective (Litex.NativeBridge.complexEq generated)
end Adapter
