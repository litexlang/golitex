import Litex.SequenceExtremaEpsilon

universe u
open Filter
open scoped Topology
namespace Litex

/-- The same two finite-extremum clauses on real observations and natural indices. -/
def NativeSequenceExtremum (upper : Bool) (a : ℕ → ℝ) (value : ℝ) : Prop :=
  (∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℕ, ∀ n, cutoff ≤ n →
    if upper then a n < value + epsilon else value - epsilon < a n) ∧
  (∀ epsilon : ℝ, 0 < epsilon → ∀ cutoff : ℕ, ∃ n : ℕ, 0 < n ∧ cutoff ≤ n ∧
    (if upper then value - epsilon < a n else a n < value + epsilon))

theorem sequenceExtremum_iff_native {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a : M.Value) (value : ℝ)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M))))) :
    HasSequenceExtremumValue M upper a (M.number (value : ℂ)) ↔
      NativeSequenceExtremum upper (observeRealSequence a) value := by
  constructor
  · intro h
    constructor
    · intro epsilon he
      obtain ⟨cutoff, hc, hb⟩ := h.1 _ (numberInRPos epsilon he)
      let cut := NativeBridge.asNat cutoff (inNPos_natural cutoff hc)
      refine ⟨cut + 1, ?_⟩
      intro n hn
      exact sequenceExtremumBoundAtIndex upper a value epsilon cutoff hc n (by omega)
        (by omega) hf hb
    · intro epsilon he N
      have hc := numberInNPosOfEq (M := M) ((N + 1 : ℕ) : ℂ) (N + 1) rfl (by omega)
      let cutoff : Obj (M := M) M.Value := semanticObject (M.number ((N + 1 : ℕ) : ℂ)) (M.member_isSet hc)
      obtain ⟨n, hn, hge, hh⟩ := sequenceExtremumHitAtTail upper a value epsilon cutoff hc hf
        (h.2 _ (numberInRPos epsilon he) _ hc)
      have hcut := NativeBridge.asNat_ofDenote cutoff (inNPos_natural cutoff hc) (N + 1) rfl
      rw [hcut] at hge
      exact ⟨n, hn, by omega, hh⟩
  · rintro ⟨hb, hh⟩
    constructor
    · intro epsilon he
      let e := semanticObject epsilon (M.member_isSet he)
      have her : In e R := inRPos_real e he
      let delta := NativeBridge.asReal e her
      have hev : epsilon = M.number (delta : ℂ) := NativeBridge.asReal_spec e her
      have hd : 0 < delta := (NativeBridge.lt_iff_ofDenoteReal (number (M := M) 0) e 0 delta rfl hev).mp
        (inRPos_positive e he)
      obtain ⟨N, hN⟩ := hb delta hd
      let cut := N + 1
      have hc := numberInNPosOfEq (M := M) (cut : ℂ) cut rfl (by dsimp [cut]; omega)
      let cutoff : Obj (M := M) M.Value := semanticObject (M.number (cut : ℂ)) (M.member_isSet hc)
      have hcut := NativeBridge.asNat_ofDenote cutoff (inNPos_natural cutoff hc) cut rfl
      refine ⟨cutoff, hc, ?_⟩
      intro index htail
      obtain ⟨n, hn, hval, hge⟩ := sequenceTail_index cutoff hc index htail
      rw [hcut] at hge
      have hNn : N ≤ n := by dsimp [cut] at hge; omega
      have hnmem := ((F.sep_members _ _ _).mp htail).1
      apply (F.preimage_mem_iff
        (fun y => M.mem y (sequenceExtremumRayValue upper (M.number (value : ℂ)) epsilon))
        (isSet (NPos (M := M))) hf).mpr
      refine ⟨hnmem, ?_⟩
      rw [hval, observeRealSequence_spec a n hn hf]
      apply (F.sep_members _ _ _).mpr
      have hreal : M.mem (M.number (observeRealSequence a n : ℂ)) (denote (R (M := M))) :=
        (M.real_members _).mpr ⟨_, rfl⟩
      refine ⟨hreal, hreal, ?_⟩
      have ho := hN n hNn
      rw [hev]
      cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, M.add_numbers, M.sub_numbers,
        ← Complex.ofReal_add, ← Complex.ofReal_sub, realLtValue_numbers] at ho ⊢ <;> exact ho
    · intro epsilon he cutoff hc
      let e := semanticObject epsilon (M.member_isSet he)
      have her : In e R := inRPos_real e he
      let delta := NativeBridge.asReal e her
      have hev : epsilon = M.number (delta : ℂ) := NativeBridge.asReal_spec e her
      have hd : 0 < delta := (NativeBridge.lt_iff_ofDenoteReal (number (M := M) 0) e 0 delta rfl hev).mp
        (inRPos_positive e he)
      let c := semanticObject cutoff (M.member_isSet hc)
      let cut := NativeBridge.asNat c (inNPos_natural c hc)
      have hcv : cutoff = M.number (cut : ℂ) := NativeBridge.asNat_spec c (inNPos_natural c hc)
      obtain ⟨n, hn, hge, ho⟩ := hh delta hd cut
      have hnmem := numberInNPosOfEq (M := M) (n : ℂ) n rfl hn
      let index : Obj (M := M) M.Value := semanticObject (M.number (n : ℂ)) (M.member_isSet hnmem)
      refine ⟨index, hnmem, ⟨(cut : ℝ), (n : ℝ), ?_, ?_, ?_⟩, ?_⟩
      · simpa only [Complex.ofReal_natCast] using hcv
      · change M.number (n : ℂ) = M.number ((n : ℝ) : ℂ)
        rw [Complex.ofReal_natCast]
      · exact_mod_cast hge
      · change (if upper then RealLtValue M (M.subValue (M.number (value : ℂ)) epsilon)
            (F.callValue a (M.number (n : ℂ))) else
            RealLtValue M (F.callValue a (M.number (n : ℂ))) (M.addValue (M.number (value : ℂ)) epsilon))
        rw [hev, observeRealSequence_spec a n hn hf]
        cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, M.add_numbers, M.sub_numbers,
          ← Complex.ofReal_add, ← Complex.ofReal_sub, realLtValue_numbers] at ho ⊢ <;> exact ho

private theorem native_extremum_congr (upper : Bool) (f g : ℕ → ℝ) (r : ℝ)
    (h : NativeSequenceExtremum upper f r) (K : ℕ)
    (heq : ∀ n, K ≤ n → f n = g n) : NativeSequenceExtremum upper g r := by
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := h.1 e he
    refine ⟨Max.max N K, ?_⟩
    intro n hn
    rw [← heq n (le_trans (le_max_right _ _) hn)]
    exact hN n (le_trans (le_max_left _ _) hn)
  · intro e he N
    obtain ⟨n, hn, hge, ho⟩ := h.2 e he (Max.max N K)
    refine ⟨n, hn, le_trans (le_max_left _ _) hge, ?_⟩
    rwa [← heq n (le_trans (le_max_right _ _) hge)]

private theorem native_extremum_shift (upper : Bool) (f : ℕ → ℝ) (r : ℝ)
    (h : NativeSequenceExtremum upper f r) (k : ℕ) :
    NativeSequenceExtremum upper (fun n => f (n + k)) r := by
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := h.1 e he
    exact ⟨N, fun n hn => hN (n + k) (by omega)⟩
  · intro e he N
    obtain ⟨m, hm, hge, ho⟩ := h.2 e he (N + k + 1)
    refine ⟨m - k, by omega, by omega, ?_⟩
    simpa only [Nat.sub_add_cancel (show k ≤ m by omega)] using ho

private theorem native_extremum_neg (upper : Bool) (f : ℕ → ℝ) (r : ℝ)
    (h : NativeSequenceExtremum upper f r) :
    NativeSequenceExtremum (!upper) (fun n => -f n) (-r) := by
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := h.1 e he
    refine ⟨N, ?_⟩
    intro n hn
    have ho := hN n hn
    cases upper <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;> linarith
  · intro e he N
    obtain ⟨n, hn, hge, ho⟩ := h.2 e he N
    refine ⟨n, hn, hge, ?_⟩
    cases upper <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;> linarith

private theorem native_extremum_compare (upper : Bool) (f g : ℕ → ℝ) (r s : ℝ)
    (hf : NativeSequenceExtremum upper f r) (hg : NativeSequenceExtremum upper g s)
    (K : ℕ) (ho : ∀ n, K ≤ n → f n ≤ g n) : r ≤ s := by
  by_contra h
  have he : 0 < (r - s) / 3 := by linarith
  cases upper
  · obtain ⟨N, hN⟩ := hf.1 _ he
    obtain ⟨n, _, hge, hhit⟩ := hg.2 _ he (Max.max N K)
    have hb := hN n (le_trans (le_max_left _ _) hge)
    have hle := ho n (le_trans (le_max_right _ _) hge)
    simp only [Bool.false_eq_true, ↓reduceIte] at hb hhit
    linarith
  · obtain ⟨N, hN⟩ := hg.1 _ he
    obtain ⟨n, _, hge, hhit⟩ := hf.2 _ he (Max.max N K)
    have hb := hN n (le_trans (le_max_left _ _) hge)
    have hle := ho n (le_trans (le_max_right _ _) hge)
    simp only [↓reduceIte] at hb hhit
    linarith

private theorem native_cutoff_context {M : Semantics.{u}} [FunctionSemantics M]
    (cutoff : M.Value) (hc : M.mem cutoff (denote (NPos (M := M)))) :
    ∃ K : ℕ, ∀ n, K ≤ n → 0 < n ∧ RealLeValue M cutoff (M.number (n : ℂ)) := by
  let c := semanticObject cutoff (M.member_isSet hc)
  let cut := NativeBridge.asNat c (inNPos_natural c hc)
  have hcv : cutoff = M.number (cut : ℂ) := NativeBridge.asNat_spec c (inNPos_natural c hc)
  refine ⟨cut + 1, ?_⟩
  intro n hn
  refine ⟨by omega, ?_⟩
  rw [hcv]
  apply (realLeValue_numbers (cut : ℝ) (n : ℝ)).mpr
  exact_mod_cast (show cut ≤ n by omega)

theorem sequenceExtremumEventuallyEqual {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b value cutoff : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M))))
    (hc : M.mem cutoff (denote (NPos (M := M))))
    (h : HasSequenceExtremumValue M upper a value)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) → RealLeValue M cutoff n →
      F.callValue b n = F.callValue a n) : HasSequenceExtremumValue M upper b value := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  rw [hr] at h ⊢
  obtain ⟨K, hK⟩ := native_cutoff_context cutoff hc
  apply (sequenceExtremum_iff_native upper b r hb).mpr
  apply native_extremum_congr upper (observeRealSequence a) (observeRealSequence b) r
    ((sequenceExtremum_iff_native upper a r ha).mp h) K
  intro n hn
  obtain ⟨hnpos, ho⟩ := hK n hn
  exact congrArg observeRealValue (heq (M.number (n : ℂ)) (numberInNPosOfEq (n : ℂ) n rfl hnpos) ho).symm

theorem sequenceExtremumShift {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b value amount : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M)))) (hm : M.mem amount (denote (N (M := M))))
    (h : HasSequenceExtremumValue M upper a value)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue b n = F.callValue a (M.addValue n amount)) :
    HasSequenceExtremumValue M upper b value := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  obtain ⟨k, hk⟩ := (M.natural_members amount).mp hm
  rw [hr] at h ⊢
  apply (sequenceExtremum_iff_native upper b r hb).mpr
  apply native_extremum_congr upper (fun n => observeRealSequence a (n + k))
    (observeRealSequence b) r (native_extremum_shift upper _ r
      ((sequenceExtremum_iff_native upper a r ha).mp h) k) 1
  intro n hn
  have he := heq (M.number (n : ℂ)) (numberInNPosOfEq (n : ℂ) n rfl (by omega))
  rw [hk, M.add_numbers, ← Nat.cast_add] at he
  exact congrArg observeRealValue he.symm

theorem sequenceExtremumNeg {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b value : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M))))
    (h : HasSequenceExtremumValue M upper a value)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) → F.callValue b n = M.negValue (F.callValue a n)) :
    HasSequenceExtremumValue M (!upper) b (M.negValue value) := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  rw [hr] at h
  rw [hr, M.neg_numbers, ← Complex.ofReal_neg]
  apply (sequenceExtremum_iff_native (!upper) b (-r) hb).mpr
  apply native_extremum_congr (!upper) (fun n => -observeRealSequence a n)
    (observeRealSequence b) (-r) (native_extremum_neg upper _ r
      ((sequenceExtremum_iff_native upper a r ha).mp h)) 1
  intro n hn
  have hnpos : 0 < n := by omega
  have he := heq (M.number (n : ℂ)) (numberInNPosOfEq (n : ℂ) n rfl hnpos)
  rw [observeRealSequence_spec a n hnpos ha, M.neg_numbers, ← Complex.ofReal_neg] at he
  have hspec := observeRealSequence_spec b n hnpos hb
  exact (Complex.ofReal_injective (M.number_injective (hspec.symm.trans he))).symm

theorem sequenceExtremumCompare {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b left right cutoff : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : M.mem left (denote (R (M := M)))) (hr : M.mem right (denote (R (M := M))))
    (hc : M.mem cutoff (denote (NPos (M := M))))
    (hla : HasSequenceExtremumValue M upper a left) (hlb : HasSequenceExtremumValue M upper b right)
    (ho : ∀ n, M.mem n (denote (NPos (M := M))) → RealLeValue M cutoff n →
      RealLeValue M (F.callValue a n) (F.callValue b n)) : RealLeValue M left right := by
  obtain ⟨r, hleft⟩ := (M.real_members left).mp hl
  obtain ⟨s, hright⟩ := (M.real_members right).mp hr
  rw [hleft] at hla
  rw [hright] at hlb
  rw [hleft, hright]
  apply (realLeValue_numbers r s).mpr
  obtain ⟨K, hK⟩ := native_cutoff_context cutoff hc
  apply native_extremum_compare upper (observeRealSequence a) (observeRealSequence b) r s
    ((sequenceExtremum_iff_native upper a r ha).mp hla)
    ((sequenceExtremum_iff_native upper b s hb).mp hlb) K
  intro n hn
  obtain ⟨hnpos, horder⟩ := hK n hn
  have h := ho _ (numberInNPosOfEq (n : ℂ) n rfl hnpos) horder
  have transported := (congrArg₂ (RealLeValue M) (observeRealSequence_spec a n hnpos ha)
    (observeRealSequence_spec b n hnpos hb)) ▸ h
  exact (realLeValue_numbers _ _).mp transported

private theorem native_limit_from_extrema (f : ℕ → ℝ) (r : ℝ)
    (hu : NativeSequenceExtremum true f r) (hl : NativeSequenceExtremum false f r) :
    Tendsto f atTop (𝓝 r) := by
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨N, hN⟩ := hu.1 e he
  obtain ⟨P, hP⟩ := hl.1 e he
  refine ⟨Max.max N P, ?_⟩
  intro n hn
  have hup := hN n (le_trans (le_max_left _ _) hn)
  have hlo := hP n (le_trans (le_max_right _ _) hn)
  change f n < r + e at hup
  change r - e < f n at hlo
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem native_extrema_order (f : ℕ → ℝ) (l u : ℝ)
    (hl : NativeSequenceExtremum false f l) (hu : NativeSequenceExtremum true f u) : l ≤ u := by
  by_contra h
  have he : 0 < (l - u) / 3 := by linarith
  obtain ⟨N, hN⟩ := hl.1 _ he
  obtain ⟨P, hP⟩ := hu.1 _ he
  have hlo := hN (Max.max N P) (le_max_left _ _)
  have hup := hP (Max.max N P) (le_max_right _ _)
  change l - (l - u) / 3 < f (Max.max N P) at hlo
  change f (Max.max N P) < u + (l - u) / 3 at hup
  linarith

theorem sequenceLimitFromExtrema {M : Semantics.{u}} [F : FunctionSemantics M]
    (a value : M.Value)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M))))
    (hu : HasSequenceExtremumValue M true a value) (hl : HasSequenceExtremumValue M false a value) :
    HasSequenceLimitValue M a value := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  rw [hr] at hu hl ⊢
  apply (sequenceLimit_iff_tendsto a r hf).mpr
  exact native_limit_from_extrema _ r ((sequenceExtremum_iff_native true a r hf).mp hu)
    ((sequenceExtremum_iff_native false a r hf).mp hl)

theorem sequenceExtremaOrder {M : Semantics.{u}} [F : FunctionSemantics M]
    (a lower upper : M.Value)
    (hf : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : M.mem lower (denote (R (M := M)))) (hu : M.mem upper (denote (R (M := M))))
    (hlo : HasSequenceExtremumValue M false a lower) (hup : HasSequenceExtremumValue M true a upper) :
    RealLeValue M lower upper := by
  obtain ⟨l, hleft⟩ := (M.real_members lower).mp hl
  obtain ⟨u, hright⟩ := (M.real_members upper).mp hu
  rw [hleft] at hlo
  rw [hright] at hup
  rw [hleft, hright]
  apply (realLeValue_numbers l u).mpr
  exact native_extrema_order _ l u ((sequenceExtremum_iff_native false a l hf).mp hlo)
    ((sequenceExtremum_iff_native true a u hf).mp hup)

end Litex
