import Litex.SequenceExtremaTransport

universe u
open Filter
open scoped Topology
namespace Litex

private theorem affine_native_congr (upper : Bool) (f g : ℕ → ℝ) (r : ℝ)
    (h : NativeSequenceExtremum upper f r)
    (heq : ∀ n, 0 < n → f n = g n) : NativeSequenceExtremum upper g r := by
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := h.1 e he
    refine ⟨N + 1, ?_⟩
    intro n hn
    rw [← heq n (by omega)]
    exact hN n (by omega)
  · intro e he N
    obtain ⟨n, hn, hge, ho⟩ := h.2 e he N
    exact ⟨n, hn, hge, (heq n hn) ▸ ho⟩

private theorem affine_native_add_constant (upper : Bool) (f : ℕ → ℝ) (r c : ℝ)
    (h : NativeSequenceExtremum upper f r) :
    NativeSequenceExtremum upper (fun n => f n + c) (r + c) := by
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := h.1 e he
    refine ⟨N, ?_⟩
    intro n hn
    have ho := hN n hn
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;> linarith
  · intro e he N
    obtain ⟨n, hn, hge, ho⟩ := h.2 e he N
    refine ⟨n, hn, hge, ?_⟩
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;> linarith

private theorem affine_native_scale_positive (upper : Bool) (f : ℕ → ℝ) (r c : ℝ)
    (hc : 0 < c) (h : NativeSequenceExtremum upper f r) :
    NativeSequenceExtremum upper (fun n => c * f n) (c * r) := by
  constructor
  · intro e he
    have hd : 0 < e / c := div_pos he hc
    have hce : c * (e / c) = e := mul_div_cancel₀ e (ne_of_gt hc)
    obtain ⟨N, hN⟩ := h.1 _ hd
    refine ⟨N, ?_⟩
    intro n hn
    have ho := hN n hn
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho ⊢
    · have ht := mul_lt_mul_of_pos_left ho hc
      nlinarith [ht]
    · have ht := mul_lt_mul_of_pos_left ho hc
      nlinarith [ht]
  · intro e he N
    have hd : 0 < e / c := div_pos he hc
    have hce : c * (e / c) = e := mul_div_cancel₀ e (ne_of_gt hc)
    obtain ⟨n, hn, hge, ho⟩ := h.2 _ hd N
    refine ⟨n, hn, hge, ?_⟩
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho ⊢
    · have ht := mul_lt_mul_of_pos_left ho hc
      nlinarith [ht]
    · have ht := mul_lt_mul_of_pos_left ho hc
      nlinarith [ht]

private theorem affine_native_scale_nonnegative (upper : Bool) (f : ℕ → ℝ) (r c : ℝ)
    (hc : 0 ≤ c) (h : NativeSequenceExtremum upper f r) :
    NativeSequenceExtremum upper (fun n => c * f n) (c * r) := by
  rcases hc.eq_or_lt with hzero | hpos
  · subst c
    constructor
    · intro e he
      exact ⟨0, fun _ _ => by cases upper <;> simpa using he⟩
    · intro e he N
      exact ⟨N + 1, by omega, by omega, by cases upper <;> simpa using he⟩
  · exact affine_native_scale_positive upper f r c hpos h

private theorem affine_native_scale_negative (upper : Bool) (f : ℕ → ℝ) (r c : ℝ)
    (hc : c < 0) (h : NativeSequenceExtremum upper f r) :
    NativeSequenceExtremum (!upper) (fun n => c * f n) (c * r) := by
  constructor
  · intro e he
    have hd : 0 < e / (-c) := div_pos he (neg_pos.mpr hc)
    have hce : c * (e / (-c)) = -e := by
      have hx := mul_div_cancel₀ e (ne_of_gt (neg_pos.mpr hc))
      nlinarith [hx]
    obtain ⟨N, hN⟩ := h.1 _ hd
    refine ⟨N, ?_⟩
    intro n hn
    have ho := hN n hn
    cases upper <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    · have ht := mul_lt_mul_of_neg_left ho hc
      nlinarith [ht]
    · have ht := mul_lt_mul_of_neg_left ho hc
      nlinarith [ht]
  · intro e he N
    have hd : 0 < e / (-c) := div_pos he (neg_pos.mpr hc)
    have hce : c * (e / (-c)) = -e := by
      have hx := mul_div_cancel₀ e (ne_of_gt (neg_pos.mpr hc))
      nlinarith [hx]
    obtain ⟨n, hn, hge, ho⟩ := h.2 _ hd N
    refine ⟨n, hn, hge, ?_⟩
    cases upper <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho ⊢
    · have ht := mul_lt_mul_of_neg_left ho hc
      nlinarith [ht]
    · have ht := mul_lt_mul_of_neg_left ho hc
      nlinarith [ht]

private theorem affine_native_add_convergent (upper : Bool) (f g : ℕ → ℝ) (r s : ℝ)
    (hf : NativeSequenceExtremum upper f r) (hg : Tendsto g atTop (𝓝 s)) :
    NativeSequenceExtremum upper (fun n => f n + g n) (r + s) := by
  constructor
  · intro e he
    have hd : 0 < e / 2 := by linarith
    obtain ⟨N, hN⟩ := hf.1 _ hd
    obtain ⟨P, hP⟩ := Metric.tendsto_atTop.mp hg _ hd
    refine ⟨Max.max N P, ?_⟩
    intro n hn
    have ho := hN n (le_trans (le_max_left _ _) hn)
    have hd := hP n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq] at hd
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hd
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;> linarith
  · intro e he N
    have hd : 0 < e / 2 := by linarith
    obtain ⟨P, hP⟩ := Metric.tendsto_atTop.mp hg _ hd
    obtain ⟨n, hn, hge, ho⟩ := hf.2 _ hd (Max.max N P)
    have hd := hP n (le_trans (le_max_right _ _) hge)
    rw [Real.dist_eq] at hd
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hd
    refine ⟨n, hn, le_trans (le_max_left _ _) hge, ?_⟩
    cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho ⊢ <;> linarith

private theorem affine_native_sum_bound (upper : Bool) (f g : ℕ → ℝ) (r s t : ℝ)
    (hf : NativeSequenceExtremum upper f r) (hg : NativeSequenceExtremum upper g s)
    (hh : NativeSequenceExtremum upper (fun n => f n + g n) t) :
    if upper then t ≤ r + s else r + s ≤ t := by
  cases upper
  · change r + s ≤ t
    by_contra h
    have he : 0 < (r + s - t) / 3 := by linarith
    obtain ⟨N, hN⟩ := hf.1 _ he
    obtain ⟨P, hP⟩ := hg.1 _ he
    obtain ⟨n, _, hn, ho⟩ := hh.2 _ he (Max.max N P)
    have ha := hN n (le_trans (le_max_left _ _) hn)
    have hb := hP n (le_trans (le_max_right _ _) hn)
    simp only [Bool.false_eq_true, ↓reduceIte] at ha hb ho
    linarith
  · change t ≤ r + s
    by_contra h
    have he : 0 < (t - (r + s)) / 3 := by linarith
    obtain ⟨N, hN⟩ := hf.1 _ he
    obtain ⟨P, hP⟩ := hg.1 _ he
    obtain ⟨n, _, hn, ho⟩ := hh.2 _ he (Max.max N P)
    have ha := hN n (le_trans (le_max_left _ _) hn)
    have hb := hP n (le_trans (le_max_right _ _) hn)
    simp only [↓reduceIte] at ha hb ho
    linarith

private theorem affine_observe_add {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b h : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hh : M.mem h (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue h n = M.addValue (F.callValue a n) (F.callValue b n))
    (n : ℕ) (hn : 0 < n) :
    observeRealSequence h n = observeRealSequence a n + observeRealSequence b n := by
  have he := heq (M.number (n : ℂ)) (numberInNPosOfEq (n : ℂ) n rfl hn)
  rw [observeRealSequence_spec a n hn ha, observeRealSequence_spec b n hn hb,
    M.add_numbers, ← Complex.ofReal_add] at he
  exact Complex.ofReal_injective (M.number_injective ((observeRealSequence_spec h n hn hh).symm.trans he))

theorem sequenceExtremumAddConstant {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b value scalar : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M)))) (hc : M.mem scalar (denote (R (M := M))))
    (h : HasSequenceExtremumValue M upper a value)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue b n = M.addValue (F.callValue a n) scalar) :
    HasSequenceExtremumValue M upper b (M.addValue value scalar) := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  obtain ⟨c, hcs⟩ := (M.real_members scalar).mp hc
  rw [hr] at h
  rw [hr, hcs, M.add_numbers, ← Complex.ofReal_add]
  apply (sequenceExtremum_iff_native upper b (r + c) hb).mpr
  apply affine_native_congr upper (fun n => observeRealSequence a n + c)
    (observeRealSequence b) (r + c)
    (affine_native_add_constant upper _ r c ((sequenceExtremum_iff_native upper a r ha).mp h))
  intro n hn
  have he := heq (M.number (n : ℂ)) (numberInNPosOfEq (n : ℂ) n rfl hn)
  rw [hcs, observeRealSequence_spec a n hn ha, M.add_numbers, ← Complex.ofReal_add] at he
  exact (Complex.ofReal_injective (M.number_injective ((observeRealSequence_spec b n hn hb).symm.trans he))).symm

private theorem affine_observe_scale {M : Semantics.{u}} [F : FunctionSemantics M]
    (a b : M.Value) (c : ℝ)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue b n = M.mulValue (M.number (c : ℂ)) (F.callValue a n))
    (n : ℕ) (hn : 0 < n) : c * observeRealSequence a n = observeRealSequence b n := by
  have he := heq (M.number (n : ℂ)) (numberInNPosOfEq (n : ℂ) n rfl hn)
  rw [observeRealSequence_spec a n hn ha, M.mul_numbers, ← Complex.ofReal_mul] at he
  exact (Complex.ofReal_injective (M.number_injective ((observeRealSequence_spec b n hn hb).symm.trans he))).symm

theorem sequenceExtremumScaleNonnegative {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b value scalar : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M)))) (hc : M.mem scalar (denote (R (M := M))))
    (hnonneg : RealLeValue M (M.number 0) scalar)
    (h : HasSequenceExtremumValue M upper a value)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue b n = M.mulValue scalar (F.callValue a n)) :
    HasSequenceExtremumValue M upper b (M.mulValue scalar value) := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  obtain ⟨c, hcs⟩ := (M.real_members scalar).mp hc
  rw [hr] at h
  rw [hcs] at hnonneg heq
  rw [hr, hcs, M.mul_numbers, ← Complex.ofReal_mul]
  apply (sequenceExtremum_iff_native upper b (c * r) hb).mpr
  apply affine_native_congr upper (fun n => c * observeRealSequence a n)
    (observeRealSequence b) (c * r)
    (affine_native_scale_nonnegative upper _ r c ((realLeValue_numbers 0 c).mp hnonneg)
      ((sequenceExtremum_iff_native upper a r ha).mp h))
  exact affine_observe_scale a b c ha hb heq

theorem sequenceExtremumScaleNegative {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b value scalar : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hv : M.mem value (denote (R (M := M)))) (hc : M.mem scalar (denote (R (M := M))))
    (hneg : RealLtValue M scalar (M.number 0))
    (h : HasSequenceExtremumValue M upper a value)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue b n = M.mulValue scalar (F.callValue a n)) :
    HasSequenceExtremumValue M (!upper) b (M.mulValue scalar value) := by
  obtain ⟨r, hr⟩ := (M.real_members value).mp hv
  obtain ⟨c, hcs⟩ := (M.real_members scalar).mp hc
  rw [hr] at h
  rw [hcs] at hneg heq
  rw [hr, hcs, M.mul_numbers, ← Complex.ofReal_mul]
  apply (sequenceExtremum_iff_native (!upper) b (c * r) hb).mpr
  apply affine_native_congr (!upper) (fun n => c * observeRealSequence a n)
    (observeRealSequence b) (c * r)
    (affine_native_scale_negative upper _ r c ((realLtValue_numbers c 0).mp hneg)
      ((sequenceExtremum_iff_native upper a r ha).mp h))
  exact affine_observe_scale a b c ha hb heq

theorem sequenceExtremumAddConvergent {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b h left right : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hh : M.mem h (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : M.mem left (denote (R (M := M)))) (hr : M.mem right (denote (R (M := M))))
    (hla : HasSequenceExtremumValue M upper a left) (hlb : HasSequenceLimitValue M b right)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue h n = M.addValue (F.callValue a n) (F.callValue b n)) :
    HasSequenceExtremumValue M upper h (M.addValue left right) := by
  obtain ⟨r, hleft⟩ := (M.real_members left).mp hl
  obtain ⟨s, hright⟩ := (M.real_members right).mp hr
  rw [hleft] at hla
  rw [hright] at hlb
  rw [hleft, hright, M.add_numbers, ← Complex.ofReal_add]
  apply (sequenceExtremum_iff_native upper h (r + s) hh).mpr
  apply affine_native_congr upper (fun n => observeRealSequence a n + observeRealSequence b n)
    (observeRealSequence h) (r + s)
    (affine_native_add_convergent upper _ _ r s ((sequenceExtremum_iff_native upper a r ha).mp hla)
      ((sequenceLimit_iff_tendsto b s hb).mp hlb))
  intro n hn
  exact (affine_observe_add a b h ha hb hh heq n hn).symm

theorem sequenceExtremumSumBound {M : Semantics.{u}} [F : FunctionSemantics M]
    (upper : Bool) (a b h left right value : M.Value)
    (ha : M.mem a (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hb : M.mem b (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hh : M.mem h (F.fnSetValue (denote (NPos (M := M))) (denote (R (M := M)))))
    (hl : M.mem left (denote (R (M := M)))) (hr : M.mem right (denote (R (M := M))))
    (hv : M.mem value (denote (R (M := M))))
    (hla : HasSequenceExtremumValue M upper a left) (hlb : HasSequenceExtremumValue M upper b right)
    (hlh : HasSequenceExtremumValue M upper h value)
    (heq : ∀ n, M.mem n (denote (NPos (M := M))) →
      F.callValue h n = M.addValue (F.callValue a n) (F.callValue b n)) :
    if upper then RealLeValue M value (M.addValue left right)
      else RealLeValue M (M.addValue left right) value := by
  obtain ⟨r, hleft⟩ := (M.real_members left).mp hl
  obtain ⟨s, hright⟩ := (M.real_members right).mp hr
  obtain ⟨t, hvalue⟩ := (M.real_members value).mp hv
  rw [hleft] at hla
  rw [hright] at hlb
  rw [hvalue] at hlh
  have hn := (sequenceExtremum_iff_native upper h t hh).mp hlh
  have hs := affine_native_congr upper (observeRealSequence h)
    (fun n => observeRealSequence a n + observeRealSequence b n) t hn
    (affine_observe_add a b h ha hb hh heq)
  have ho := affine_native_sum_bound upper _ _ r s t
    ((sequenceExtremum_iff_native upper a r ha).mp hla)
    ((sequenceExtremum_iff_native upper b s hb).mp hlb) hs
  rw [hleft, hright, hvalue, M.add_numbers, ← Complex.ofReal_add]
  cases upper <;> simpa only [Bool.false_eq_true, ↓reduceIte, realLeValue_numbers] using ho

end Litex
