import Litex.BuiltinTranscendental
universe u v w x y
namespace Litex

theorem logarithmProductBaseValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (LogObj (M := M) α β))
    (q : Obj (M := M) (LogObj (M := M) γ δ))
    (hbase : Same p.val.base q.val.base)
    (hguard : Lt (number 0) p.val.base ∧ ¬ Same p.val.base (number 1))
    (hx : Lt (number 0) p.val.arg) (hy : Lt (number 0) q.val.arg) :
    M.divValue (realUnaryValue Real.log (M.mulValue (denote p.val.arg) (denote q.val.arg)))
      (realUnaryValue Real.log (denote p.val.base)) = M.addValue (denote p) (denote q) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2.1
  obtain ⟨t, ht⟩ := (M.real_members _).mp q.wd.2.1
  have hs0 := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 s rfl hs).mp hx
  have ht0 := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 t rfl ht).mp hy
  have hn := logBaseNonzero p.val.base r hr hguard.1 hguard.2
  rw [denoteLog p r s hr hs, denoteLog q r t (hbase.symm.trans hr) ht,
    hr, hs, ht, M.mul_numbers, ← Complex.ofReal_mul, realUnaryValue_number,
    realUnaryValue_number, M.div_numbers _ _ hn, M.add_numbers,
    ← Complex.ofReal_div, ← Complex.ofReal_add]
  congr 1
  rw [Real.log_mul (ne_of_gt hs0) (ne_of_gt ht0), add_div]

theorem logarithmQuotientBaseValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (LogObj (M := M) α β))
    (q : Obj (M := M) (LogObj (M := M) γ δ))
    (hbase : Same p.val.base q.val.base)
    (hguard : Lt (number 0) p.val.base ∧ ¬ Same p.val.base (number 1))
    (hx : Lt (number 0) p.val.arg) (hy : Lt (number 0) q.val.arg) :
    M.divValue (realUnaryValue Real.log (M.divValue (denote p.val.arg) (denote q.val.arg)))
      (realUnaryValue Real.log (denote p.val.base)) = M.subValue (denote p) (denote q) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2.1
  obtain ⟨t, ht⟩ := (M.real_members _).mp q.wd.2.1
  have hs0 := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 s rfl hs).mp hx
  have ht0 := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 t rfl ht).mp hy
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht0)
  have hn := logBaseNonzero p.val.base r hr hguard.1 hguard.2
  rw [denoteLog p r s hr hs, denoteLog q r t (hbase.symm.trans hr) ht,
    hr, hs, ht, M.div_numbers _ _ htC, ← Complex.ofReal_div, realUnaryValue_number,
    realUnaryValue_number, M.div_numbers _ _ hn, M.sub_numbers,
    ← Complex.ofReal_div, ← Complex.ofReal_sub]
  congr 1
  rw [Real.log_div (ne_of_gt hs0) (ne_of_gt ht0), sub_div]

theorem logarithmReciprocalValue {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (LogObj (M := M) α β))
    (hguard : Lt (number 0) p.val.base ∧ ¬ Same p.val.base (number 1))
    (hx : Lt (number 0) p.val.arg) :
    M.divValue (realUnaryValue Real.log (M.divValue (M.number 1) (denote p.val.arg)))
      (realUnaryValue Real.log (denote p.val.base)) = M.subValue (M.number 0) (denote p) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2.1
  have hs0 := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 s rfl hs).mp hx
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs0)
  have hn := logBaseNonzero p.val.base r hr hguard.1 hguard.2
  rw [denoteLog p r s hr hs, hr, hs, M.div_numbers _ _ hsC,
    ← Complex.ofReal_one, ← Complex.ofReal_div, realUnaryValue_number,
    realUnaryValue_number, M.div_numbers _ _ hn, M.sub_numbers,
    ← Complex.ofReal_div, ← Complex.ofReal_zero, ← Complex.ofReal_sub]
  congr 1
  rw [Real.log_div one_ne_zero (ne_of_gt hs0), Real.log_one, sub_div, zero_div]

theorem logarithmChangeBaseValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (LogObj (M := M) α β))
    (q : Obj (M := M) (LogObj (M := M) γ δ))
    (hbase : Same p.val.base q.val.base)
    (hguard : Lt (number 0) q.val.arg ∧ ¬ Same q.val.arg (number 1))
    (hchosen : Lt (number 0) p.val.base ∧ ¬ Same p.val.base (number 1))
    (_hx : Lt (number 0) p.val.arg) :
    M.divValue (realUnaryValue Real.log (denote p.val.arg))
      (realUnaryValue Real.log (denote q.val.arg)) = M.divValue (denote p) (denote q) := by
  obtain ⟨c, hc⟩ := (M.real_members _).mp p.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp p.wd.2.1
  obtain ⟨b, hb⟩ := (M.real_members _).mp q.wd.2.1
  have hcC := logBaseNonzero p.val.base c hc hchosen.1 hchosen.2
  have hbC := logBaseNonzero q.val.arg b hb hguard.1 hguard.2
  have hc0 : Real.log c ≠ 0 := Complex.ofReal_ne_zero.mp hcC
  have hb0 : Real.log b ≠ 0 := Complex.ofReal_ne_zero.mp hbC
  have hratio : ((Real.log b / Real.log c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast div_ne_zero hb0 hc0
  rw [denoteLog p c s hc hs, denoteLog q c b (hbase.symm.trans hc) hb,
    hs, hb, realUnaryValue_number, realUnaryValue_number,
    M.div_numbers _ _ hbC, M.div_numbers _ _ hratio,
    ← Complex.ofReal_div, ← Complex.ofReal_div]
  congr 1
  congr 1
  field_simp

/-- The supported power representation retains a natural or integer exponent. -/
theorem supportedPowerExponentInZ {M : Semantics.{u}} {α : Type v} {β : Type w}
    [Representation M α] [Representation M β]
    (p : Obj (M := M) (PowObj (M := M) α β)) : In p.val.exponent Z := by
  rcases p.wd with ⟨_, n, _, he⟩ | ⟨_, n, _, he⟩ | ⟨_, z, he, _, _⟩
  · change denote p.val.exponent = M.number (n : ℂ) at he
    exact (M.integer_members _).mpr ⟨(n : ℤ), by simpa only [Int.cast_natCast] using he⟩
  · change denote p.val.exponent = M.number (n : ℂ) at he
    exact (M.integer_members _).mpr ⟨(n : ℤ), by simpa only [Int.cast_natCast] using he⟩
  · exact he

theorem logarithmArgumentPowerValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (q : Obj (M := M) (LogObj (M := M) γ δ))
    (harg : Same p.val.base q.val.arg)
    (hguard : Lt (number 0) q.val.base ∧ ¬ Same q.val.base (number 1))
    (hx : Lt (number 0) q.val.arg) :
    M.divValue (realUnaryValue Real.log (denote p)) (realUnaryValue Real.log (denote q.val.base)) =
      M.mulValue (denote p.val.exponent) (denote q) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp q.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp q.wd.2.1
  obtain ⟨z, hz⟩ := (M.integer_members _).mp (supportedPowerExponentInZ p)
  have hs0 := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 s rfl hs).mp hx
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs0)
  have hn := logBaseNonzero q.val.base r hr hguard.1 hguard.2
  have hp : denote p = M.number ((s ^ z : ℝ) : ℂ) := by
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [harg.trans hs, hz, M.pow_numbers_int _ _ hsC, ← Complex.ofReal_zpow]
  rw [denoteLog q r s hr hs, hp, hr, hz, realUnaryValue_number, realUnaryValue_number,
    M.div_numbers _ _ hn, M.mul_numbers, Real.log_zpow,
    ← Complex.ofReal_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_div]
  congr 1
  congr 1
  exact mul_div_assoc (z : ℝ) (Real.log s) (Real.log r)

theorem logarithmBasePowerValue {M : Semantics.{u}}
    {α : Type v} {β : Type w} {γ : Type x} {δ : Type y}
    [Representation M α] [Representation M β] [Representation M γ] [Representation M δ]
    (p : Obj (M := M) (PowObj (M := M) α β))
    (q : Obj (M := M) (LogObj (M := M) γ δ))
    (hbase : Same p.val.base q.val.base)
    (hguard : Lt (number 0) q.val.base ∧ ¬ Same q.val.base (number 1))
    (_heR : In p.val.exponent R) (he0 : ¬ Same p.val.exponent (number 0))
    (_hx : Lt (number 0) q.val.arg) :
    M.divValue (realUnaryValue Real.log (denote q.val.arg)) (realUnaryValue Real.log (denote p)) =
      M.divValue (denote q) (denote p.val.exponent) := by
  obtain ⟨r, hr⟩ := (M.real_members _).mp q.wd.1
  obtain ⟨s, hs⟩ := (M.real_members _).mp q.wd.2.1
  obtain ⟨z, hz⟩ := (M.integer_members _).mp (supportedPowerExponentInZ p)
  have hr0 := (NativeBridge.lt_iff_ofDenoteReal _ _ 0 r rfl hr).mp hguard.1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr0)
  have hz0 : z ≠ 0 := by
    intro hzero
    apply he0
    change denote p.val.exponent = M.number 0
    simpa only [hzero, Int.cast_zero] using hz
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz0
  have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast hz0
  have hn := logBaseNonzero q.val.base r hr hguard.1 hguard.2
  have hnR : Real.log r ≠ 0 := Complex.ofReal_ne_zero.mp hn
  have hp : denote p = M.number ((r ^ z : ℝ) : ℂ) := by
    change M.powValue (denote p.val.base) (denote p.val.exponent) = _
    rw [hbase.trans hr, hz, M.pow_numbers_int _ _ hrC, ← Complex.ofReal_zpow]
  have hp0 : (Real.log (r ^ z) : ℂ) ≠ 0 := by
    rw [Real.log_zpow]
    exact_mod_cast mul_ne_zero hzR hnR
  rw [denoteLog q r s hr hs, hs, hp, hz, realUnaryValue_number, realUnaryValue_number,
    M.div_numbers _ _ hp0, M.div_numbers _ _ hzC, ← Complex.ofReal_intCast,
    ← Complex.ofReal_div, ← Complex.ofReal_div, Real.log_zpow]
  congr 1
  congr 1
  field_simp

end Litex
